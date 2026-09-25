#include "corpus.h"

int point_distance2(const struct point *first, const struct point *second)
{
  int horizontal = first->x - second->x;
  int vertical = first->y - second->y;
  return horizontal * horizontal + vertical * vertical;
}

struct point make_point(int horizontal, int vertical)
{
  struct point result;
  result.x = horizontal;
  result.y = vertical;
  return result;
}

int rect_area(struct rect box)
{
  return box.width * box.height;
}

int rect_contains(const struct rect *box, struct point probe)
{
  return probe.x >= box->origin.x && probe.y >= box->origin.y &&
         probe.x < box->origin.x + box->width && probe.y < box->origin.y + box->height;
}

int list_length(const struct node *head)
{
  int length = 0;
  while (head != NULL) {
    length++;
    head = head->next;
  }
  return length;
}

int list_sum(const struct node *head)
{
  int total = 0;
  for (const struct node *cursor = head; cursor != NULL; cursor = cursor->next)
    total += cursor->value;
  return total;
}

struct node *list_reverse(struct node *head)
{
  struct node *previous = NULL;
  while (head != NULL) {
    struct node *following = head->next;
    head->next = previous;
    previous = head;
    head = following;
  }
  return previous;
}
