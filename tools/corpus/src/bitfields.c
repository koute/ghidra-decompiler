#include "corpus.h"

void set_flags(struct device_flags *flags, int mode, int priority)
{
  flags->enabled = 1;
  flags->mode = mode;
  flags->priority = priority;
  flags->channel = mode + priority;
}

int get_mode(const struct device_flags *flags)
{
  if (!flags->enabled)
    return -1;
  return flags->mode * 16 + flags->priority;
}

u32 pack_flags(struct device_flags flags)
{
  return (u32)flags.enabled | ((u32)flags.mode << 1) | ((u32)flags.channel << 8);
}
