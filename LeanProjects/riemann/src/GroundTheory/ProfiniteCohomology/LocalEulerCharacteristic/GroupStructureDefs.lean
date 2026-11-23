import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

def coprimePart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | (orderOf x).Coprime p}

def primaryPart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | ∃ n : ℕ, orderOf x = p ^ n}

variable {G : Type*} [Group G]

def coprimeQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (coprimePart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def primaryQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (primaryPart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def coprimeRelPreimage (N₀ N₁ : Subgroup G) [N₁.Normal] (p : ℕ) : Subgroup G :=
  (coprimeQuotientPreimage (N₁.subgroupOf N₀) p).map N₀.subtype

end GroundTheory.ProfCoh
