import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa

section Bare

variable {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)

def Bl : Submodule R (Γ → M) := LinearMap.range (LinearMap.pi fun g => ρ g - LinearMap.id)

theorem mem_Bl {z : Γ → M} : z ∈ Bl ρ ↔ ∃ m, ∀ g, z g = ρ g m - m := by
  rw [Bl, LinearMap.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, funext fun g => (hm g).symm⟩

variable [TopologicalSpace Γ]

def LC : Prop := ∀ m, IsLocallyConstant fun g => ρ g m

def Zl : Submodule R (Γ → M) where
  carrier := {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}
  add_mem' := by
    rintro x y ⟨a1, a2⟩ ⟨b1, b2⟩
    refine ⟨a1.add b1, fun g h => ?_⟩
    simp only [Pi.add_apply, a2, b2, map_add]; abel
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp⟩
  smul_mem' := by
    rintro c x ⟨a1, a2⟩
    exact ⟨a1.comp (c • ·), fun g h => by simp [a2]⟩

theorem mem_Zl {z : Γ → M} : z ∈ Zl ρ ↔ IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h) := Iff.rfl

end Bare

variable {l : ℕ} [Fact l.Prime]

def epsBar {Γ : Type} [Group Γ] (ε : Γ →* ℤ_[l]ˣ) (g : Γ) : ZMod l := PadicInt.toZMod ((ε g : ℤ_[l]ˣ) : ℤ_[l])

structure IsDualPair {R Γ M M' : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (ε : Γ →* ℤ_[l]ˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ M') (b : M →+ M' →+ ZMod l) : Prop where
  left : ∀ x, (∀ y, b x y = 0) → x = 0
  right : ∀ y, (∀ x, b x y = 0) → y = 0
  equiv : ∀ g x y, b (ρ g x) (ρ' g y) = epsBar ε g * b x y

def LocCount (D : Type) [Group D] [TopologicalSpace D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (R M M' : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Finite M] [Finite M']
    (ρ : Representation R D M) (ρ' : Representation R D M') (b : M →+ M' →+ ZMod l), LC ρ → IsDualPair ε ρ ρ' b →
    Finite (Zl ρ) ∧ Nat.card (Zl ρ) = Nat.card M ^ (1 + d) * Nat.card ρ'.invariants

variable (l) in

def UnrCount (D : Type) [Group D] [TopologicalSpace D] (J : Subgroup D) : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M), LC ρ →
    (∀ m : M, l • m = 0) → (∀ g ∈ J, ρ g = 1) →
    {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}.Finite ∧ {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}.ncard = Nat.card M

def GWBare {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ε : Γ →* ℤ_[l]ˣ) {W : Type} [Fintype W] (D : W → Type)
    [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)] (ι : ∀ w, D w →* Γ) {d : ℕ} (cw : Fin d → Γ) : Prop :=
  ∀ (R M M' : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Finite M] [Finite M']
    (ρ : Representation R Γ M) (ρ' : Representation R Γ M') (b : M →+ M' →+ ZMod l), LC ρ → IsDualPair ε ρ ρ' b →
    ∀ 𝓛 : ∀ w, AddSubgroup (D w → M),
      (∀ w, (Bl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup ≤ 𝓛 w ∧
        𝓛 w ≤ (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup) →
      Finite (Zl ρ) ∧ Finite (Zl ρ') ∧
      {z | z ∈ Zl ρ ∧ ∀ w, z ∘ ι w ∈ 𝓛 w}.ncard * Nat.card (Bl ρ') * Nat.card M ^ Fintype.card W *
          ∏ i, Nat.card {m : M // ρ (cw i) m = m} ≤
        Nat.card M * {y | y ∈ Zl ρ' ∧ ∀ w, 𝓛 w = (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup →
          y ∘ ι w ∈ Bl (ρ'.comp (ι w) : Representation R (D w) M')}.ncard * ∏ w, Nat.card (𝓛 w)

variable {L : Loc}

structure ArData (G : Glob l L) (q d : ℕ) : Type 1 where
  Dq : Option (Fin q) → Type
  [grp : ∀ j, Group (Dq j)]
  [top : ∀ j, TopologicalSpace (Dq j)]
  [tgrp : ∀ j, IsTopologicalGroup (Dq j)]
  [cpt : ∀ j, CompactSpace (Dq j)]
  [tdisc : ∀ j, TotallyDisconnectedSpace (Dq j)]
  φq : ∀ j, Dq j →* G.G₀
  φq_cont : ∀ j, Continuous (φq j)
  cw : Fin d → G.Γ
  cw_sq : ∀ i, cw i * cw i = 1
  cw_η : ∀ i, G.η (cw i) = -1
  cw_ε : ∀ i, G.ε (cw i) = -1
  c_ε : G.ε G.c = -1
  dv : L.Vl → ℕ
  sum_dv : ∑ v, dv v = d

attribute [instance] ArData.grp ArData.top ArData.tgrp ArData.cpt ArData.tdisc

namespace ArData

variable {G : Glob l L} {q d : ℕ} (a : ArData G q d)

abbrev W (L : Loc) (q : ℕ) : Type := L.Vl ⊕ L.St ⊕ Option (Fin q)

def D : W L q → Type
  | .inl v => L.Gv v
  | .inr (.inl u) => L.Gu u
  | .inr (.inr j) => a.Dq j

instance : ∀ w, Group (a.D w)
  | .inl v => L.gv v
  | .inr (.inl u) => L.gu u
  | .inr (.inr j) => a.grp j

instance : ∀ w, TopologicalSpace (a.D w)
  | .inl v => L.tv v
  | .inr (.inl u) => L.tu u
  | .inr (.inr j) => a.top j

def ι : ∀ w, a.D w →* G.Γ
  | .inl v => G.η.ker.subtype.comp (G.φ v)
  | .inr (.inl u) => G.η.ker.subtype.comp (G.φu u)
  | .inr (.inr j) => G.η.ker.subtype.comp (a.φq j)

structure Counts : Prop where
  gw : GWBare G.ε a.D a.ι a.cw
  locV : ∀ v, LocCount (L.Gv v) (G.ε.comp (a.ι (.inl v))) (a.dv v)
  locU : ∀ u, LocCount (L.Gu u) (G.ε.comp (a.ι (.inr (.inl u)))) 0
  locQ : ∀ j, LocCount (a.Dq j) (G.ε.comp (a.ι (.inr (.inr j)))) 0
  unr : ∀ u, UnrCount l (L.Gu u) (L.Ju u)

end ArData

structure ArSys {G0 : Glob l L} (T : TWGrp G0) (d : ℕ) (D0 : Subgroup G0.G₀) : Type 1 where
  a : ∀ N, ArData (T.GN N) T.q d
  counts : ∀ N, (a N).Counts
  dv : L.Vl → ℕ
  dv_eq : ∀ N, (a N).dv = dv
  d0 : ∀ N, (((T.h N).p₀).comp ((a N).φq none)).range = D0
  ph : ∀ N j, T.ph N j ∈ ((a N).φq (some j)).range
  ta : ∀ N j, T.ta N j ∈ ((a N).φq (some j)).range

def IsAd (F : GFrame l) {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n : ℕ}
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (rep : Representation A F.Γ V) : Prop :=
  (∀ (g : F.G₀) (Z : V), (rep g Z : Matrix (Fin n) (Fin n) R) = χ g • (ρ g * Z * ρ g⁻¹)) ∧
    ∀ Z : V, (rep F.c Z : Matrix (Fin n) (Fin n) R) = -(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ)

structure AdOk (F : GFrame l) {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n : ℕ}
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) : Prop where
  one : ρ 1 = 1
  mul : ∀ g h, ρ (g * h) = ρ g * ρ h
  form : ∀ g, ∃ u : Rˣ, (ρ g)ᵀ * ρ (F.conj g) = (u : R) • (1 : Matrix (Fin n) (Fin n) R)
  χ_one : χ 1 = 1
  χ_mul : ∀ g h, χ (g * h) = χ g * χ h
  ad : ∀ g, ∀ Z ∈ V, χ (g : F.G₀) • (ρ g * Z * ρ g⁻¹) ∈ V
  tr : ∀ Z ∈ V, χ F.c • Zᵀ ∈ V

def nu (n a g : ℕ) : ℕ := a.choose 2 + (n - a).choose 2 + g * (a * (n - a))

end UpperTheory.V.Pa
