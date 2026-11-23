import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Th

variable {l : ℕ} [Fact l.Prime]

structure DualPair (k : ℕ) {R Γ M M' : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (ε : Γ →* ℤ_[l]ˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ M') (b : M →+ M' →+ ZMod (l ^ k)) : Prop where
  left : ∀ x, (∀ y, b x y = 0) → x = 0
  right : ∀ y, (∀ x, b x y = 0) → y = 0
  equiv : ∀ g x y, b (ρ g x) (ρ' g y) = PadicInt.toZModPow k ((ε g : ℤ_[l]ˣ) : ℤ_[l]) * b x y

def LocCnt (D : Type) [Group D] [TopologicalSpace D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (R M M' : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Finite M] [Finite M']
    (ρ : Representation R D M) (ρ' : Representation R D M') (b : M →+ M' →+ ZMod (l ^ k)), LC ρ → DualPair k ε ρ ρ' b →
    Finite (Zl ρ) ∧ Nat.card (Zl ρ) = Nat.card M ^ (1 + d) * Nat.card ρ'.invariants

variable (l) in

def UnrCnt (D : Type) [Group D] [TopologicalSpace D] (J : Subgroup D) : Prop :=
  ∀ (k : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M), LC ρ →
    (∀ m : M, l ^ k • m = 0) → (∀ g ∈ J, ρ g = 1) →
    {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}.Finite ∧ {z | z ∈ Zl ρ ∧ ∀ g ∈ J, z g = 0}.ncard ≤ Nat.card M

def GWCnt {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ε : Γ →* ℤ_[l]ˣ) {W : Type} [Fintype W] (D : W → Type)
    [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)] (ι : ∀ w, D w →* Γ) {d : ℕ} (cw : Fin d → Γ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (R M M' : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Finite M] [Finite M']
    (ρ : Representation R Γ M) (ρ' : Representation R Γ M') (b : M →+ M' →+ ZMod (l ^ k)), LC ρ → DualPair k ε ρ ρ' b →
    ∀ 𝓛 : ∀ w, AddSubgroup (D w → M),
      (∀ w, (Bl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup ≤ 𝓛 w ∧
        𝓛 w ≤ (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup) →
      Finite (Zl ρ) ∧ Finite (Zl ρ') ∧
      {z | z ∈ Zl ρ ∧ ∀ w, z ∘ ι w ∈ 𝓛 w}.ncard * Nat.card (Bl ρ') * Nat.card M ^ Fintype.card W *
          ∏ i, Nat.card {m : M // ρ (cw i) m = m} ≤
        Nat.card M * {y | y ∈ Zl ρ' ∧ ∀ w, 𝓛 w = (Zl (ρ.comp (ι w) : Representation R (D w) M)).toAddSubgroup →
          y ∘ ι w ∈ Bl (ρ'.comp (ι w) : Representation R (D w) M')}.ncard * ∏ w, Nat.card (𝓛 w)

variable {L : Loc}

structure Cnts {G : Glob l L} {q d : ℕ} (a : ArData G q d) : Prop where
  gw : GWCnt G.ε a.D a.ι a.cw
  locV : ∀ v, LocCnt (L.Gv v) (G.ε.comp (a.ι (.inl v))) (a.dv v)
  locQ : ∀ j, LocCnt (a.Dq j) (G.ε.comp (a.ι (.inr (.inr j)))) 0
  unr : ∀ u, UnrCnt l (L.Gu u) (L.Ju u)

structure Sys {G0 : Glob l L} (T : TWGrp G0) (d : ℕ) (D0 : Subgroup G0.G₀) : Type 1 where
  a : ∀ N, ArData (T.GN N) T.q d
  counts : ∀ N, Cnts (a N)
  dv : L.Vl → ℕ
  dv_eq : ∀ N, (a N).dv = dv
  d0 : ∀ N, (((T.h N).p₀).comp ((a N).φq none)).range = D0
  ph : ∀ N j, T.ph N j ∈ ((a N).φq (some j)).range
  ta : ∀ N j, T.ta N j ∈ ((a N).φq (some j)).range

def IsAdP (F : GFrame l) {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n : ℕ}
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin n) R) (χ : F.Γ → R)
    (rep : Representation A F.Γ (Matrix (Fin n) (Fin n) R)) : Prop :=
  (∀ (g : F.G₀) Z, rep g Z = χ g • (ρ g * Z * ρ g⁻¹)) ∧ ∀ Z, P * rep F.c Z = -(χ F.c • (Zᵀ * P))

section Pt

variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}

abbrev Mm (O : Type) [CommRing O] [IsLocalRing O] (n m : ℕ) : Type := Matrix (Fin n) (Fin n) (Om O m)

variable (O) in

def epsm (G : Glob l L) (m : ℕ) (g : G.Γ) : Om O m := algebraMap O (Om O m) (algebraMap ℤ_[l] O (G.ε g : ℤ_[l]))

variable {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)

abbrev IsAd0 (rep : Representation O G.Γ (Mm O n m)) : Prop := IsAdP G.frame (y.ρm h m) (red m y.P) (fun _ => 1) rep

abbrev IsAd1 (rep : Representation O G.Γ (Mm O n m)) : Prop := IsAdP G.frame (y.ρm h m) (red m y.P) (epsm O G m) rep

def Pt.ρ0 (g : G0.G₀) : Mm O n m := red m (mat y.ρ g)

def bor (v : L.Vl) : AddSubgroup (Mm O n m) where
  carrier := {Z | ∀ i j : Fin n, j < i → (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z *
    red m (y.w v : Matrix (Fin n) (Fin n) O) : Mm O n m) i j = 0}
  add_mem' h h' i j e := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, h i j e, h' i j e, add_zero]
  zero_mem' i j _ := by simp
  neg_mem' h i j e := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, h i j e, neg_zero]

def Zbor (v : L.Vl) : AddSubgroup (L.Gv v → Mm O n m) where
  carrier := {β | IsLocallyConstant β ∧
    (∀ g g', β (g * g') = β g + y.ρ0 m (G0.φ v g) * β g' * y.ρ0 m (G0.φ v g)⁻¹) ∧ ∀ g, β g ∈ bor y m v}
  add_mem' := by
    rintro β β' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨a1.add b1, fun g g' => ?_, fun g => add_mem (a3 g) (b3 g)⟩
    simp only [Pi.add_apply, a2, b2, Matrix.mul_add, Matrix.add_mul]; abel
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g g' => by simp, fun g => zero_mem _⟩
  neg_mem' := by
    rintro β ⟨a1, a2, a3⟩
    refine ⟨a1.comp Neg.neg, fun g g' => ?_, fun g => neg_mem (a3 g)⟩
    simp only [Pi.neg_apply, a2, Matrix.mul_neg, Matrix.neg_mul]; abel

def Tw : Set (G0.G₀ → Mm O n m) :=
  {z | IsLocallyConstant z ∧ (∀ g g', z (g * g') = z g + epsm O G0 m g • (y.ρ0 m g * z g' * y.ρ0 m g⁻¹)) ∧
    ∀ g, red m y.P * z (G0.frame.conj g) = (z g)ᵀ * red m y.P}

def TwB : Set (G0.G₀ → Mm O n m) :=
  {z | ∃ Y : Mm O n m, red m y.P * Y = Yᵀ * red m y.P ∧
    z = fun g : G0.G₀ => epsm O G0 m g • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) - Y}

def DetO (S : Set G0.G₀) : Prop :=
  ∀ z : G0.G₀ → Matrix (Fin n) (Fin n) O, (∀ i j, AdicCont (maximalIdeal O) fun g => z g i j) →
    (∀ g g', z (g * g') = z g + algebraMap ℤ_[l] O (G0.ε g : ℤ_[l]) • (mat y.ρ g * z g' * mat y.ρ g⁻¹)) →
    (∀ g, (y.P : Matrix (Fin n) (Fin n) O) * z (G0.frame.conj g) = (z g)ᵀ * y.P) →
    (∀ σ ∈ S, ∀ k : ℕ, (z σ * mat y.ρ σ ^ k).trace = 0) →
    ∃ (a : O) (Y : Matrix (Fin n) (Fin n) O), a ≠ 0 ∧ (y.P : Matrix (Fin n) (Fin n) O) * Y = Yᵀ * y.P ∧
      ∀ g : G0.G₀, a • z g = algebraMap ℤ_[l] O (G0.ε g : ℤ_[l]) • (mat y.ρ g * Y * mat y.ρ g⁻¹) - Y

end Pt

end UpperTheory.V.Th

end
