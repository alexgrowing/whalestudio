import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HInt {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (M : Submodule (𝓞 E) (Fin m → E)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, hform (starRingEnd E) J x y ∈ (algebraMap (𝓞 E) E).range

def HDual {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (M : Submodule (𝓞 E) (Fin m → E)) (d : ℕ) : Prop :=
  ∀ w : Fin m → E, (∀ x ∈ M, hform (starRingEnd E) J x w ∈ (algebraMap (𝓞 E) E).range) → (d : E) • w ∈ M

variable (E) in

def Lat (m d : ℕ) : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
  {p | IsHerm (starRingEnd E) p.1 ∧ p.1.det ≠ 0 ∧ p.2.FG ∧ Submodule.span E (p.2 : Set (Fin m → E)) = ⊤ ∧
    HInt p.1 p.2 ∧ HDual p.1 p.2 d}

def Iso {m : ℕ} (p q : Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) : Prop :=
  ∃ A : GL (Fin m) E, cT (starRingEnd E) (A : Matrix (Fin m) (Fin m) E) * p.1 * (A : Matrix (Fin m) (Fin m) E) = q.1 ∧
    IsImg A q.2 p.2

def FinCl {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))) : Prop :=
  ∃ T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)), T.Finite ∧ ∀ p ∈ S, ∃ q ∈ T, Iso p q

variable (E) in

def HL (m : ℕ) : Prop := ∀ d : ℕ, 1 ≤ d → FinCl (Lat E m d)

def gram {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin k → Fin m → E) : Matrix (Fin k) (Fin k) E :=
  Matrix.of fun i j => hform (starRingEnd E) J (v i) (v j)

variable (E) in

def SplitSet (m k d : ℕ) (G : Set (Matrix (Fin k) (Fin k) E)) :
    Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
  {p | p ∈ Lat E m d ∧ ∃ v : Fin k → Fin m → E, (∀ i, v i ∈ p.2) ∧ gram p.1 v ∈ G}

end Defs

def PartShort : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m d : ℕ, 1 ≤ m → 1 ≤ d → ∃ C : ℚ, ∀ p ∈ Lat E m d, ∃ x ∈ p.2, x ≠ 0 ∧
      |Algebra.norm ℚ (hform (starRingEnd E) p.1 x x)| ≤ C

def PartUnits : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ C : ℚ, ∃ R : Set E, R.Finite ∧ (0 : E) ∉ R ∧
      ∀ a ∈ (algebraMap (𝓞 E) E).range, star a = a → a ≠ 0 → |Algebra.norm ℚ a| ≤ C →
        ∃ u : (𝓞 E)ˣ, ∃ r ∈ R, a = star (algebraMap (𝓞 E) E (u : 𝓞 E)) * algebraMap (𝓞 E) E (u : 𝓞 E) * r

def PartIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m d : ℕ, 1 ≤ d → ∃ G : Set (Matrix (Fin 2) (Fin 2) E), G.Finite ∧ (∀ Γ ∈ G, Γ.det ≠ 0) ∧
      ∀ p ∈ Lat E m d, ∀ x ∈ p.2, x ≠ 0 → hform (starRingEnd E) p.1 x x = 0 →
        ∃ v : Fin 2 → Fin m → E, (∀ i, v i ∈ p.2) ∧ gram p.1 v ∈ G

def PartSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m k : ℕ, 1 ≤ k → (∀ j < m, HL E j) → ∀ d : ℕ, 1 ≤ d → ∀ G : Set (Matrix (Fin k) (Fin k) E), G.Finite →
      (∀ Γ ∈ G, Γ.det ≠ 0) → FinCl (SplitSet E m k d G)

def PartBetween : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (N : Submodule (𝓞 E) (Fin m → E)), N.FG → ∀ δ : 𝓞 E, δ ≠ 0 →
    {M : Submodule (𝓞 E) (Fin m → E) | N ≤ M ∧ ∀ x ∈ M, δ • x ∈ N}.Finite

def PartMink : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ G : Matrix (Fin N) (Fin N) ℝ, G.PosDef →
    ∃ c : Fin N → ℤ, c ≠ 0 ∧ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ K * G.det ^ ((1 : ℝ) / N)

section Lemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem FinCl.mono {m : ℕ} {S S' : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))}
    (h : FinCl S') (hs : S ⊆ S') : FinCl S := by
  obtain ⟨T, hT, hp⟩ := h
  exact ⟨T, hT, fun p hp' => hp p (hs hp')⟩

theorem FinCl.union {m : ℕ} {S S' : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))}
    (h : FinCl S) (h' : FinCl S') : FinCl (S ∪ S') := by
  obtain ⟨T, hT, hp⟩ := h
  obtain ⟨T', hT', hp'⟩ := h'
  refine ⟨T ∪ T', hT.union hT', fun p hp0 => ?_⟩
  rcases hp0 with h1 | h1
  · obtain ⟨q, hq, hi⟩ := hp p h1
    exact ⟨q, Or.inl hq, hi⟩
  · obtain ⟨q, hq, hi⟩ := hp' p h1
    exact ⟨q, Or.inr hq, hi⟩

theorem hform_smul {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c c' : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) (c' • y) = star c * c' * hform (starRingEnd E) J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_self_star {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : IsHerm (starRingEnd E) J)
    (x : Fin m → E) : star (hform (starRingEnd E) J x x) = hform (starRingEnd E) J x x := by
  have hij : ∀ i j, star (J j i) = J i j := fun i j => by
    have h1 := congrFun (congrFun hJ i) j
    simpa [cT, starRingEnd_apply] using h1
  simp only [hform, starRingEnd_apply, star_sum, star_mul', star_star, hij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hl_zero : HL E 0 := by
  intro d _
  refine ⟨{((0 : Matrix (Fin 0) (Fin 0) E), (⊥ : Submodule (𝓞 E) (Fin 0 → E)))},
    Set.finite_singleton _, fun p _ => ⟨_, rfl, 1, Matrix.ext fun i _ => Fin.elim0 i, fun v => ?_⟩⟩
  have hv : v = 0 := funext fun i => Fin.elim0 i
  subst hv
  constructor
  · intro _
    exact ⟨0, Submodule.zero_mem _, funext fun i => Fin.elim0 i⟩
  · intro _
    exact Submodule.zero_mem _

end Lemmas

theorem hl_step (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (m : ℕ) (hm : 1 ≤ m) (ih : ∀ k < m, HL E k) : HL E m := by
  intro d hd
  obtain ⟨C, hC⟩ := hS F E hc m d hm hd
  obtain ⟨R, hR, hR0, hRu⟩ := hU F E hc C
  obtain ⟨G2, hG2, hG2det, hiso⟩ := hI F E hc m d hd
  have hG1 : ((fun r : E => Matrix.of fun (_ _ : Fin 1) => r) '' R).Finite := hR.image _
  have hG1det : ∀ Γ ∈ (fun r : E => Matrix.of fun (_ _ : Fin 1) => r) '' R, Γ.det ≠ 0 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Matrix.det_unique]
    show r ≠ 0
    rintro rfl
    exact hR0 hr
  refine FinCl.mono (FinCl.union (hP F E hc m 1 le_rfl ih d hd _ hG1 hG1det)
    (hP F E hc m 2 (by norm_num) ih d hd G2 hG2 hG2det)) ?_
  intro p hp
  obtain ⟨x, hx, hx0, hxC⟩ := hC p hp
  by_cases hiso0 : hform (starRingEnd E) p.1 x x = 0
  · refine Or.inr ?_
    simp only [SplitSet, Set.mem_setOf_eq]
    exact ⟨hp, hiso p hp x hx hx0 hiso0⟩
  · refine Or.inl ?_
    have hint : hform (starRingEnd E) p.1 x x ∈ (algebraMap (𝓞 E) E).range := hp.2.2.2.2.1 x hx x hx
    obtain ⟨u, r, hr, hur⟩ := hRu _ hint (hform_self_star p.1 hp.1 x) hiso0 hxC
    set c : E := algebraMap (𝓞 E) E ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) with hcdef
    have hca : c * algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
      rw [hcdef, ← map_mul, Units.inv_mul, map_one]
    have hsca : star c * star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) = 1 := by
      rw [← star_mul', hca, star_one]
    simp only [SplitSet, Set.mem_setOf_eq]
    refine ⟨hp, fun _ => c • x, fun _ => ?_, ⟨r, hr, ?_⟩⟩
    · show c • x ∈ p.2
      rw [hcdef, algebraMap_smul]
      exact p.2.smul_mem _ hx
    · ext i j
      simp only [gram, Matrix.of_apply]
      rw [hform_smul, hur]
      rw [show star c * c * (star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) *
          algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E) * r) =
          (star c * star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E))) *
          (c * algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) * r by ring, hsca, hca, one_mul, one_mul]

theorem hl_all (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (m : ℕ) : HL E m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0
      exact hl_zero
    · exact hl_step hS hU hI hP F E hc m hm ih

theorem stH_of_hl (hHL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ m, HL E m) : StH := by
  intro F E _ _ _ _ _ _ hc n J hJ hdet
  classical
  obtain ⟨T0, hT0, hcl⟩ := hHL F E hc n 1 le_rfl
  let pick : Matrix (Fin n) (Fin n) E × Submodule (𝓞 E) (Fin n → E) → Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E := fun q =>
    if h : ∃ M : Submodule (𝓞 E) (Fin n → E), ∃ A : GL (Fin n) E,
        cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) = q.1 ∧ IsImg A q.2 M then
      (Classical.choose h, Classical.choose (Classical.choose_spec h)) else (⊥, 1)
  have hpick : ∀ q : Matrix (Fin n) (Fin n) E × Submodule (𝓞 E) (Fin n → E), (∃ M : Submodule (𝓞 E) (Fin n → E), ∃ A : GL (Fin n) E,
      cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) = q.1 ∧ IsImg A q.2 M) →
      cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E) = q.1 ∧
        IsImg (pick q).2 q.2 (pick q).1 := by
    intro q h
    show cT (starRingEnd E) ((dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 : Matrix (Fin n) (Fin n) E) * J *
        ((dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 : Matrix (Fin n) (Fin n) E) = q.1 ∧
      IsImg (dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 q.2 (dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).1
    rw [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec h)
  refine ⟨(hT0.image (fun q => (pick q).1)).toFinset, fun M hfg hspan hsd => ?_⟩
  have hLat : (J, M) ∈ Lat E n 1 := by
    simp only [Lat, Set.mem_setOf_eq]
    refine ⟨hJ, hdet, hfg, hspan, fun x hx y hy => (hsd y).1 hy x hx, fun w hw => ?_⟩
    rw [Nat.cast_one, one_smul]
    exact (hsd w).2 hw
  obtain ⟨q, hq, A, hA1, hA2⟩ := hcl (J, M) hLat
  dsimp only at hA1 hA2
  obtain ⟨hq1, hq2⟩ := hpick q ⟨M, A, hA1, hA2⟩
  have key : cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) =
      cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E) := hA1.trans hq1.symm
  refine ⟨A * (pick q).2⁻¹, ?_, (pick q).1, ?_, ?_⟩
  · show cT (starRingEnd E) ((A * (pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * J *
      ((A * (pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = J
    rw [Units.val_mul, cT_mul]
    calc cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J *
          ((A : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
        = cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E)) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
          simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E)) *
            (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by rw [key]
      _ = cT (starRingEnd E) (((pick q).2 : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) * J *
            (((pick q).2 : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
          rw [cT_mul]
          simp only [Matrix.mul_assoc]
      _ = J := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]
  · exact (Set.Finite.mem_toFinset _).mpr ⟨q, hq, rfl⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨w0, hw0, rfl⟩ := (hA2 v).1 hv
      refine ⟨((pick q).2 : Matrix (Fin n) (Fin n) E) *ᵥ w0, (hq2 _).2 ⟨w0, hw0, rfl⟩, ?_⟩
      rw [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul (pick q).2⁻¹,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w0, hw0, rfl⟩ := (hq2 w).1 hw
      refine (hA2 _).2 ⟨w0, hw0, ?_⟩
      rw [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul (pick q).2⁻¹,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem stH_of_parts (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit) : StH :=
  stH_of_hl fun F E _ _ _ _ _ _ hc m => hl_all hS hU hI hP F E hc m

end PIW.AdelClassFin
