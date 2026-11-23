import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem val_lt_iff_of_dec {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {a b : Ω} (hb : b ≠ 0) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  have hb' : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have h1 : 0 < A.valuation b := (Valuation.pos_iff _).mpr hb
  have h2 : 0 < A.valuation (σ b) := (Valuation.pos_iff _).mpr hb'
  rw [← div_lt_one₀ h1, ← div_lt_one₀ h2, ← map_div₀ A.valuation (σ a), ← map_div₀ A.valuation a, ← map_div₀ σ]
  exact valuation_apply_lt_one_iff hσ (a / b)

theorem val_apply_eq {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (x : Ω) : A.valuation (σ x) = A.valuation x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have key : ∀ τ ∈ Dec (F := E) A, ∀ y : Ω, y ≠ 0 → A.valuation (τ y) < A.valuation y → False := by
    intro τ hτ y hy hlt
    have hne : ∀ k : ℕ, (τ ^ k) y ≠ 0 := fun k => (map_ne_zero _).mpr hy
    have hdec : ∀ k : ℕ, A.valuation ((τ ^ (k + 1)) y) < A.valuation ((τ ^ k) y) := by
      intro k
      induction k with
      | zero => simpa using hlt
      | succ k ih =>
        have := (val_lt_iff_of_dec hτ (hne k)).mpr ih
        simpa only [← AlgEquiv.mul_apply, ← pow_succ'] using this
    have hanti : StrictAnti fun k : ℕ => A.valuation ((τ ^ k) y) := strictAnti_nat_of_succ_lt hdec
    have hinj : Function.Injective fun k : ℕ => (τ ^ k) y := fun i j hij =>
      hanti.injective (by simp only at hij ⊢; rw [hij])
    have hint : IsIntegral E y := (Algebra.IsAlgebraic.isAlgebraic (R := E) y).isIntegral
    have hfin := (minpoly E y).rootSet_finite Ω
    apply Set.infinite_of_injective_forall_mem hinj (s := (minpoly E y).rootSet Ω) ?_ hfin
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show (τ ^ k) y = ((τ ^ k : G E Ω) : Ω →ₐ[E] Ω) y from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero]
  rcases lt_trichotomy (A.valuation (σ x)) (A.valuation x) with h | h | h
  · exact (key σ hσ x hx h).elim
  · exact h
  · refine (key σ⁻¹ ((Dec (F := E) A).inv_mem hσ) (σ x) ((map_ne_zero σ).mpr hx) ?_).elim
    rwa [show (σ⁻¹ : G E Ω) (σ x) = x by simp]

theorem val_ratio {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : A.valuation (σ x / x) = 1 := by
  rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)]

theorem ratio_cong {σ ψ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (hψ : ψ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) :
    A.valuation (σ (ψ x) / ψ x - σ x / x) < 1 := by
  set y := ψ x / x with hy
  have hy1 : A.valuation y = 1 := val_ratio hψ hx
  have hy0 : y ≠ 0 := by intro h; rw [h, map_zero] at hy1; exact zero_ne_one hy1
  have hψx : ψ x = x * y := by rw [hy]; field_simp
  have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  have hσy0 : σ y ≠ 0 := (map_ne_zero σ).mpr hy0
  have e : σ (ψ x) / ψ x - σ x / x = (σ x / x) * ((σ y - y) / y) := by
    rw [hψx, map_mul]; field_simp
  rw [e, map_mul, val_ratio (Ine_le_Dec A hσ) hx, one_mul, map_div₀, hy1, div_one]
  exact hσ.2 y hy1.le

def ratioUnit {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : Aˣ where
  val := ⟨σ x / x, (A.valuation_le_one_iff _).mp (val_ratio hσ hx).le⟩
  inv := ⟨x / σ x, (A.valuation_le_one_iff _).mp (by
    rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)])⟩
  val_inv := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show σ x / x * (x / σ x) = 1; field_simp
  inv_val := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show x / σ x * (σ x / x) = 1; field_simp

theorem res_eq_of_cong {a b : A} (h : A.valuation ((a : Ω) - b) < 1) :
    IsLocalRing.residue A a = IsLocalRing.residue A b := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  simpa using h

def tameSym {x : Ω} (hx : x ≠ 0) : Ine (F := E) A →* (IsLocalRing.ResidueField A)ˣ where
  toFun σ := Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (ratioUnit (Ine_le_Dec A σ.2) hx)
  map_one' := by
    ext
    show IsLocalRing.residue A ⟨(1 : G E Ω) x / x, _⟩ = 1
    rw [← map_one (IsLocalRing.residue A)]
    congr 1
    apply Subtype.ext
    show (1 : G E Ω) x / x = 1
    simp [hx]
  map_mul' σ τ := by
    ext
    show IsLocalRing.residue A ⟨(σ * τ : G E Ω) x / x, _⟩ =
      IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ * IsLocalRing.residue A ⟨(τ : G E Ω) x / x, _⟩
    rw [← map_mul]
    apply res_eq_of_cong
    show A.valuation ((σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x)) < 1
    have hτx : (τ : G E Ω) x ≠ 0 := (map_ne_zero _).mpr hx
    have e : (σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x) =
        ((σ : G E Ω) ((τ : G E Ω) x) / (τ : G E Ω) x - (σ : G E Ω) x / x) * ((τ : G E Ω) x / x) := by
      rw [AlgEquiv.mul_apply]; field_simp
    rw [e, map_mul, val_ratio (Ine_le_Dec A τ.2) hx, mul_one]
    exact ratio_cong σ.2 (Ine_le_Dec A τ.2) hx

theorem isWild_of_tameSym {σ : Ine (F := E) A} (h : ∀ (x : Ω) (hx : x ≠ 0), tameSym hx σ = 1) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) := by
  refine ⟨σ.2, fun x hx => ?_⟩
  have h1 := congrArg Units.val (h x hx)
  change IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ = IsLocalRing.residue A 1 at h1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h1
  have h2 : A.valuation ((σ : G E Ω) x / x - 1) < 1 := by simpa using h1
  have hv : 0 < A.valuation x := (Valuation.pos_iff _).mpr hx
  have e : (σ : G E Ω) x - x = ((σ : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  calc A.valuation ((σ : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x :=
        mul_lt_mul_of_pos_right h2 hv
    _ = A.valuation x := one_mul _

theorem isWild_commutator (s t : Ine (F := E) A) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A ((s * t * s⁻¹ * t⁻¹ : Ine (F := E) A) : G E Ω) := by
  refine isWild_of_tameSym fun x hx => ?_
  simp only [map_mul, map_inv]
  rw [mul_comm (tameSym hx s) (tameSym hx t)]
  group

theorem isWild_frob {q : ℕ} {φ : G E Ω} (hφ : IsFrob A q φ) (s : Ine (F := E) A) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (((⟨φ * s * φ⁻¹, conj_mem_Ine hφ.1 s.2⟩ : Ine (F := E) A) * (s ^ q)⁻¹ :
      Ine (F := E) A) : G E Ω) := by
  refine isWild_of_tameSym fun x hx => ?_
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
  ext
  show IsLocalRing.residue A ⟨(φ * (s : G E Ω) * φ⁻¹) x / x, _⟩ = (IsLocalRing.residue A ⟨(s : G E Ω) x / x, _⟩) ^ q
  rw [← map_pow]
  apply res_eq_of_cong
  show A.valuation ((φ * (s : G E Ω) * φ⁻¹) x / x - ((s : G E Ω) x / x) ^ q) < 1
  have hφD : φ ∈ Dec (F := E) A := hφ.1
  have hφiD : φ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hφD
  set y := (φ⁻¹ : G E Ω) x with hy
  have hy0 : y ≠ 0 := (map_ne_zero _).mpr hx
  have hxy : x = φ y := by rw [hy, mul_inv_apply]
  have e1 : (φ * (s : G E Ω) * φ⁻¹) x / x = φ ((s : G E Ω) y / y) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hy, map_div₀]
    conv_lhs => rw [show x = φ y from hxy]
  have hz : A.valuation ((s : G E Ω) y / y) ≤ 1 := (val_ratio (Ine_le_Dec A s.2) hy0).le
  have c1 : A.valuation (φ ((s : G E Ω) y / y) - ((s : G E Ω) y / y) ^ q) < 1 := hφ.2 _ hz
  have c2 : A.valuation ((s : G E Ω) y / y - (s : G E Ω) x / x) < 1 := ratio_cong s.2 hφiD hx
  have c3 := cong_pow hz (val_ratio (Ine_le_Dec A s.2) hx).le c2 q
  rw [e1]
  exact cong_trans c1 c3

end DiscreteGroups.sglob.DzType

end
