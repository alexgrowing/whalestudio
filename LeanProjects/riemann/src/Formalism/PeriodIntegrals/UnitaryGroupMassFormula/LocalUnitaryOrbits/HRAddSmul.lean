import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasureImageCosets
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def lamA (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def lamP (a : ℕ) (ϖ : Fv F v) : AddSubgroup (TupV (E := E) v n a) :=
  (lamA v Λ a).map (DistribMulAction.toAddMonoidHom (TupV (E := E) v n a) (sc (E := E) v ϖ))

def clsU (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a

theorem hR_add_smul (s : Fv F v ⊗[F] E) (x z y w : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + s • z) (y + s • w) = hR (Fv F v) σ J x y + s * hR (Fv F v) σ J x w +
      sigR (Fv F v) σ s * hR (Fv F v) σ J z y + sigR (Fv F v) σ s * s * hR (Fv F v) σ J z w := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_sc (x : Fv F v) : sigR (Fv F v) σ (sc (E := E) v x) = sc (E := E) v x := by
  simp [sigR, sc]

theorem unif_int {ϖ : Fv F v} (hϖ : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ]
  exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by
    rw [← ofAdd_zero, Multiplicative.ofAdd_le]; norm_num)

theorem sc_mul_mem {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : sc (E := E) v x * c ∈ OEv (E := E) v := by
  have h := (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).smul_mem
    (⟨x, hx⟩ : v.adicCompletionIntegers F) hc
  have e : (⟨x, hx⟩ : v.adicCompletionIntegers F) • c = sc (E := E) v x * c := by
    show x • c = sc (E := E) v x * c
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e] at h
  exact h

theorem oev_add {c d : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v) (hd : d ∈ OEv (E := E) v) :
    c + d ∈ OEv (E := E) v :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).add_mem hc hd

theorem nearT_add {a : ℕ} (hSD : IsSDLoc σ J v Λ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ)
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (X Z : TupV (E := E) v n a)
    (hX : X ∈ LamT v Λ a) (hZ : Z ∈ LamT v Λ a) (hN : X ∈ NearT v σ J ϖ T) :
    X + sc (E := E) v ϖ • Z ∈ NearT v σ J ϖ T := by
  intro i j
  obtain ⟨c, hc, hce⟩ := hN i j
  have hh : ∀ p q : Fin a, ∀ P Q : TupV (E := E) v n a, P ∈ LamT v Λ a → Q ∈ LamT v Λ a →
      hR (Fv F v) σ J (P p) (Q q) ∈ OEv (E := E) v :=
    fun p q P Q hP hQ => (hSD (Q q)).1 (hQ q) (P p) (hP p)
  have hi := unif_int v hϖ
  refine ⟨c + (hR (Fv F v) σ J (X i) (Z j) + hR (Fv F v) σ J (Z i) (X j) +
      sc (E := E) v ϖ * hR (Fv F v) σ J (Z i) (Z j)), ?_, ?_⟩
  · exact oev_add v hc (oev_add v (oev_add v (hh i j X Z hX hZ) (hh i j Z X hZ hX))
      (sc_mul_mem v hi (hh i j Z Z hZ hZ)))
  · have e1 : gramR (Fv F v) σ J (X + sc (E := E) v ϖ • Z) i j =
        hR (Fv F v) σ J (X i + sc (E := E) v ϖ • Z i) (X j + sc (E := E) v ϖ • Z j) := rfl
    have e2 : gramR (Fv F v) σ J X i j = hR (Fv F v) σ J (X i) (X j) := rfl
    rw [e1, hR_add_smul, sigR_sc]
    rw [e2] at hce
    linear_combination hce

theorem countU_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasU σ J ψ v Λ a Y)
    (hI : IdxU σ J ψ v Λ a Y) (hC : ClsU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  set μ := dX σ J ψ v a with hμdef
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, dX, dif_pos hμ]
    exact hμ.choose_spec.1
  have hPL : lamP v Λ a ϖ ≤ lamA v Λ a := by
    rintro _ ⟨Z, hZ, rfl⟩ i
    have : (sc (E := E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl
    show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ
    rw [this]
    have e : sc (E := E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by
      ext p
      simp only [Pi.smul_apply, smul_eq_mul]
      show _ = ϖ • Z i p
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]
    exact (latLoc (E := E) v Λ).smul_mem _ (hZ i)
  have hIdx := hI hG ϖ hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h0
    have : qv v = 0 := by simp [qv, h0]
    linarith
  have hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0 := by
    rw [hIdx]; exact pow_ne_zero _ hN0
  have eL := PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin
  have eS := measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin
    {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)}
    (by
      rintro x hx y ⟨Z, hZ, hZe⟩
      simp only [Set.mem_setOf_eq]
      rw [AddSubgroup.coe_add, ← hZe]
      exact nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx)
  have himg : ((↑) : lamA v Λ a → TupV (E := E) v n a) ''
      {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X, h1⟩, h2, rfl⟩
  rw [himg] at eS
  have eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) *
      μ (lamP v Λ a ϖ) := eL
  rw [eS, eL', ← mul_assoc]
  congr 1
  have hcard := hC hG ϖ hϖ
  change (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _
  rw [← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a) := by
      simp [qv]
    rw [hqv]
    have hle : a ^ 2 ≤ 2 * n * a := by nlinarith
    have e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e3]
    have e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1 := by
      rw [zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')
    linear_combination (-(qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a)) * e4
  · have hP0 : 0 ≤ prodEta (E := E) v n a := by
      unfold prodEta
      refine Finset.prod_nonneg fun j _ => ?_
      have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
      have habs : |((etaV (E := E) v : ℤ) : ℝ)| = 1 := by
        unfold etaV; split_ifs <;> norm_num
      have h1 : ((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
        calc _ ≤ |((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))| :=
              le_abs_self _
          _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
              rw [abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]
          _ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
      linarith
    exact mul_nonneg (zpow_nonneg hq.le _) hP0

end PI.OmLocU
