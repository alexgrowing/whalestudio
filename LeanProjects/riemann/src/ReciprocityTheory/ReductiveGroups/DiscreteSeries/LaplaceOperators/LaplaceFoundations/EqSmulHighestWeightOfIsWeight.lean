import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueU
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eq_smul_highestWeight_of_isWeight {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) {v : T.V}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T) Λ v) : ∃ c : ℂ, v = c • T.w := by
  by_cases h0 : v = 0
  · exact ⟨0, by simp [h0]⟩
  have hd := HW.torep_dτ_of_wt T hv
  have hraise : ∀ a b, a < b → ε a = ε b → T.dτ (Matrix.single a b 1) v = 0 := by
    intro a b hab he
    by_contra hx
    have hwx : ∀ c, T.dτ (Matrix.single c c 1) (T.dτ (Matrix.single a b 1) v) =
        (((Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c : ℝ) : ℂ) • T.dτ (Matrix.single a b 1) v := by
      intro c
      have hR := HW.KType.kRel T c c a b rfl he
      have h1 := congrArg (fun f : Module.End ℂ T.V => f v) hR
      simp only [HW.kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe] at h1
      have hab' : a ≠ b := ne_of_lt hab
      rw [hd c, map_smul] at h1
      by_cases hca : c = a
      · subst hca
        have hcb : ¬ b = c := fun h => hab' h.symm
        rw [if_pos rfl, if_neg hcb] at h1
        simp only [LinearMap.zero_apply, sub_zero, ContinuousLinearMap.coe_coe] at h1
        rw [sub_eq_iff_eq_add] at h1
        rw [h1]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg (Ne.symm hcb)]
        push_cast
        module
      · by_cases hcb : b = c
        · subst hcb
          rw [if_neg hca, if_pos rfl] at h1
          simp only [LinearMap.zero_apply, zero_sub, ContinuousLinearMap.coe_coe] at h1
          rw [sub_eq_iff_eq_add] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg hca]
          push_cast
          module
        · rw [if_neg hca, if_neg hcb] at h1
          simp only [LinearMap.zero_apply, sub_zero] at h1
          rw [sub_eq_zero] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg hca, if_neg (Ne.symm hcb)]
          simp
    obtain ⟨cc, hc, he'⟩ := HW.KType.weight_le T hx hwx
    let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
        map_add' := by
          intro f g
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp [Finset.mul_sum, mul_left_comm] }
    have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
      intro x
      simp [ψ, Pi.single_apply]
    have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
      abel
    rw [hl] at he'
    have h := congrArg ψ he'
    simp only [map_sum, map_smul, root, map_sub, hψ, smul_eq_mul] at h
    have hr : ∑ x, ∑ y, (cc x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
      refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
      by_cases h0 : cc x y = 0
      · simp [h0]
      · have hxy := (hc x y h0).1
        have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique T h0 ⟨hd, hraise⟩
  exact ⟨c, hc⟩

section Span

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

theorem sumF' {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_mem_Kset (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) : kE k r h ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kE_conjTranspose, ← kE_mul]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hh
    rw [hh, kE_one]
  · ext i j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · rw [hε i hi, hε j hj]; simp
      · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
    · rw [kE_row _ _ hi]
      by_cases hij : i = j
      · subst hij; ring
      · rw [if_neg hij]; simp

def dg (θ : Fin (2 * r + k + 1) → ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

def th2 (θ : Fin (2 * r + k + 1) → ℝ) : Fin (2 * r + k + 1) → ℝ := fun a => if a.val < k then 0 else θ a

def th1 (θ : Fin (2 * r + k + 1) → ℝ) : Fin k → ℝ := fun q => θ (fI k r q)

def dgk (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I))

theorem dg_mem (θ : Fin (2 * r + k + 1) → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dg, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dg, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dgk_mem (t : Fin k → ℝ) : dgk t ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have := dg_mem (k := k) (r := 0) (ε := fun _ => true)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dgk, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dgk, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dg_split (θ : Fin (2 * r + k + 1) → ℝ) : dg θ = kE k r (dgk (th1 θ)) * dg (th2 θ) := by
  ext i j
  unfold dg
  rw [Matrix.mul_diagonal]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [dg, dgk, kE, th1, th2, dif_pos hi, dif_pos hj, if_pos hj, Matrix.diagonal_apply, fI]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]; simp
    · simp only [dg, th2, if_neg hj, Matrix.diagonal_apply]
      rw [kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; exact absurd hi hj
      · simp [hij]
  · simp only [dg, th2, Matrix.diagonal_apply]
    rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem central_diagonal_commute (θ : Fin (2 * r + k + 1) → ℝ) (h : Matrix (Fin k) (Fin k) ℂ) :
    kE k r h * dg (th2 θ) = dg (th2 θ) * kE k r h := by
  ext i j
  rw [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp [th2, hi, hj]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; ring
    · rw [if_neg hij]; simp

variable (T : S7.KType ε Λ)

def rhoK (h : Matrix (Fin k) (Fin k) ℂ) : T.V →L[ℂ] T.V := HW.torepSig T (kE k r h)

def spanW : Submodule ℂ T.V :=
  sInf {S | T.w ∈ S ∧ ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S}

theorem w_mem_spanW : T.w ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun _ hS => hS.1

theorem spanW_stable {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) {v : T.V}
    (hv : v ∈ spanW (k := k) (r := r) T) : rhoK (k := k) (r := r) T h v ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun S hS => hS.2 h hh v (Submodule.mem_sInf.1 hv S hS)

theorem spanW_le {S : Submodule ℂ T.V} (hw : T.w ∈ S)
    (hS : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S) :
    spanW (k := k) (r := r) T ≤ S :=
  sInf_le ⟨hw, hS⟩

theorem torep_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) (v : T.V) : HW.torepSig T (a * b) v = HW.torepSig T a (HW.torepSig T b v) := by
  rw [(HW.torep_isURepOn T).1.2 a ha b hb]; rfl

theorem spanW_scalar (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (θ : Fin (2 * r + k + 1) → ℝ)
    {x : T.V} (hx : x ∈ spanW (k := k) (r := r) T) :
    HW.torepSig T (dg (th2 θ)) x = Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I) • x := by
  set c := Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I)
  let S : Submodule ℂ T.V := LinearMap.ker ((HW.torepSig T (dg (th2 θ)) : T.V →ₗ[ℂ] T.V) - c • LinearMap.id)
  have hmem : ∀ y, y ∈ S ↔ HW.torepSig T (dg (th2 θ)) y = c • y := by
    intro y
    simp [S, sub_eq_zero]
  have hle : spanW (k := k) (r := r) T ≤ S := by
    refine spanW_le T ((hmem _).2 (HW.torep_wt_w T (th2 θ) (dg_mem _))) ?_
    intro h hh v hv
    rw [hmem] at hv ⊢
    unfold rhoK
    rw [← torep_mul T (dg_mem _) (kE_mem_Kset hε hh), ← central_diagonal_commute, torep_mul T (kE_mem_Kset hε hh) (dg_mem _), hv,
      map_smul]
  exact (hmem x).1 (hle hx)

end Span

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
