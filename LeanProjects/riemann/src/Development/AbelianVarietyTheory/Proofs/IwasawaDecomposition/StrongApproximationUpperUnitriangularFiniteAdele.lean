import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace GlobalTheory.UnipApproxGL

open NumberField IsDedekindDomain Matrix PIW.ClassFinD

variable {F : Type} [Field F] [NumberField F]

theorem approx (x e : FiniteAdeleRing (𝓞 F) F) :
    ∃ r : F, e * (x + algebraMap F (FiniteAdeleRing (𝓞 F) F) r) ∈ Ohat F := by
  have hU : IsOpen ((fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) ⁻¹'
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F)) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage (continuous_const.mul (continuous_const.add continuous_id))
  have h0 : (fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) (-x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F := by
    show e * (x + -x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
    rw [add_neg_cancel, mul_zero]
    exact (Ohat F).zero_mem
  obtain ⟨r, hr⟩ := (PI.UnipApproxD.additive_dense_integers F).exists_mem_open hU ⟨-x, h0⟩
  exact ⟨r, hr⟩

theorem row_exists (n : ℕ) (u : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hu : IsUpperUni u) (i : Fin n) (e : Fin n → FiniteAdeleRing (𝓞 F) F) :
    ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j, i < j → e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
  classical
  have key : ∀ m : ℕ, ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j : Fin n, i < j → j.val < m →
        e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun k => if k = i then 1 else 0, by simp, fun k hk => ?_, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      simp [ne_of_lt hk]
    | succ m ih =>
      obtain ⟨y, hy1, hy0, hyc⟩ := ih
      by_cases h : ∃ hm : m < n, i < (⟨m, hm⟩ : Fin n)
      · obtain ⟨hm, him⟩ := h
        obtain ⟨r, hr⟩ := approx (∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k ⟨m, hm⟩)
          (e ⟨m, hm⟩)
        have hsum : ∀ j, ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F)
              (y k + if k = (⟨m, hm⟩ : Fin n) then r else 0) * u k j
            = ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j +
                algebraMap F (FiniteAdeleRing (𝓞 F) F) r * u ⟨m, hm⟩ j := by
          intro j
          simp only [map_add, add_mul, Finset.sum_add_distrib, apply_ite (algebraMap F _), map_zero,
            ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        refine ⟨fun k => y k + if k = (⟨m, hm⟩ : Fin n) then r else 0, ?_, ?_, ?_⟩
        · simp [hy1, ne_of_lt him]
        · intro k hk
          simp [hy0 k hk, ne_of_lt (hk.trans him)]
        · intro j hij hjm
          rw [hsum]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
          · rw [hu.1 ⟨m, hm⟩ j (by rw [Fin.lt_def]; exact hj), mul_zero, add_zero]
            exact hyc j hij hj
          · have hjM : j = ⟨m, hm⟩ := Fin.ext hj
            subst hjM
            rw [hu.2, mul_one]
            exact hr
      · refine ⟨y, hy1, hy0, fun j hij hjm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
        · exact hyc j hij hj
        · exfalso
          have hm : m < n := hj ▸ j.isLt
          exact h ⟨hm, by rwa [show (⟨m, hm⟩ : Fin n) = j from Fin.ext hj.symm]⟩
  obtain ⟨y, h1, h2, h3⟩ := key n
  exact ⟨y, h1, h2, fun j hij => h3 j hij j.isLt⟩

theorem matInt_inv_of_upperUni {n : ℕ} (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hg : IsUpperUni g.val) (hi : MatInt g.val) : MatInt g⁻¹.val := by
  have hdet : g.val.det = 1 := by
    rw [det_of_upperTriangular (fun i j hij => hg.1 i j hij)]
    simp [hg.2]
  have h1 : g.val * adjugate g.val = 1 := by rw [mul_adjugate, hdet, one_smul]
  have hinv : g⁻¹.val = adjugate g.val := by
    calc g⁻¹.val = g⁻¹.val * (g.val * adjugate g.val) := by rw [h1, mul_one]
      _ = adjugate g.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
  let W' : Matrix (Fin n) (Fin n) (Ohat F) := fun i j => ⟨g.val i j, hi i j⟩
  have hW : g.val = (Ohat F).subtype.mapMatrix W' := by ext i j; rfl
  intro i j
  rw [hinv, hW, ← RingHom.map_adjugate]
  exact ((adjugate W') i j).2

theorem unipApprox : PIW.ClassFinD.UnipApprox := by
  classical
  intro F _ _ n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose y hy1 hy0 hyc using fun i => row_exists n u.val hu i
    (fun j => (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j)
  let Y : Matrix (Fin n) (Fin n) F := fun i k => y i k
  have hdet : Y.det = 1 := by
    rw [det_of_upperTriangular (fun i k hki => hy0 i k hki)]
    simp [Y, hy1]
  let Yg : GL (Fin n) F :=
    ((Matrix.isUnit_iff_isUnit_det Y).mpr (by rw [hdet]; exact isUnit_one)).unit

  let P : Fin n → Fin n → FiniteAdeleRing (𝓞 F) F := fun i j =>
    ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y i k) * u.val k j
  have hPlow : ∀ i j, j < i → P i j = 0 := by
    intro i j hji
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hy0 i k hk, map_zero, zero_mul]
    · rw [hu.1 k j (lt_of_lt_of_le hji hk), mul_zero]
  have hPdiag : ∀ i, P i i = 1 := by
    intro i
    show ∑ k, _ = _
    rw [Finset.sum_eq_single i]
    · rw [hy1 i, map_one, one_mul, hu.2]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hy0 i k hk, map_zero, zero_mul]
      · rw [hu.1 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  let w := (diagGL n τ)⁻¹ * glIncl F n Yg * u * diagGL n τ
  have hw : ∀ i j, w.val i j =
      (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j := by
    intro i j
    simp only [w, ← map_inv, Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [Matrix.mul_apply]
    rfl
  have hwu : IsUpperUni w.val := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hw, hPlow i j hji, mul_zero, zero_mul]
    · rw [hw, hPdiag, mul_one, Units.inv_mul]
  have hwi : MatInt w.val := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hw]
      have := hyc i j hij
      rw [show (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j =
        (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j * P i j by ring]
      exact this
    · rw [hwu.2]; exact (Ohat F).one_mem
    · rw [hwu.1 i j hji]; exact (Ohat F).zero_mem
  refine ⟨Yg⁻¹, w, ⟨hwi, matInt_inv_of_upperUni w hwu hwi⟩, ?_⟩
  simp only [w, map_inv]
  group

end GlobalTheory.UnipApproxGL

end
