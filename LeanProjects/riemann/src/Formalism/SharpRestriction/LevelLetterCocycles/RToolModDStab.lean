import Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section DStab

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smul' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem rToolMod_geom (a : LetA O n) (m : ℕ) : ∃ g : LetA O n, (1 + a) ^ m = 1 + a * g := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨1 + g + a * g, by rw [pow_succ, hg]; ring⟩

theorem rToolMod_unit (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (t : LetA O n) (m : ℕ) : IsUnit ((1 + W.π₀ * t) ^ m) := by
  obtain ⟨w, hw⟩ := hπ
  have hp : 2 ≤ PD.p := by
    by_contra h
    have hv := W.v_l
    rcases (show PD.p = 0 ∨ PD.p = 1 by omega) with h0 | h0 <;> rw [h0] at hv
    · rw [Nat.cast_zero, AddValuation.map_zero] at hv
      exact WithTop.top_ne_coe (show (⊤ : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) from hv)
    · rw [Nat.cast_one, AddValuation.map_one] at hv
      have h01 : ((0 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := hv
      exact absurd (WithTop.coe_inj.mp h01) (by norm_num)
  have hp1 : PD.p - 1 ≠ 0 := by omega
  refine IsUnit.pow m ?_
  refine Pi.isUnit_iff.mpr fun i => ?_
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  simp [hw, letπ, zero_pow hp1]

theorem rToolMod_qi_q (hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (m : ℕ)
    (x : W.DD T) :
    Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ m) x, smul_smul, map_pow, ← mul_pow,
    Ring.inverse_mul_cancel _ hqU, one_pow, one_smul]

theorem rToolMod_dStab [NeZero n] (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : DerivationPreservesQLattice W := by
  unfold DerivationPreservesQLattice
  intro hA T' hT i k x hx
  obtain ⟨hbij, hs, hp2⟩ := hA
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hbij).finrank_eq, Module.finrank_self]
  obtain ⟨-, -, h9⟩ := hP9 T' hT hs hp2
  obtain ⟨hring, hmod⟩ := h9 hfin
  obtain ⟨-, hmod2⟩ := hmod
  obtain ⟨hπΔ, -, ⟨w₁, hw₁⟩, -, -, -, ⟨w₂, hw₂⟩, -⟩ := hring
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hπΔ
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]
  have hγπ : W.γA W.gam W.π₀ = W.π₀ + (w₂ : LetA O n) * W.π₀ * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [← hEat, ← hw₂]; ring
  have hγq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      Formalism.MainNotions.LiftingTheory.qp W * (1 + W.π₀ * (w₂ : LetA O n)) := by
    have e1 : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add, map_natCast]
    rw [e1, hγπ]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  have hΔq : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
    intro δ hδ
    simp only [Formalism.MainNotions.LiftingTheory.qp, map_add, map_natCast, hΔπ δ hδ]
  have ha : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw₁, map_mul, map_pow]
    exact (w₁.isUnit.map _).mul (W.EE_π.pow _)
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
    haveI := W.EE_complete
    have hI : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        Ideal.span {((PD.p : ℕ) : W.EE)} := Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    have hJ : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        (⊥ : Ideal W.EE).jacobson := by
      first
        | exact IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact HenselianRing.jac (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
    have h1 := Ideal.mem_jacobson_bot.mp hJ 1
    have hinv := Ring.mul_inverse_cancel _ ha
    have h2 : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) = algebraMap (LetA O n) W.EE W.π₀ *
        (((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * 1 + 1) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add, map_natCast]
      linear_combination (-((PD.p : ℕ) : W.EE)) * hinv
    rw [h2]; exact ha.mul h1
  obtain ⟨e, he⟩ : ∃ e, e = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := ⟨_, rfl⟩
  have hcan1 : ∀ z : W.DD T', W.π₀ • (e • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀, smul_smul, Ring.mul_inverse_cancel _ ha, one_smul]
  have hcan2 : ∀ z : W.DD T', e • (W.π₀ • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀ z, smul_smul, Ring.inverse_mul_cancel _ ha, one_smul]
  have hinj : ∀ z₁ z₂ : W.DD T', W.π₀ • z₁ = W.π₀ • z₂ → z₁ = z₂ := by
    intro z₁ z₂ h; rw [← hcan2 z₁, h, hcan2]
  have hcomm : ∀ (b : LetA O n) (z : W.DD T'), b • (e • z) = e • (b • z) := by
    intro b z
    rw [← algebraMap_smul W.EE b (e • z), ← algebraMap_smul W.EE b z, smul_smul, smul_smul, mul_comm]
  have hγE : ∀ δ ∈ W.DelF, W.γE δ e = e := by
    intro δ hδ
    have h3 : W.γE δ (algebraMap (LetA O n) W.EE W.π₀) = algebraMap (LetA O n) W.EE W.π₀ := by
      rw [W.γE_ext]; exact congrArg (algebraMap (LetA O n) W.EE) (hΔπ δ hδ)
    rw [he]
    calc W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀))
        = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) *
          (algebraMap (LetA O n) W.EE W.π₀ * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) := by
          rw [Ring.mul_inverse_cancel _ ha, mul_one]
      _ = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * algebraMap (LetA O n) W.EE W.π₀) *
          Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by rw [map_mul, h3]; ring
      _ = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by
          rw [Ring.inverse_mul_cancel _ ha, map_one, one_mul]
  have hγsm : ∀ (g : W.Gam) (b : LetA O n) (z : W.DD T'),
      W.γD T' g (b • z) = W.γA g b • W.γD T' g z := γD_smul' W T'
  have hdOp : ∀ z, Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' z = e • (W.γD T' W.gam z - z) := fun z => by rw [he]; rfl
  have hγy : ∀ (m : ℕ) (z : W.DD T'), W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ m • z) =
      (1 + W.π₀ * (w₂ : LetA O n)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • W.γD T' W.gam z) := by
    intro m z
    rw [hγsm, map_pow, hγq, mul_pow, smul_smul, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ m)]
  obtain ⟨⟨hEx, hΔx⟩, hq⟩ := hx
  have hγE_i : W.γA W.gam (letE i : LetA O n) = letE i := by
    funext j
    show W.γ₀ W.gam ((letE i : LetA O n) j) = (letE i : LetA O n) j
    simp only [letE, Pi.single_apply]
    split_ifs <;> simp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN Formalism.MainNotions.CrystallineLiftingInputs.DL
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hEγ : (letE i : LetA O n) • W.γD T' W.gam x = W.γD T' W.gam x := by
      rw [← hγE_i, ← hγsm, hEx]
    rw [hdOp, hcomm, smul_sub, hEγ, hEx]
  · intro δ hδ
    rw [hdOp, W.γD_smul, hγE δ hδ, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hΔx δ hδ]
  · split_ifs at hq ⊢ with hk
    · obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) k.toNat
      have hu := rToolMod_unit W ⟨w₁, hw₁⟩ (w₂ : LetA O n) k.toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ k.toNat - 1 := by
        rw [hg]; ring
      have hyΔ : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.NΔ T' :=
        show Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T' ∧ ∀ δ ∈ W.DelF,
            W.γD T' δ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) = Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x from
          ⟨hq, fun δ hδ => by rw [hγsm, map_pow, hΔq δ hδ, hΔx δ hδ]⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) - Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x =
          W.π₀ • x' := hx'
      have key : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' x = (↑hu.unit⁻¹ : LetA O n) •
          (x' - ((w₂ : LetA O n) * g) • (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x)) := by
        apply hinj
        rw [hdOp, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat), hcan1,
          smul_comm W.π₀ (↑hu.unit⁻¹ : LetA O n), smul_sub W.π₀, ← hx'', hγy, smul_smul W.π₀, hpg,
          sub_smul, one_smul]
        simp only [smul_sub, smul_smul, ← mul_assoc, hu.val_inv_mul, one_mul]
        abel
      rw [key]
      exact (W.N T').smul_mem _ ((W.N T').sub_mem hx'N ((W.N T').smul_mem _ hq))
    · obtain ⟨y, hyN, rfl⟩ := hq
      obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) (-k).toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat - 1 := by
        rw [hg]; ring
      have hyΔ' : ∀ δ ∈ W.DelF, W.γD T' δ y = y := by
        intro δ hδ
        have h1 := hΔx δ hδ
        rw [hγsm, map_pow, hΔq δ hδ] at h1
        rw [← rToolMod_qi_q W T' hqU (-k).toNat (W.γD T' δ y), h1, rToolMod_qi_q W T' hqU]
      have hyΔ : y ∈ W.NΔ T' :=
        show y ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ y = y from ⟨hyN, hyΔ'⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam y - y = W.π₀ • x' := hx'
      refine ⟨(1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat • x' + ((w₂ : LetA O n) * g) • y,
        (W.N T').add_mem ((W.N T').smul_mem _ hx'N) ((W.N T').smul_mem _ hyN), ?_⟩
      apply hinj
      rw [hdOp, hcan1, hγy, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat), smul_add W.π₀,
        smul_comm W.π₀ ((1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat), ← hx'', smul_smul W.π₀, hpg,
        sub_smul, one_smul]
      simp only [smul_sub, smul_add, smul_smul, mul_comm]
      abel

end DStab

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
