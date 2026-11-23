import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KTwoAwayLevel

theorem mem_mL_of_fix {I : AutInst} (g : ℕ) {t : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (ht : t ∈ IntAf I.F I.E) {z : VA I}
    (hz : z ∈ I.Lf) (hfix : ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t) • z = z) : z ∈ mL I g := by
  have e : z = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (t • z) := by rw [smul_smul]; exact hfix.symm
  rw [e]
  exact Submodule.subset_span ⟨t • z, I.Lf.smul_mem (⟨t, ht⟩ : IntAf I.F I.E) hz, rfl⟩

theorem conj_fix {I : AutInst} {a y : I.Gf} (ha : a ∈ I.Kset) (hy : y ∈ I.Kset) (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hc : ∀ i j, c * (I.fmat y - 1) i j = (I.fmat y - 1) i j) {w : VA I} (hw : w ∈ I.Lf) :
    (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w ∈ I.Lf ∧
      c • ((I.fmat (a⁻¹ * y * a) - 1) *ᵥ w) = (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w := by
  have hK : a⁻¹ * y * a ∈ I.Kset := by
    show ((a⁻¹ * y * a : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (inv_mem ha) hy) ha
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hK hw) hw
  · have hM : c • (I.fmat y - 1) = I.fmat y - 1 := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, hc]
    have hinv : I.fmat a⁻¹ * I.fmat a = 1 := by
      simp only [Formalism.MainNotions.S.AutInst.fmat]
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    have e : I.fmat (a⁻¹ * y * a) - 1 = I.fmat a⁻¹ * (I.fmat y - 1) * I.fmat a := by
      simp only [Formalism.MainNotions.S.AutInst.fmat] at hinv ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, ← hinv]
    rw [e, ← Matrix.smul_mulVec]
    conv_rhs => rw [← hM]
    rw [Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7}

open Classical in
theorem exists_div_indP (v : GlobalTheory.FinPl.Pl D) (g : ℕ) (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, s ∈ Formalism.UG.intAd D.host.F ∧
      (g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * s = GlobalTheory.FinPl.KOpen.indP D (· = v) := by
  have hg' : g ≠ 0 := by rintro rfl; exact hg (by simp)
  have hg0 : (g : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hg'
  refine ⟨GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹,
    fun w => ?_, ?_⟩
  · have e : (GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹) w =
        (if w = v then 1 else 0) * algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹ := rfl
    rw [e]
    by_cases hw : w = v
    · subst hw
      have h2 : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹) =
          w.valuation D.host.F (g : D.host.F)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      rw [if_pos rfl, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, h2, map_inv₀]
      have h1 : w.valuation D.host.F (g : D.host.F) = 1 := by
        have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (g : 𝓞 D.host.F)
        rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hg] at this
        simpa using this
      rw [h1, inv_one]
    · rw [if_neg hw, zero_mul]; exact zero_mem _
  · rw [mul_left_comm, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) g, ← map_mul,
      mul_inv_cancel₀ hg0, map_one, mul_one]

open Classical in
theorem fix_of_grpAt {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (g : ℕ)
    (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ grpAt (D.sp.Y 0) (· = v)) :
    ∃ t ∈ IntAf I.F I.E, ∀ i j, (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t *
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j =
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j := by
  subst h
  obtain ⟨s, hs, hgs⟩ := exists_div_indP v g hg
  refine ⟨(1 : (Formalism.L2.SG.InstExistsPf.instOf D).E) ⊗ₜ[(Formalism.L2.SG.InstExistsPf.instOf D).F] s, Subring.subset_closure (Or.inr ⟨⟨s, hs⟩, rfl⟩), fun i j => ?_⟩
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [ContinuousMulEquiv.symm_apply_apply] at e
  have hf : (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA rfl)) κ).2) =
      (Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) :=
    (congrArg Units.val e).symm
  have key : ∀ i j : Fin (D.sp.Y 0).rank, (1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v)) *
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j := by
    intro i j
    have hb : (Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j ∈ idAt D (· = v) :=
      (GlobalTheory.FinPl.SetCut.mem_congGrp_iff _ _ κ).1 hκ i j
    have hent : ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
        Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply]
      congr 1
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    have hm := congrArg (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
      (GlobalTheory.FinPl.KOpen.e_mul_fin hb)
    rw [map_mul, Algebra.TensorProduct.comm_tmul] at hm
    rw [hent]
    exact hm
  have hg1 : ((g : ℕ) : D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) * ((1 : D.host.E) ⊗ₜ[D.host.F] s) =
      1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v) := by
    rw [← hgs, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := D.host.E)) g,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hf]
  exact (congrArg (fun c => c * ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j) hg1).trans
    (key i j)

theorem k2cong_conj_of_grpAt : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (v : GlobalTheory.FinPl.Pl D), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ κ : GA D (D.sp.Y 0), κ ∈ grpAt (D.sp.Y 0) (· = v) → (iotaX X h κ).2 ∈ X.B.I.Kset → K2cong X.B.I X.B.g X.e0 X.z0 X.bw ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) := by
  intro D X h u v hv κ hκ hK
  obtain ⟨t, ht, hfix⟩ := fix_of_grpAt h v _ hv κ hκ
  have hc : ∀ i j, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (X.B.I.fmat (iotaX X h κ).2 - 1) i j =
      (X.B.I.fmat (iotaX X h κ).2 - 1) i j := by
    rw [X.g_eq]; exact hfix
  have key : ∀ w ∈ X.B.I.Lf,
      (X.B.I.fmat ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) - 1) *ᵥ w ∈ mL X.B.I X.B.g := by
    intro w hw
    obtain ⟨h1, h2⟩ := conj_fix (X.xu_K u) hK _ hc hw
    exact mem_mL_of_fix X.B.g ht h1 h2
  unfold K2cong InMod
  exact ⟨fun a => Submodule.mem_sup_right (key _ (X.vectorsInLattice.1 a).1), Submodule.mem_sup_right (key _ X.vectorsInLattice.2.1),
    fun i => Submodule.mem_sup_right (key _ (X.vectorsInLattice.2.2 i).1)⟩

end GlobalTheory.Core.Mi.KTwoAwayLevel
