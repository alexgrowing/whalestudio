import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIpFst

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

set_option maxHeartbeats 1600000 in

theorem orbEx : IdemEx → ApproxId → Dens → TopX → AlgRich → AlgStab → SigLaw → HermScale → OrbEx := by
  intro _hIE hAI hDens hTop hAR hAS hSL hHS D n r t hn V hV ψ hψ θ hθ b₀ hb S e hS he fib μt hfib hfibs
    hfibi hμt lam hlam hIntg
  obtain ⟨i1, i2, i3, i4, i5, hemb, i7, i8, i9⟩ := hTop D V.rank r t e
  have hT2 : ∀ a b : ℕ, T2Space (Formalism.IndefR.Datum.Mx D a b) := by
    intro a b
    obtain ⟨j1, -, -, -, -, -, -, -, -⟩ := hTop D a 0 b 1
    let f : Formalism.IndefR.Datum.Mx D a b → PositivityTheory.Rg.Rsw.Em.XS D a 0 b 1 :=
      fun x => ⟨((0 : Formalism.IndefR.Datum.Mx D a 0), x), one_smul _ _, one_smul _ _⟩
    have hf : Continuous f := (continuous_const.prodMk continuous_id).subtype_mk _
    constructor
    intro x y hxy
    obtain ⟨U, W, hU, hW, hxU, hyW, hUW⟩ := t2_separation (x := f x) (y := f y)
      (fun h => hxy (congrArg (fun w => (Subtype.val w).2) h))
    exact ⟨f ⁻¹' U, f ⁻¹' W, hU.preimage hf, hW.preimage hf, hxU, hyW, hUW.preimage f⟩
  haveI := hT2 t t
  haveI := hT2 r r
  obtain ⟨hσfin, hσY, -, hσU, hσS, hσG⟩ :=
    hSL D r t V b₀ S e hS he fib μt hfib hfibs hfibi hμt
  obtain ⟨gk, Gk, hgG, htend, hdec⟩ := hAI D t ψ hψ S e hS lam hlam
  have hRich := hAR D θ hθ V.rank r t n hn S e hS
  let k : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) → PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e → ℂ :=
    fun x z => PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x))
      (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z))
  have hkc : Continuous (fun p : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) × PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
      PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val p.1)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val p.2))) :=
    GlobalTheory.CompanionTheory.OrbExist.continuous_pch₂ hψ
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
      ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp (continuous_subtype_val.comp continuous_snd))
  have hD := hDens (PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e) (↥(PositivityTheory.Rg.Rsw.L.hermS D t e))
    (PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)) lam k (PositivityTheory.Rg.Rsw.Em.algA θ hn S e)
    {z | PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z) = 0}
    {z | PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀)}
    gk (fun j z => Gk j (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)))
    hσfin hkc.measurable (fun x z => (hψ.2.1 _).le) hRich.1
    (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val) continuous_const)
    (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_ip_fst (r := r) (t := t) V).comp continuous_subtype_val)
      continuous_const)
    hσY
    (fun j => ⟨(hgG j).1, (hgG j).2.1, fun z _ => (hgG j).2.2 _ (GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _)⟩)
    htend
    (fun C hC _ hCZ ε hε => by
      have hC' : IsCompact ((fun z : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
          PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) '' C) :=
        hC.image ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val)
      filter_upwards [hdec _ hC'.isClosed (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _, GlobalTheory.CompanionTheory.OrbExist.qv_smul V b₀ e _ z.2.2,
          fun h0 => Set.disjoint_left.1 hCZ hz h0⟩) ε hε] with j hj z hz
      exact hj _ ⟨z, hz, rfl⟩)
    hIntg
  obtain ⟨ν, hνfin, hνsupp, hνint, hνcov⟩ := hD
  have hYae : ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)),
      PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀) :=
    MeasureTheory.ae_iff.2 hσY
  refine ⟨ν, ⟨?_, ?_, ?_, ?_, ?_⟩, hνint⟩
  · refine ⟨fun K hK => ?_⟩
    rw [hemb.map_apply]
    exact hνfin.lt_top_of_isCompact
      ((GlobalTheory.CompanionTheory.OrbExist.isClosed_fixed (a := V.rank) (r := r) (t := t)
        e).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  · rw [hemb.map_apply]
    refine measure_mono_null ?_ hνsupp
    intro z hz hYZ
    exact hz ⟨z.2.1, z.2.2, hYZ.1, hYZ.2⟩
  · intro h hh
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftU V r t h
    have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
      refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS (Formalism.L2.Theta.matHom V h) 1 hh (by simp) Θ
          (fun z => ?_) f hf
        rw [GlobalTheory.CompanionTheory.OrbExist.mm_jn, Units.val_one]
        exact (Matrix.mul_one _).symm
      · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσU h hh Θ fun z => rfl) fun x =>
          Filter.Eventually.of_forall fun z => by
            show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
              PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                (PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).1,
                  PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).2))
            simp only [PositivityTheory.Rg.Rsw.L.qv, PositivityTheory.Rg.Rsw.L.yv, GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.ip_mt]
    have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiU V r t h) 1 hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiU V r t h).continuous.measurable (fun z => rfl) hcov
    rw [one_smul] at this
    exact this
  · intro y hy
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftS V.rank y
    have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
      refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.shU hn y) (by simp)
          (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 y 0 1 (by simp) hy (by simp) (by simp)) Θ
          (fun z => ?_) f hf
        rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
          PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
          fun X => Matrix.one_mul X]
        refine Eq.trans ?_ (GlobalTheory.CompanionTheory.ColumnSplitting.jnBl D n t V.rank r hn (Subtype.val z).1 (Subtype.val z).2 y).symm
        show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1
          ((Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y) = _
        rw [add_comm]
      · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσS y hy Θ fun z => rfl) fun x =>
          hYae.mono fun z hz => by
            show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
              PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                ((Subtype.val z).1, (Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y))
            rw [GlobalTheory.CompanionTheory.OrbExist.qv_shear V b₀ hb e _ _ y hz hy]
    have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiS V.rank y) 1 hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiS V.rank y).continuous.measurable (fun z => rfl) hcov
    rw [one_smul] at this
    exact this
  · intro g hg
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftG V.rank r g
    obtain ⟨c, hc, hcmap⟩ := hHS D t S e hS lam hlam g⁻¹ (GlobalTheory.CompanionTheory.OrbExist.smul_inv_sub e g hg)
    have hκ : ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ V.rank *
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ ^ t =
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) := by
      rw [map_inv, GlobalTheory.CompanionTheory.OrbExist.absA_inv]
      exact GlobalTheory.CompanionTheory.OrbExist.kap _ (GlobalTheory.CompanionTheory.OrbExist.absA_ne D _) V.rank r t hV
    have hkG : ∀ x, ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)), k x z = k (c x) (Θ z) :=
      fun x => Filter.Eventually.of_forall fun z => by
        show PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
          PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val (c x))) (PositivityTheory.Rg.Rsw.L.qv V b₀
            ((Subtype.val z).1, PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
              (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))))
        rw [hc x, ← GlobalTheory.CompanionTheory.OrbExist.pch_conj, GlobalTheory.CompanionTheory.OrbExist.qv_col, GlobalTheory.CompanionTheory.OrbExist.conj_cancel]
    have hcov : MeasureTheory.Measure.map Θ ν =
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) • ν := by
      refine hνcov Θ _ fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.colU hn g) (by simp)
          (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 0 0 (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))
            (by simp) (by simp) (by simp) hg) Θ (fun z => ?_) f hf
        rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
          PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
          fun X => Matrix.one_mul X]
        refine Eq.trans ?_ (GlobalTheory.CompanionTheory.OrbExist.jn_bl hn (Subtype.val z).1 (Subtype.val z).2 1 0 0
          (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))).symm
        show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1 (PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
          (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))) = _
        simp only [PositivityTheory.Rg.Rsw.L.mm, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
      · rw [GlobalTheory.CompanionTheory.OrbExist.trans_int _ lam k f Θ c _ _ (hσG g hg Θ fun z => rfl) hcmap hkG, hκ]
    exact GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g) _ hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g).continuous.measurable (fun z => rfl) hcov

end GlobalTheory.CompanionTheory.OrbExist

end
