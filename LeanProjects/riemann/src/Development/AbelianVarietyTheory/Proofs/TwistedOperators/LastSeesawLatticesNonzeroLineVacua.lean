import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionRankZeroExtRestriction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalProjectionPreservesDepthLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroVacuumBesselLineLatticeRankZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a b : WO S₀ T) :
    symplO S T (d.ext0 T a) (d.ext0 T b) = symplO S₀ T a b := by
  have h := d.hO_ext T 0 0 0 0 a b
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplO, symplO, h]

theorem isHalf_mul_right {k l m : ℕ} {e : AE D} {u : Mx D k l} (p : Mx D l m) (hu : IsHalf e u) : IsHalf e (u ⬝ p) := by
  intro i j
  show e * ∑ r, u i r * p r j = ∑ r, u i r * p r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [← mul_assoc, hu i r]

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

open GlobalTheory.FinPl.VLast.KernPf (wittCoreRestrictionHom wittCoreRestrictionHom_apply wittDecomposition_rankZero_ext_restriction) in

theorem lastLat_rankZero (hψ : IsStdChar D ψ (-1)) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'')
    (Γ : AddSubgroup (WO J.W T)) (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X))
    (hX : ∀ u, u ∈ ΓX ↔ J.d.ext0 T (o.resT J.W₀ u).1 ∈ Γ ∧ (show WO J.W₀ (negSp L'') from (o.resT J.W₀ u).2) ∈ ΓL)
    (h₁ : ∃ f, VacG ψ J.W T Γ f ∧ f ≠ 0) (h₂ : ∃ f, VacG ψ J.W₀ (negSp L'') ΓL f ∧ f ≠ 0) :
    LastLat ψ J o Γ ΓL ΓX := by
  have s0 := @GlobalTheory.SplitScalar.symplO_zero_right D
  have mA : ∀ a : WO J.W₀ T, J.d.ext0 T a ∈ Γ → (o.resT J.W₀).symm (a, 0) ∈ ΓX := fun a ha => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨ha, zero_mem _⟩
  have mB : ∀ b : WO J.W₀ L'', (show WO J.W₀ (negSp L'') from b) ∈ ΓL → (o.resT J.W₀).symm (0, b) ∈ ΓX := fun b hb => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨by rw [map_zero]; exact zero_mem _, hb⟩
  have n : ∀ a b : WO J.W₀ L'', ψ (symplO J.W₀ L'' a b) = 1 → ψ (symplO J.W₀ (negSp L'') a b) = 1 := fun a b h => by
    have e : symplO J.W₀ (negSp L'') a b = -symplO J.W₀ L'' a b := by
      simp only [symplO, hO, negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [e, ← GlobalTheory.CjNeg.conj_psi hψ, h, map_one]
  have hA : ∀ e (u : WO J.W₀ T), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (u, 0)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, add_zero]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have hB : ∀ e (u : WO J.W₀ L''), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (0, u)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, zero_add]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have back : ∀ u : WO J.W T, J.d.ext0 T (wittCoreRestrictionHom J.d T u) = u := wittDecomposition_rankZero_ext_restriction J.d T
  refine ⟨fun (w : WO J.W₀ X) hw => ⟨⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun (u : WO J.W₀ L'') hu => n _ _ ?_,
    fun e he (u : WO J.W₀ L'') hu hh => n _ _ ?_⟩, ?_⟩
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.1 _ (mA _ hu')
    rw [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_snd, nsmul_zero, s0, add_zero] at this
    rw [← back u, ← map_nsmul, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.2 e he _ (mA _ hu') (hA e _ (isHalf_mul_right _ hh))
    rw [o.symplO_resT, AddEquiv.apply_symm_apply, s0, add_zero] at this
    rw [← back u, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have := hw.1 _ (mB u hu)
    rwa [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_fst, nsmul_zero, s0, zero_add] at this
  · have := hw.2 e he _ (mB u hu) (hB e u hh)
    rwa [o.symplO_resT, AddEquiv.apply_symm_apply, s0, zero_add] at this
  · obtain ⟨f₁, a₁, b₁⟩ := h₁
    obtain ⟨f₂, a₂, b₂⟩ := h₂
    refine ⟨f₁, f₂, a₁, a₂, b₁, b₂, ?_⟩
    show VacG ψ J.W₀ X _ (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂))
    refine ⟨o.isThetaFunO_boxT (GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero J.d T a₁.1) (GlobalTheory.CjNeg.theta_negT' hψ a₂.1),
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, map_nsmul (o.resT J.W₀), Prod.smul_fst, Prod.smul_snd, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        map_nsmul (J.d.ext0 T), a₁.2.1 _ h1, GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (a₂.2.1 _ h2)
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        a₁.2.2 e he _ h1 (GlobalTheory.RankZeroVac.isHalf_wittHyperbolicExtendByZero_apply J.d T (GlobalTheory.AscInh.isHalf_mul o.pA hh)), GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))
        (a₂.2.2 e he _ h2 (GlobalTheory.AscInh.isHalf_mul o.pB hh))

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem latCore_zero_split : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (u : WO (G.V (.core 1)) (G.V (.core 0))), u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.resT _ u).1 ∈ latRow G 0 ∧ (F.oz.resT _ u).2 ∈ lineLat F 0 := by
  intro D q T L μ0 hL sc G W M hM F hF h u
  have e1 := GlobalTheory.T.orthogonal_projection_preserves_depth_lattice D q T L μ0 hL sc G W M hM F hF
  have e2 := GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero D q T L μ0 hL sc G W M hM F hF h
  have hu : F.oz.jA ⬝ (F.oz.pA ⬝ u) + F.oz.jB ⬝ (F.oz.pB ⬝ u) = u := (F.oz.resT _).symm_apply_apply u
  have hl : F.oz.pB ⬝ u ∈ lineLat F 0 ↔ (F.oz.resT _).symm (0, F.oz.pB ⬝ u) ∈ latCore G 0 := Iff.rfl
  show u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.pA ⬝ u) ∈ latRow G 0 ∧ F.oz.pB ⬝ u ∈ lineLat F 0
  rw [hl, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB ⬝ (F.oz.pB ⬝ u)), ← e2]
  constructor
  · intro hm
    have ha := e1 u hm
    refine ⟨ha, ?_⟩
    have hb : F.oz.jB ⬝ (F.oz.pB ⬝ u) = u - F.oz.jA ⬝ (F.oz.pA ⬝ u) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hu
    rw [hb]; exact sub_mem hm ha
  · rintro ⟨ha, hb⟩
    rw [← hu]
    exact add_mem ha hb

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem lastLat_std : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  intro D q T L μ0 hL sc G W M hM F hF
  have hψ := W.ψ_std
  have hline0 : ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := GlobalTheory.T.exists_ne_zero_vacuum_besselLineLattice_rankZero D q T L μ0 hL sc G W M hM F hF
  refine ⟨fun ρ hρ => ?_, fun v h => ?_⟩
  · rcases ρ with _ | σ
    · exact hline0
    · obtain ⟨-, -, h3⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D q T L μ0 hL sc G W M hM F hF
      exact GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ hψ _ _ _ _ (G.sp.P_is (2 * (σ + 1) + 1) (by omega)).sd (h3 (σ + 1)) _ le_rfl
  · have hm : 0 < D.R.m := by omega
    have hdep := dep_vac W 0 hm
    refine lastLat_rankZero hψ (F.jac v 0 h) F.oz _ _ _ (latCore_zero_split D q T L μ0 hL sc G W M hM F hF h) ?_ hline0
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (W.vac 0), ⟨GlobalTheory.CjNeg.theta_negS' hψ hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.1 u hu))
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.2 e he u hu hh))
    · intro h0
      apply GlobalTheory.SeeSaw.Inh.vac_ne_zero (W.vac_is 0 hm)
      funext w
      have h1 := congrFun h0 w
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Pi.zero_apply, map_eq_zero] at h1
      exact (map_eq_zero (starRingEnd ℂ)).1 h1

end GlobalTheory.LastSeeSaw

end
