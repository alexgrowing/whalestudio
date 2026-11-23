import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.GKGlobalise

theorem kFin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) = GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  apply le_antisymm
  · refine sSup_le fun W hW v hv => ?_
    exact ⟨W, hW.1, hv, hW.2⟩
  · rintro v ⟨A, hA, hv, hs⟩
    exact le_sSup (show A ∈ {W : Submodule ℂ (M.H τ) | FiniteDimensional ℂ W ∧
      Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W} from ⟨hA, hs⟩) hv

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun v hv =>
  (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ v).2 ((GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)).2.2.1 v hv)

theorem globalise : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  intro hP D θ V S M hθ F ⟨haut, hcusp, hK, hL⟩
  have hHC := hP.harishChandraModules
  have hCW := hP.casselmanWallach
  have hk : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ = GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) := fun τ => (kFin_eq M τ).symm
  let e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) :=
    fun τ => (LinearEquiv.ofEq _ _ (hk τ)).toLinearMap
  let T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M := F.compLinearMap e
  have hupd : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) τ (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      T₀ (Function.update u τ w) = F (Function.update (fun τ' => e τ' (u τ')) τ (e τ w)) := by
    intro u τ w
    show F (fun τ' => e τ' (Function.update u τ w τ')) = _
    congr 1
    funext τ'
    exact Function.apply_update (fun τ => e τ) u τ w τ'
  have hGK : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M ∅ 1 0 ∅ T₀ := by
    refine ⟨fun u => (haut _).toIsAutFun, fun u => (haut _).smooth, fun u => hcusp _,
      fun u => ?_, fun u => GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ (haut _),
      fun u k hk => by simp at hk, ?_, ?_⟩
    · rw [Measure.restrict_zero]; exact memLp_measure_zero
    · intro τ k hkm u w hw
      rw [hupd]
      exact hK τ k (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hkm) hkm (fun τ' => e τ' (u τ')) (e τ w) hw
    · intro τ X hX u w hw
      rw [hupd]
      refine hL τ X hX (fun τ' => e τ' (u τ')) (e τ w) ?_
      have hsm : (u τ : M.H τ) ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (GlobalTheory.SmVec.trRep (M.σ τ) (M.fr τ)) := by
        rw [← GlobalTheory.SmVec.sm_eq]; exact kFin_le_sm hHC M τ (u τ).2
      have h1 := GlobalTheory.SmVec.hasDerivAt_dRep hsm (X := X) hX
      show HasDerivAt _ (w : M.H τ) 0
      rw [hw]
      exact h1

  obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M ∅ 1 0 ∅ T₀ hGK
  obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
    GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
  choose π dπ hπ using hπ
  have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
    have ha := hGK.1 u
    obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hGK.2.1 u, hGK.2.2.1 u, (hTU u).2⟩
    exact ⟨x, hx⟩
  let eι := LinearEquiv.ofInjective ι hinj
  let T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
    eι.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
  have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
    have h1 := congrArg Subtype.val (eι.apply_symm_apply ⟨T₀ u, hmem u⟩)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
    intro τ k hk u w hw
    apply hinj
    rw [(hπ τ).2.1 k (GlobalTheory.GKExt.kset_sub hk), hT₀', hT₀']
    have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := GlobalTheory.GKExt.conj_back (M.fr_unit τ)
    have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [hk']; exact hk
    refine (hGK.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
    rw [hw]
    show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
    rw [hk']
  have hL' : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
      (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
      T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
    intro τ X hX u w hw
    apply hinj
    rw [(hπ τ).2.2 X hX, hT₀', hT₀']
    have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
      funext y
      unfold dRep
      congr 1
      funext t
      show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
      rw [GlobalTheory.GKExt.exp_conj_inv (M.fr_unit τ), GlobalTheory.GKExt.conj_back (M.fr_unit τ)]
    exact hGK.2.2.2.2.2.2.2 τ _ (GlobalTheory.GKExt.conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
      (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
    intro τ τ' hne g hg g' hg'
    ext x
    apply hinj
    simp only [ContinuousLinearMap.comp_apply]
    rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
    funext y
    simp only [rTr, mul_assoc]
    exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
  obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK' hL'
  obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
    (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
  let T : Formalism.IndefR.Mult.MMap M := ι.compMultilinearMap TE
  have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
    show ι (TE v) = T₀ u
    rw [hTE1 v u h, hT₀']
  have hMult : Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T := by
    refine ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, fun v k hk => by simp at hk, hequiv, hcont⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  refine ⟨T, hMult, fun u => ?_⟩
  let ue : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M := fun τ => ⟨(u τ : M.H τ), by rw [← kFin_eq M τ]; exact (u τ).2⟩
  refine ⟨fun τ => ⟨(u τ : M.H τ), kFin_le_sm hHC M τ (ue τ).2⟩, fun τ => rfl, ?_⟩
  rw [hext _ ue (fun τ => rfl)]
  show F (fun τ => e τ (ue τ)) = F u
  congr 1

end GlobalTheory.GKGlobalise
