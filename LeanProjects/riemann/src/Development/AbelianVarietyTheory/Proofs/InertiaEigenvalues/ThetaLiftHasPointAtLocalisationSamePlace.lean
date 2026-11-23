import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiftPoint

theorem root_map_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (htop : ⨆ μ, f.maxGenEigenspace μ = ⊤) {C : Type} [Field C] (φ : K →+* C) (c : C)
    (hc : (f.charpoly.map φ).IsRoot c) : ∃ μ, f.maxGenEigenspace μ ≠ ⊥ ∧ φ μ = c := by
  classical
  have hmon : f.charpoly.Monic := LinearMap.charpoly_monic f
  set F := f.charpoly.roots.toFinset with hFdef
  have hF : ∀ μ, f.maxGenEigenspace μ ≠ ⊥ → μ ∈ F := by
    intro μ hμ
    rw [Module.End.maxGenEigenspace_eq] at hμ
    have hev := Module.End.hasEigenvalue_of_hasGenEigenvalue hμ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at hev
    rw [hFdef, Multiset.mem_toFinset, mem_roots hmon.ne_zero]
    exact hev
  have htop' : F.sup f.maxGenEigenspace = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    by_cases h : f.maxGenEigenspace μ = ⊥
    · rw [h]; exact bot_le
    · exact Finset.le_sup (f := f.maxGenEigenspace) (hF μ h)
  have hcard : Multiset.card f.charpoly.roots = f.charpoly.natDegree := by
    rw [LinearMap.charpoly_natDegree]
    have h1 := Formalism.L2.NCov.finrank_finset_sup (f.independent_maxGenEigenspace) F
    rw [htop', finrank_top] at h1
    rw [h1]
    simp_rw [LinearMap.finrank_maxGenEigenspace_eq, ← count_roots]
    exact (Multiset.toFinset_sum_count_eq _).symm
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [← hprod, Polynomial.map_multiset_prod, Multiset.map_map, IsRoot, eval_multiset_prod,
    Multiset.map_map] at hc
  obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hc)
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C] at ha0
  refine ⟨a, ?_, (sub_eq_zero.1 ha0).symm⟩
  have hr : f.charpoly.IsRoot a := (mem_roots hmon.ne_zero).1 ha
  obtain ⟨x, hx⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f a).2 hr).exists_hasEigenvector
  intro hb
  apply hx.2
  have : x ∈ f.maxGenEigenspace a := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simpa [sub_eq_zero] using Module.End.mem_eigenspace_iff.1 hx.1⟩
  rw [hb] at this
  exact (Submodule.mem_bot _).1 this

theorem tN_lin (D : D7) (M : MtFam D) (HT : HeckeTied D M) (NL : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl}
    {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hvk : GenAt D (D.what₂.places.resChar w) (NL.B.Qc j w) v k) (hc : IsConjPl D.host v s.w)
    (hu : IsUnif D.host.E s.v ϖ) (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M.loc i).wt.W) :
    NG.tN (M.loc i).J s ϖ k (c • f + f') = c • NG.tN (M.loc i).J s ϖ k f + NG.tN (M.loc i).J s ϖ k f' := by
  have hbad : s.v ∉ badPl D i := genOutBad_of NL j w i h v k s hvk hc
  have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s ϖ k hbad hu
  simp only [NG.tN]
  rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]

theorem tC_exists (D : D7) (M : MtFam D) (B : NLocBase D M) (hstd : HeckeStdTw B) (j : ℕ)
    (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (hμ : μ = D.what₂.muTw w) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : LocPl D j w) (φ : FractionRing (B.Oc j w) →+* ℂ)
    (hφ : ∀ x, φ (B.ec j w x) = D.what₂.embLL x) (v : PlE D.host) (k : ℕ)
    (hvk : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) :
    ∃ tC : Module.End ℂ (D.what₂.Mt μ j),
      (∀ (c : ℂ) (y : D.what₂.Mt μ j), y ≠ 0 → tC y = c • y →
        ∃ κ : B.Oc j w, φ (algebraMap _ _ κ) = c) ∧
      ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        (∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W),
          NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') =
            c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') →
        ∀ y, NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) =
          (M μ j h1 h2).real (tC y) := by
  subst hμ
  classical
  obtain ⟨hfd, -⟩ := finrank_V B j w
  haveI := hfd
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  haveI : Module.Finite ℂ (D.what₂.Mt (D.what₂.muTw w) j) := Module.Finite.of_basis bC
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
    bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
  have hCpoly : tC.charpoly = (B.hL j w v k).charpoly.map D.what₂.embLL :=
    NCov.charpoly_transport_basis D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 _ _ fun a => by
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
      simp only [bC, Module.Basis.mk_apply] at e
      exact e
  have hb := B.iV_basis j w b
  have hKpoly : (B.hK j w v k).charpoly = (B.hL j w v k).charpoly.map (B.ec j w) :=
    NCov.charpoly_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 _ _ (fun x => B.hK_def j w v k x)
  refine ⟨tC, fun c y hy hty => ?_, fun s ϖ hc hu hadd => ?_⟩
  · have hroot : tC.charpoly.IsRoot c := by
      rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hty, hy⟩
    have hcomp : D.what₂.embLL = φ.comp (B.ec j w) := RingHom.ext fun x => (hφ x).symm
    rw [hCpoly, hcomp, ← Polynomial.map_map, ← hKpoly] at hroot
    obtain ⟨μ, hμ, hμc⟩ := root_map_eq (B.hK j w v k) (B.split j w v k hvk) φ c hroot
    obtain ⟨κ, hκ⟩ := (hstd j w h1 h2 hw).2 v k hvk μ hμ
    exact ⟨κ, by rw [hκ, hμc]⟩
  · set Mw := M (D.what₂.muTw w) j h1 h2 with hMw
    have htN0 : NG.tN Mw.J s ϖ k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := hadd 1 0 0
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := hadd 1 (Mw.real y) (Mw.real y')
          rw [one_smul, one_smul] at this
          simp only [map_add]
          exact this
        map_smul' := fun c y => by
          have := hadd c (Mw.real y) 0
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
      show NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
        Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
      rw [e, hbC a]
      exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
    intro y
    exact LinearMap.congr_fun hLt y

theorem ptV_of_transport {D : D7} {M : MtFam D} (A : AVTied D M) (i' : D.nd.Loc) (P' : D.naut.AV i')
    (x' : D.nd.X i') {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = D.nd.mu i') (hj : j = D.nd.j i') (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (V : Submodule ℂ (D.what₂.Mt μ j))
    (hV : V.map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ hj).toLinearMap = D.naut.typeV i' P')
    (hev : ∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i' w → IsConjPl D.host w s.w →
      IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V,
      NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) =
        iotaOC D i' ((D.nd.hT i' w k : D.nd.X i' → D.nd.O i') x') • (M μ j h1 h2).real y) :
    D.naut.ptV i' P' = some x' := by
  subst hμ; subst hj
  rw [GlobalTheory.EtaJoin.TypeSum.map_eqvMt_self] at hV
  subst hV
  exact (A.ptV i' P' x').2 hev

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i), thetaOf D.nd D.naut i σ P → ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ (P' : D.naut.AV i') (x' : D.nd.X i'), thetaOf D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  intro D M HT AV NL hstd i σ P hθ
  classical
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hj1 := (D.nd.j_range i).1
  have hj2 := (D.nd.j_range i).2
  have hw : LocPl D (D.nd.j i) (D.nd.w i) := locPl_of_mem D h
  have hμ : D.nd.mu i = D.what₂.muTw (D.nd.w i) := D.nd.mu_w i
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have hr0 : (M.loc i).real y0 ≠ 0 := fun h0 => hy0ne ((M.loc i).real_inj (h0.trans (map_zero _).symm))

  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK

  have HS := GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i
  have key : ∀ v k, GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k →
      ∃ κ : NL.B.Oc (D.nd.j i) (D.nd.w i), ∀ (s : SplitPlace D.host.E)
        (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = φ (algebraMap _ _ κ) • (M.loc i).real y := by
    intro v k hvk
    obtain ⟨hv, hk1, hk2⟩ := (genAt_iff NL h v k).2 hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    obtain ⟨c, hcP⟩ := HS P v k s ϖ hv hc hu hk1 hk2
    obtain ⟨tC, htC1, htC2⟩ := tC_exists D M NL.B hstd (D.nd.j i) (D.nd.w i) (D.nd.mu i) hμ hj1 hj2 hw φ hφ v k hvk
    have ht0 : tC y0 = c • y0 := by
      apply (M.loc i).real_inj
      have e0 := htC2 s ϖ hc hu (tN_lin D M HT NL h v k s ϖ hvk hc hu) y0
      change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e0
      rw [← e0, hcP y0 hy0, map_smul]
    obtain ⟨κ, hκ⟩ := htC1 c y0 hy0ne ht0
    refine ⟨κ, fun s' ϖ' hc' hu' y hy => ?_⟩
    obtain ⟨c', hcP'⟩ := HS P v k s' ϖ' hv hc' hu' hk1 hk2
    have e1 := htC2 s' ϖ' hc' hu' (tN_lin D M HT NL h v k s' ϖ' hvk hc' hu') y0
    change NG.tN (M.loc i).J s' ϖ' k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e1
    rw [hcP' y0 hy0, ht0, map_smul] at e1
    have hcc : c' = c := smul_left_injective ℂ hr0 e1
    rw [hcP' y hy, hcc, hκ]
  let κF : PlE D.host → ℕ → NL.B.Oc (D.nd.j i) (D.nd.w i) := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k then
      Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) =
          φ (algebraMap _ _ (κF v k)) • (M.loc i).real y := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)

  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) hj1 hj2 hμ φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, -, -⟩ := (genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
      exact ⟨s, ϖ, hc, hu, tN_lin D M HT NL h v k s ϖ hvk hc hu, hκF v k hvk s ϖ hc hu y0 hy0⟩)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hW : NCov.W (heckeAlg NL.B _ _) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3

  obtain ⟨i', hi', hmx⟩ := NL.mx_all (D.nd.j i) (D.nd.w i) hj1 hj2 (D.nd.w_tw i) (NCov.cls ψ)
    (NCov.cls_isMaximal ψ)
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hμ' : D.nd.mu i = D.nd.mu i' := by rw [D.nd.mu_w i, D.nd.mu_w i', e2]
  have hj' : D.nd.j i = D.nd.j i' := e1.symm
  let x' : D.nd.X i' := (NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩
  obtain ⟨P', hP'⟩ := GlobalTheory.EtaJoin.TypeSum.typeV_of_transport AV i' hμ' hj' hj1 hj2 (AV.S i P) (AV.irr i P)
    (by
      change (NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real ≠ ⊥
      rw [← AV.typeV i P]; exact D.naut.typeV_ne i P)
  change Submodule.map _ ((NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real) = _ at hP'
  rw [← AV.typeV i P] at hP'
  refine ⟨i', hi', P', x', ⟨?_, ?_⟩, ?_⟩
  · rw [← GlobalTheory.EtaJoin.TypeSum.map_eqvMt_thetaT_isot hμ' hj' σ]
    intro h0
    apply hθ.1
    apply Submodule.map_injective_of_injective (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ' hj').injective
    rw [h0, Submodule.map_bot]
  · rw [← GlobalTheory.EtaJoin.TypeSum.map_eqvMt_thetaT_isot hμ' hj' σ, ← hP']
    exact Submodule.map_mono hθ.2
  · refine ptV_of_transport AV i' P' x' hμ' hj' hj1 hj2 _ hP' ?_
    intro v k s ϖ hv' hc hu hk1 hk2 y hy
    have hvk := (genAt_iff NL hi' v k).1 ⟨hv', hk1, hk2⟩
    change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = _ • (M.loc i).real y
    rw [hκF v k hvk s ϖ hc hu y hy]
    congr 1
    rw [NL.iotaC_coh _ _ i' hi', NL.ptX_hT _ _ i' hi' x' v k hvk]
    show φ (algebraMap _ _ (κF v k)) = NL.iotaC _ _ (((NL.ptX _ _ i' hi') ((NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩)).1 _)
    rw [Equiv.apply_symm_apply, hφalg]
    show NL.iotaC _ _ (κF v k) = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
    rw [hψv v k hvk]

end GlobalTheory.LiftPoint
