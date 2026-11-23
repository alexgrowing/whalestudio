import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweThetaLiftComponents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.LiftPoint

noncomputable section

namespace GlobalTheory.ResLoc

theorem exists_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw NL.B)
    (i : D.nd.Loc) (P : D.naut.AV i) : ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      ∃ (hμ' : D.nd.mu i = D.nd.mu i') (hj' : D.nd.j i = D.nd.j i') (P' : D.naut.AV i') (x' : D.nd.X i'),
        (D.naut.typeV i P).map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ' hj').toLinearMap = D.naut.typeV i' P' ∧
        D.naut.ptV i' P' = some x' := by
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
  refine ⟨i', hi', hμ', hj', P', x', hP', ?_⟩
  refine ptV_of_transport AV i' P' x' hμ' hj' hj1 hj2 _ hP' ?_
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

theorem pairs_of_transport {D : D7} (i' : D.nd.Loc) (P' : D.naut.AV i') {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = D.nd.mu i')
    (hj : j = D.nd.j i') (V : Submodule ℂ (D.what₂.Mt μ j))
    (hV : V.map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ hj).toLinearMap = D.naut.typeV i' P') {σ : D.what₂.FT}
    (h : ∃ f ∈ D.what₂.isot j σ, ∃ F ∈ V, inner ℂ F (D.what₂.thetaT μ j f) ≠ 0) : GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' := by
  subst hμ; subst hj
  rw [GlobalTheory.EtaJoin.TypeSum.map_eqvMt_self] at hV
  subst hV
  exact h

theorem exists_pair_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M)
    (hstd : HeckeStdTw NL.B) (i : D.nd.Loc) (σ : D.what₂.FT)
    (h : ∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) :
    ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
      GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨f, hf, hθ⟩ := h
  obtain ⟨P, F, hF, hFf⟩ := GlobalTheory.Proof.HoweThetaLiftComponents.exists_inner_ne_zero (D.naut.typeV i) (D.naut.typeV_top i) _ hθ
  obtain ⟨i', hi', hμ, hj, P', x', hP', hx'⟩ := exists_point D M HT AV NL hstd i P
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  exact ⟨i', P', x', e1, e2, pairs_of_transport i' P' hμ hj _ hP' ⟨f, hf, F, hF, hFf⟩, hx'⟩

theorem exists_thetaT_ne {D : D7} (hd : DV.LamDef D) {μ : D.what₂.Tup} {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {σ : D.what₂.FT}
    (hσ : D.what₂.isot j σ ≠ ⊥) (hp : 0 < D.what₂.lamP μ j σ) : ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra hn
  push Not at hn
  rw [hd μ j h1 h2 σ hσ, DV.lamTr_of_scalar D μ j σ 0 hσ fun x hx => by rw [hn x hx]; simp] at hp
  exact lt_irrefl _ hp

end GlobalTheory.ResLoc

end
