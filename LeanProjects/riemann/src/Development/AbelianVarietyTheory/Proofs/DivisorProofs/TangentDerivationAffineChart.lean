import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSPkg

open GlobalTheory.DeRham GlobalTheory.Cris

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem ksPackage : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  intro PP E _ _ _ H Dw l Xo c TF U δ K _ _ P hU y' hU' hs hev
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ y' = frX P := by
    apply GlobalTheory.FlagMod.xF_ext (Y := TF.Y)
    · rw [Category.assoc, hs, spMap_comp_spMap]
      congr 1
    · exact GlobalTheory.FlagMod.frX_snd P
    · have h1 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ (y' ≫ TF.Y.j)) ⁻¹ᵁ U.1 :=
        GlobalTheory.FlagMod.le_preimage_comp _ hU'
      rw [Category.assoc, ← GlobalTheory.FlagMod.spMap_ev _ U.2 h1, ← GlobalTheory.FlagMod.spMap_ev _ U.2 hU,
        GlobalTheory.FlagMod.ev_spMap _ _ _ hU' h1]
      refine congrArg (fun f => spMap f ≫ (U.2 : IsAffineOpen U.1).fromSpec) ?_
      ext r
      rw [RingHom.comp_apply, hev r]
      simp [GlobalTheory.FlagTan.red]
  have hx : GlobalTheory.FlagTan.IsTanX P (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp_spMap]
      rfl
    · rw [← Category.assoc, hred, GlobalTheory.FlagMod.frX_fst]
  have P5 := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G (y' ≫ pullback.fst _ _)
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G P.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hUn := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P5 Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P5 Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P5 hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback P hπ a ha
  have hL := (P5.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P5 P hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))),
      ∃ w, GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ => by
    obtain ⟨_, w, -, hw⟩ := GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, GlobalTheory.KSExist.conj_embK]) a₀
    exact ⟨w, hw⟩
  exact ⟨A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub, hb, _, hπ, hπ', rfl, hpol, hu,
    fun σ k => hbl ⟨σ, k⟩, hrow, hA, gA, hA', gA', LB.isLB_pull Xo.univ.t.PP.isLB _⟩

end GlobalTheory.KSPkg
