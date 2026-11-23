import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrInjectiveLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteDvrIdealContractionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackStalkIsDomainEtaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupExtendsDvrPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleStalkBoundaryUnifStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkCompSpecMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MixedLower

set_option maxHeartbeats 1000000 in

theorem exists_trait_stalkIdeal_of_dimOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)), SABMap t X.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (k' : ℕ) (γ : Fin k' → LinearMap.BilinForm ℤ P.D.toPre.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X k' γ → InCone P.D.toPre γ → (∀ w : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), IsDomain ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk w) ∧ IsIntegrallyClosed ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk w) ∧ IsNoetherianRing ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk w)) → ∀ v : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), ringKrullDim ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) = 1 → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ϖ : W) (gv : (pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v →+* W) (B : LinearMap.BilinForm ℤ P.D.toPre.X), CDvr W ∧ Irreducible ϖ ∧ B ∈ balForms H.bar P.D.toPre.X ∧ FormAt P.D.toPre (gv.comp (((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.germ ⊤ v trivial).hom.comp ((pullback.fst ξ (e.hom ≫ genι Z ≫ π)).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) ϖ B ∧ ∀ a : (pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v, (∃ m : ℕ, ((n * d' : ℕ) : ℝ) * φ.evalZ B ≤ m ∧ ϖ ^ m ∣ gv a) → a ∈ FinalTheorems.stalkId (((BY.idealSheaf ^ n).comap (genι Y)).comap (pullback.snd ξ (e.hom ≫ genι Z ≫ π))) v := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn hN v hv
  obtain ⟨hOd, hOi, hOn⟩ := hN v
  have hc0 : CharZero ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) := by
    let f : c.F →+* (pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v :=
      ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.germ ⊤ v trivial).hom.comp
        ((pullback.snd ξ (e.hom ≫ genι Z ≫ π) ≫ genStr Y).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
    letI := f.toAlgebra
    exact charZero_of_injective_algebraMap f.injective
  obtain ⟨W, _, _, _, gv, hW, hginj, hgloc⟩ := GlobalTheory.T.exists_complete_dvr_injective_local _ hOi hOn hv hc0
  have hr := GlobalTheory.T.pullback_stalk_isDomain_etale E H D l Xo c X Z Y π e R ξ hEt v hOd W gv hginj
  obtain ⟨W', _, _, _, ι, tW, mY, PW, hW', hιinj, hιloc⟩ := GlobalTheory.T.exists_semiabelian_extension_dvr E H D l Xo c Y W hW _ hr
  haveI := hW'.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W'
  let g' := ι.comp gv
  have hg'inj : Function.Injective g' := hιinj.comp hginj
  haveI hg'loc : IsLocalHom g' := RingHom.isLocalHom_comp ι gv
  have hχ : spMap ι ≫ spMap gv ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π) ≫ genι Y
      = (spMap g' ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π)) ≫ genι Y := by
    simp only [g', spMap_comp, Category.assoc]
  have mY' := hχ ▸ mY
  have hr' := GlobalTheory.T.pullback_stalk_isDomain_etale E H D l Xo c X Z Y π e R ξ hEt v hOd W' g' hg'inj
  have hr'' : Set.range (jK W' ≫ (spMap g' ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π)) ≫ genι Y) ⊆ Set.range Y.j := by
    simpa only [Category.assoc] using hr'
  obtain ⟨be, hbe, hmon⟩ := GlobalTheory.MonPeriods.exists_isMonomial_levelOne hW' ϖ hϖ tW PW
  obtain ⟨m₀, hm₀, hid⟩ := hY W' hW' ϖ hϖ _ tW mY' PW hr'' be hbe hmon
  obtain ⟨⟨mX⟩, hrX⟩ := GlobalTheory.T.blowup_extends_dvr_point E H D l Xo c X Z Y BY π e J EX n hB W' hW' _ tW mY' hr''
  have hcomp : (spMap g' ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π)) ≫ e.hom ≫ genι Z ≫ π
      = spMap (g'.comp (((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.germ ⊤ v trivial).hom.comp ((pullback.fst ξ (e.hom ≫ genι Z ≫ π)).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) ≫ ξ := by
    have hL8 := GlobalTheory.T.fromSpecStalk_comp_spec_map _ R (pullback.fst ξ (e.hom ≫ genι Z ≫ π)) v
    rw [spMap_comp _ g', ← hL8]
    simp only [Category.assoc, pullback.condition]
  rw [hcomp] at mX hrX
  obtain ⟨eL, heL, hFA⟩ := GlobalTheory.T.etale_stalk_boundary_unif E H D l Xo c X R ξ t mξ P hCN hEt hFU hTI W' hW' ϖ hϖ _ tW mX PW hrX be hbe hmon
  refine ⟨W', inferInstance, inferInstance, inferInstance, ϖ, g', be.compl₁₂ eL.toAddMonoidHom.toIntLinearMap eL.toAddMonoidHom.toIntLinearMap, hW', hϖ, ⟨fun y z => ?_, fun a y z => ?_⟩, hFA, ?_⟩
  · exact hbe.1 _ _
  · simp only [LinearMap.compl₁₂_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, map_smul]
    exact hbe.2.1 a _ _
  · rintro a ⟨m, hm, hdvd⟩
    have hev : φ.evalZ (be.compl₁₂ eL.toAddMonoidHom.toIntLinearMap eL.toAddMonoidHom.toIntLinearMap) = φ.evalZ be :=
      φ.eval_comp heL (fun a b => (be a b : ℝ))
    have hm₀' : (m₀ : ℝ) = d' * φ.evalZ be := by
      rw [hm₀]
      simp only [InvFun.evalZ, InvFun.eval, comb]
      ring
    have hle : n * m₀ ≤ m := by
      have : ((n * m₀ : ℕ) : ℝ) ≤ m := by
        rw [hev] at hm
        push_cast at hm ⊢
        rw [hm₀']
        linarith
      exact_mod_cast this
    have hmem : g' a ∈ (FinalTheorems.stalkId (((BY.idealSheaf ^ n).comap (genι Y)).comap (pullback.snd ξ (e.hom ≫ genι Z ≫ π))) v).map g' := by
      rw [← GlobalTheory.T.ideal_along_stalk_point_eq_map _ _ _ _ g' hg'loc, idlAlong_comap, idlAlong_comap, idlAlong_pow]
      have e1 : ((spMap g' ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v) ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π)) ≫ genι Y
          = (spMap g' ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π)) ≫ genι Y := by
        simp only [Category.assoc]
      rw [e1, hid, Ideal.span_singleton_pow, ← pow_mul, Ideal.mem_span_singleton]
      exact (pow_dvd_pow ϖ (by rw [mul_comm]; exact hle)).trans hdvd
    exact GlobalTheory.T.complete_dvr_ideal_contraction _ hOi hOn hv W' hW' g' hg'inj hg'loc _ a hmem

end GlobalTheory.MixedLower
