import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov

theorem exists_isFrame_of_isUnit_evalPt_det {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U : X.Opens}
    {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (g : Fin r → Γ(M, U)) {K : Type} [CommRing K] (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (h : IsUnit (TangentOrigin.evalPt x U hx ((hf.basis le_rfl).det g))) :
    ∃ (V : X.Opens) (hV : V ≤ U), ⊤ ≤ x ⁻¹ᵁ V ∧ VB.IsFrame fun i => Twist.resM M hV (g i) := by
  refine ⟨X.basicOpen ((hf.basis le_rfl).det g), X.basicOpen_le _, ?_, ?_⟩
  · have h1 : IsUnit (x.appLE U ⊤ hx ((hf.basis le_rfl).det g)) := by
      have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      have e : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (TangentOrigin.evalPt x U hx ((hf.basis le_rfl).det g)) =
          x.appLE U ⊤ hx ((hf.basis le_rfl).det g) := Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) _
      rwa [e] at this
    have h2 := Scheme.basicOpen_appLE x ⊤ U hx ((hf.basis le_rfl).det g)
    rw [Scheme.basicOpen_of_isUnit _ h1] at h2
    exact h2.le.trans inf_le_right
  · refine VB.isFrame_iff.2 fun W hW => ?_
    have h0 : IsUnit (resG X (X.basicOpen_le ((hf.basis le_rfl).det g)) ((hf.basis le_rfl).det g)) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace _
    have h1 := h0.map (resG X hW)
    rw [LB.resG_resG, hf.resG_det] at h1
    have h2 := (Module.Basis.is_basis_iff_det _).2 h1
    simp only [Twist.resM_resM]
    exact ⟨h2.1, h2.2.ge⟩

theorem isUnit_det_of_isEigBasis {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] {φ : c.F →+* K}
    {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ} {v v' : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)}
    (hv : IsEigBasis Z φ x τ v) (hv' : IsEigBasis Z φ x τ v') (A : Matrix (Fin r) (Fin r) K)
    (hA : ∀ i, IsCombAtG Z.t x v' (fun a => A a i) (v i)) : IsUnit A.det := by
  choose b hb using fun j => (hv.2 _ (hv'.1 j)).exists
  have e : A * Matrix.of (fun i j => b j i) = 1 := by
    ext a j
    have h1 := isCombAtG_mul Z.t x (fun i => (hv'.1 i).1) (fun i => (hv.1 i).1) (hv'.1 j).1 A (b j) hA (hb j)
    have h2 := isCombAtG_single Z.t x (fun i => (hv'.1 i).1) j
    have h3 := congrFun ((hv'.2 _ (hv'.1 j)).unique h1 h2) a
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Pi.single_apply] using h3
  exact Matrix.isUnit_det_of_right_inverse e

theorem isFrame_pullback_map {X Y : Scheme.{0}} (π : Y ⟶ X) {M M' : X.Modules} [M'.IsQuasicoherent] (u : M ⟶ M')
    {r : ℕ} {U : X.Opens} {f : Fin r → Γ(M, U)} (h : VB.IsFrame fun i => u.app U (f i)) :
    VB.IsFrame fun i => ((Scheme.Modules.pullback π).map u).app (π ⁻¹ᵁ U)
      (QCoh.pullbackSections π M (le_refl (π ⁻¹ᵁ U)) (f i)) := by
  simp only [QCoh.pullback_map_app_pullbackSections]
  exact h.pullback π

theorem isIso_pullback_of_matches : ∀ (D : D7) (O : Setup D) (B : Scheme.{0}) (q : B ⟶ Sp (𝓞 D.what₂.LL)) (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z),
    IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
    ∀ (σ : D.host.E →+* ℂ) (M M' : B.Modules), IsVB M (O.S.Dw.mult σ) → IsVB M' (O.S.Dw.mult σ) →
    ∀ (u : M ⟶ M') (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) (t' : FrAssign O.s.T.Z M' (O.S.Dw.mult σ) jB),
    IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t → IsLieFrames O.s.T.Z O.κ.e jB πB M' _ σ false t' →
    Matches O.s.T.Z jB πB u t t' →
    ∀ (Y Gs : Scheme.{0}) (π : Y ⟶ B) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp D.what₂.LL),
      jY ≫ π ≫ q = s ≫ spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) →
      IsIso ((Scheme.Modules.pullback jY).map ((Scheme.Modules.pullback π).map u)) := by
  intro D O B q Bg jB πB hW σ M M' hM hM' u t t' ht ht' hm Y Gs π jY s hs
  haveI := hM.isQuasicoherent
  haveI := hM'.isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  haveI := (hM'.pullback π).isQuasicoherent
  refine VB.isIso_of_frames (ι := Fin (O.S.Dw.mult σ)) _ fun y => ?_
  obtain ⟨K, _, x₀, hx₀⟩ : ∃ (K : Type) (_ : Field K) (x₀ : Sp K ⟶ Gs), ∀ z, x₀ z = y :=
    ⟨Gs.residueField y, inferInstance, Gs.fromSpecResidueField y, Scheme.fromSpecResidueField_apply y⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : D.what₂.LL →+* K, spMap ψ = x₀ ≫ s := ⟨(Spec.preimage (x₀ ≫ s)).hom, Spec.map_preimage _⟩
  have w : (x₀ ≫ jY ≫ π) ≫ q = spMap ψ ≫ spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
    rw [hψ, Category.assoc, Category.assoc, hs, Category.assoc]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : Sp K ⟶ Bg, x ≫ jB = x₀ ≫ jY ≫ π ∧
      x ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = spMap ψ :=
    ⟨hW.lift _ (spMap ψ) w, hW.lift_fst _ _ _, hW.lift_snd _ _ _⟩
  have hpt : ∀ z, (x ≫ jB) z = π (jY y) := fun z => by
    rw [hx₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx₀]
  obtain ⟨U₀, f₀, hb₀, hf₀⟩ := hM (π (jY y))
  obtain ⟨U, f', -, hb, hle, hf'⟩ := hM'.exists_affine hb₀
  have hf := hf₀.res hle
  have hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U := fun z _ => show (x ≫ jB) z ∈ U from hpt z ▸ hb
  have hd := isUnit_det_of_isEigBasis O.s.T.Z (ht.1 U _ hf K x hx ψ hx₂) (ht'.1 U _ hf' K x hx ψ hx₂)
    (Matrix.of fun a i => TangentOrigin.evalPt (x ≫ jB) U hx ((hf'.basis le_rfl).repr
      (Twist.resM M' le_rfl (u.app U (Twist.resM M hle (f₀ i)))) a)) (hm U _ f' hf hf' K x hx)
  obtain ⟨V, hV, hxV, hg⟩ := exists_isFrame_of_isUnit_evalPt_det hf'
    (fun i => Twist.resM M' le_rfl (u.app U (Twist.resM M hle (f₀ i)))) (x ≫ jB) hx (by
      rw [Module.Basis.det_apply, RingHom.map_det]
      exact hd)
  have hyV : π (jY y) ∈ V := by
    have := hxV (show IsLocalRing.closedPoint K ∈ (⊤ : (Sp K).Opens) from trivial)
    exact hpt _ ▸ this
  have hg' : VB.IsFrame fun i => u.app V (Twist.resM M hV (Twist.resM M hle (f₀ i))) := by
    simpa only [Twist.resM_self, Twist.app_resM] using hg
  exact ⟨jY ⁻¹ᵁ (π ⁻¹ᵁ V), _, hyV, ((hf.res hV).pullback π).pullback jY,
    isFrame_pullback_map jY _ (isFrame_pullback_map π u hg')⟩

end GlobalTheory.PairCov

end
