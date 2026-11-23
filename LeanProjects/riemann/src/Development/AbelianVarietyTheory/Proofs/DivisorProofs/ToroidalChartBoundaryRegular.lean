import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ArchLim

theorem valR_app_eq {A : Type} [CommRing A] {X X' : Scheme.{0}} (z : Sp A ⟶ X) (g : X ⟶ X') (U : X'.Opens)
    (f : Γ(X', U)) : valR z (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (z ≫ g) U f := by
  unfold valR
  by_cases h : ⊤ ≤ z ⁻¹ᵁ g ⁻¹ᵁ U
  · have h' : ⊤ ≤ (z ≫ g) ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    have e := Scheme.Hom.appLE_comp_appLE z g U (g ⁻¹ᵁ U) ⊤ le_rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (q.hom f)) e
  · have h' : ¬ ⊤ ≤ (z ≫ g) ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

theorem differentiableOn_ev_up : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (σ : c.F →+* ℂ) (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 c.F)) (jm : Y ⟶ Z.X) (hq : jm ≫ Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 c.F) c.F)) n) (W : (gen Z).Opens) (f : Γ(gen Z, W)), DifferentiableOn ℂ (ev (genStr Z) σ W f ∘ up jm hq σ ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' ptsIn (genStr Z) σ W)) := by
  intro E _ _ _ H Dw l Xo c Z σ Y q jm hq n ch W f v hv
  set y := ch.e.symm v with hy
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show jm (y.1 (IsLocalRing.closedPoint ℂ)) ∈ (⊤ : Z.X.Opens) from trivial)
  have : IsAffineHom (genι Z) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback Z.s (spMap (algebraMap (𝓞 c.F) c.F))).flip inferInstance
  have hU : IsAffineOpen (genι Z ⁻¹ᵁ V) := hV.preimage (genι Z)
  have key_mem : ∀ y' : CxPts q (σ.comp (algebraMap (𝓞 c.F) c.F)),
      up jm hq σ y' ∈ ptsIn (genStr Z) σ (genι Z ⁻¹ᵁ V) ↔ y' ∈ ptsIn q (σ.comp (algebraMap (𝓞 c.F) c.F)) (jm ⁻¹ᵁ V) := by
    intro y'
    rw [mem_ptsIn, mem_ptsIn]
    have e : genι Z ((up jm hq σ y').1 (IsLocalRing.closedPoint ℂ)) = jm (y'.1 (IsLocalRing.closedPoint ℂ)) :=
      congrArg (fun g : Sp ℂ ⟶ Z.X => g (IsLocalRing.closedPoint ℂ)) (up_ι jm hq σ y')
    change genι Z _ ∈ V ↔ jm _ ∈ V
    rw [e]
  have hev : ∀ (y' : CxPts q (σ.comp (algebraMap (𝓞 c.F) c.F))) (x : Γ(Z.X, V)),
      ev (genStr Z) σ (genι Z ⁻¹ᵁ V) (((genι Z).app V).hom x) (up jm hq σ y') =
        ev q (σ.comp (algebraMap (𝓞 c.F) c.F)) (jm ⁻¹ᵁ V) ((jm.app V).hom x) y' := by
    intro y' x
    change valR (up jm hq σ y').1 _ _ = valR y'.1 _ _
    rw [valR_app_eq, valR_app_eq, up_ι]

  let := ((genι Z).app V).hom.toAlgebra
  have hloc := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := CommRingCat.of (𝓞 c.F)) (L := CommRingCat.of c.F)
    (nonZeroDivisors (𝓞 c.F)) (IsPullback.of_hasPullback Z.s (spMap (algebraMap (𝓞 c.F) c.F))) hV
  set T := ch.e.target ∩ ch.e.symm ⁻¹' ptsIn q (σ.comp (algebraMap (𝓞 c.F) c.F)) (jm ⁻¹ᵁ V) with hT
  have hTo : IsOpen T := ch.e.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hs : ∀ w ∈ T, (up jm hq σ ∘ ch.e.symm) w ∈ ptsIn (genStr Z) σ (genι Z ⁻¹ᵁ V) :=
    fun w hw => (key_mem _).2 hw.2
  have hd : ∀ a : Γ(gen Z, genι Z ⁻¹ᵁ V),
      DifferentiableOn ℂ (ev (genStr Z) σ (genι Z ⁻¹ᵁ V) a ∘ (up jm hq σ ∘ ch.e.symm)) T := by
    intro a
    obtain ⟨⟨r, ⟨m, hm⟩⟩, hr⟩ := IsLocalization.surj (S := Γ(gen Z, genι Z ⁻¹ᵁ V))
      ((nonZeroDivisors (𝓞 c.F)).map (GlobalTheory.QCoh.Qcqs.baseRingHom Z.s V).hom) a
    obtain ⟨b, hb, rfl⟩ := hm
    simp only [RingHom.algebraMap_toAlgebra] at hr
    have hb0 : σ (algebraMap (𝓞 c.F) c.F b) ≠ 0 :=
      (map_ne_zero σ).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
    refine (((ch.holo (jm ⁻¹ᵁ V) ((jm.app V).hom r)).mono fun w hw => hw).mul_const
      (σ (algebraMap (𝓞 c.F) c.F b))⁻¹).congr fun w hw => ?_
    have hw' : up jm hq σ (ch.e.symm w) ∈ ptsIn (genStr Z) σ (genι Z ⁻¹ᵁ V) := (key_mem _).2 hw.2
    have e := congrArg (fun t => ev (genStr Z) σ (genι Z ⁻¹ᵁ V) t (up jm hq σ (ch.e.symm w))) hr
    simp only [ev_mul, hev] at e
    have eb : (jm.app V).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom Z.s V).hom b) =
        algX q (jm ⁻¹ᵁ V) b := by
      rw [GlobalTheory.QCoh.Qcqs.app_baseRingHom, hq]
      rfl
    rw [eb, ev_algX hw.2] at e
    simp only [Function.comp_apply, RingHom.comp_apply] at e ⊢
    rw [← e, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  obtain ⟨-, hh⟩ := holo_of_affine hU hTo hs hd
  have hyV : y ∈ ptsIn q (σ.comp (algebraMap (𝓞 c.F) c.F)) (jm ⁻¹ᵁ V) := mem_ptsIn.2 hxV
  have hO : IsOpen (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn q (σ.comp (algebraMap (𝓞 c.F) c.F)) (jm ⁻¹ᵁ V) ∩
      up jm hq σ ⁻¹' ptsIn (genStr Z) σ W)) :=
    ch.e.isOpen_inter_preimage_symm ((isOpen_ptsIn _).inter ((isOpen_ptsIn W).preimage (continuous_up jm hq σ)))
  exact (((hh W f).mono fun w hw => ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩).differentiableAt
    (hO.mem_nhds ⟨hv.1, hyV, hv.2⟩)).differentiableWithinAt

end GlobalTheory.ArchLim
