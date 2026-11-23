import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem valAt_alg {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

private theorem valAt_ne {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] {y : Sp K ⟶ Z}
    {f : Z.functionField} (hf : UnitAt (below y) f) : TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_alg]
  exact (ha.map _).ne_zero

private theorem valAt_mul' {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] {y : Sp K ⟶ Z}
    {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_alg, valAt_alg, valAt_alg, map_mul]

private theorem isRatSec_of_isSecOf {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {B : Vert.Model O} (P : VertDiv B) (t : P.M.ι → B.X.functionFieldˣ) (h : IsSecOf P t) : IsRatSec P.M t := by
  intro i j hg
  have hi : genericPoint B.X ∈ B.gen ⊓ P.M.U i := ⟨B.genericPoint_mem_gen, hg.1⟩
  have hj : genericPoint B.X ∈ B.gen ⊓ P.M.U j := ⟨B.genericPoint_mem_gen, hg.2⟩
  have hW : genericPoint B.X ∈ B.gen ⊓ (P.M.U i ⊓ P.M.U j) := ⟨B.genericPoint_mem_gen, hg⟩
  have := congrArg (fnOf _ hW) (GlobalTheory.LB.coord_rel P.t i j (inf_le_inf_left _ inf_le_left)
    (inf_le_inf_left _ inf_le_right) inf_le_right)
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at this
  rw [h i hi, h j hj]
  exact this

theorem UpperTheory.generic_iso_sections_log :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (b : 𝓞 F →+* O) (Z : NModel O) (C : Z.Comp) (μ : Match Y b (Z.comp C)) (v : HeightOneSpectrum (𝓞 F)) (L L' : LB Z.X) (hL : L.IsLB) (hL' : L'.IsLB) (u : Z.GenIso L L') (s : (L.pull (Z.compι C)).ι → (Z.comp C).X.functionFieldˣ) (s' : (L'.pull (Z.compι C)).ι → (Z.comp C).X.functionFieldˣ) (l l' : Ext v → AlgPt Y → ℝ), Reads μ v (L.pull (Z.compι C)) s l → Reads μ v (L'.pull (Z.compι C)) s' l' → (∀ (i : L.ι) (j : L'.ι) (h : genericPoint (Z.comp C).X ∈ Z.compι C ⁻¹ᵁ (Z.gen ⊓ (L.U i ⊓ L'.U j))), fnOf _ h ((Z.compι C).app _ (u.u i j).val) = (s (fun _ => i) : (Z.comp C).X.functionField) / (s' (fun _ => j) : (Z.comp C).X.functionField)) → ∃ (P : VertDiv (Z.comp C)) (t : P.M.ι → (Z.comp C).X.functionFieldˣ), P.cls = Z.vRes C (u.div hL hL') ∧ IsSecOf P t ∧ Reads μ v P.M t (fun e y => l e y - l' e y) := by
  intro F _ _ Y O _ _ _ b Z C μ v L L' hL hL' u s s' l l' hs hs' hu
  obtain ⟨-, W, hW, hs⟩ := hs
  obtain ⟨-, W', hW', hs'⟩ := hs'
  have hsec : IsSecOf ((u.pair hL hL').pull (Z.compι_str C))
      (fun q => s (fun _ => (q ⟨⟩).1) / s' (fun _ => (q ⟨⟩).2)) := by
    intro q h
    have e : (Z.comp C).gen ⊓ ((u.pair hL hL').pull (Z.compι_str C)).M.U q ≤
        Z.compι C ⁻¹ᵁ (Z.gen ⊓ (L.U (q ⟨⟩).1 ⊓ L'.U (q ⟨⟩).2)) :=
      inf_le_inf (NModel.preimage_gen (Z.compι_str C)).ge (GlobalTheory.LB.pull_U_le _ q)
    have h1 := NModel.VPair.eqn_pull (u.pair hL hL') (Z.compι_str C) q le_rfl le_rfl e
    have h2 := congrArg (fnOf _ h) h1
    refine Eq.trans ?_ (h2.symm.trans (fnOf_resG _ h _))
    refine (Units.val_div_eq_div_val _ _).trans ((hu _ _ (e h)).symm.trans ?_)
    refine (fnOf_resG e h _).symm.trans (congrArg _ ?_)
    exact congrArg (fun a => resG _ e ((Z.compι C).app _ a)) (GlobalTheory.LB.resG_self _ _).symm
  refine ⟨(u.pair hL hL').pull (Z.compι_str C), _, rfl, hsec, isRatSec_of_isSecOf _ _ hsec, W ⊓ W', ⟨hW, hW'⟩, ?_⟩
  intro e y z zt q hy hz hzt hq
  have hq' (x) : Z.compι C (zt x) ∈ L.U (q ⟨⟩).1 ⊓ L'.U (q ⟨⟩).2 := GlobalTheory.LB.pull_U_le _ q (hq (x := x) trivial)
  obtain ⟨a1, a2⟩ := hs e y z zt (fun _ => (q ⟨⟩).1) hy.1 hz hzt fun x _ => mem_pull.2 (hq' x).1
  obtain ⟨b1, b2⟩ := hs' e y z zt (fun _ => (q ⟨⟩).2) hy.2 hz hzt fun x _ => mem_pull.2 (hq' x).2
  simp only [Units.val_div_eq_div_val]
  have c : UnitAt _ _ := a1.mul b1.inv
  rw [← div_eq_mul_inv] at c
  refine ⟨c, ?_⟩
  have d := valAt_mul' c.regAt b1.regAt
  rw [div_mul_cancel₀ _ b1.ne_zero] at d
  rw [← a2, ← b2, d, map_mul, Real.log_mul (by simpa using valAt_ne c) (by simpa using valAt_ne b1)]
  ring
