import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrivOnZeroLocus

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]

theorem stalkMap_eq_zero (i : Z ⟶ X) (z : Z) (V : X.Opens) (hz : i z ∈ V) (f : X.functionField)
    (hV : ∀ z' : Z, i z' ∈ V → ¬ GlobalTheory.Cartier.UnitAt (i z') f) (c : X.presheaf.stalk (i z))
    (hc : algebraMap _ X.functionField c = f) : i.stalkMap z c = 0 := by
  have h : genericPoint Z ⤳ z := genericPoint_specializes z
  have h' : i (genericPoint Z) ⤳ i z := i.base.hom.map_specializes h
  have hη : i (genericPoint Z) ∈ V := h'.mem_open V.isOpen hz
  have hc' : algebraMap _ X.functionField (X.presheaf.stalkSpecializes h' c) = f := by
    rw [← hc]
    show (X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes h') c) =
      (X.presheaf.stalkSpecializes _) c
    rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
  have hnu : ¬ IsUnit (X.presheaf.stalkSpecializes h' c) := fun hu => hV _ hη ⟨_, hu, hc'⟩
  have hnu' : ¬ IsUnit (i.stalkMap (genericPoint Z) (X.presheaf.stalkSpecializes h' c)) :=
    fun hu => hnu (isUnit_of_map_unit _ _ hu)
  have h0 : i.stalkMap (genericPoint Z) (X.presheaf.stalkSpecializes h' c) = 0 := by
    by_contra hne
    exact hnu' (Ne.isUnit (G₀ := Z.functionField) hne)
  have e := Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) z h c
  apply GlobalTheory.PushInv.stalkSpecializes_injective h
  rw [map_zero, ← e]
  exact h0

theorem stalkMap_eq_of_congr (i : Z ⟶ X) (y : Z) (V : X.Opens) (hy : i y ∈ V) (f : X.functionField)
    (hV : ∀ z' : Z, i z' ∈ V → ¬ GlobalTheory.Cartier.UnitAt (i z') f) (hreg : GlobalTheory.Cartier.RegAt (i y) f)
    (hf0 : f ≠ 0) (g : X.functionField) (hg : GlobalTheory.Cartier.RegAt (i y) ((g - 1) / f))
    (ca cb : X.presheaf.stalk (i y))
    (h : algebraMap _ X.functionField ca = g * algebraMap _ X.functionField cb) :
    i.stalkMap y ca = i.stalkMap y cb := by
  obtain ⟨c, hc⟩ := hreg
  obtain ⟨d, hd⟩ := hg
  have e : ca = cb + cb * c * d := by
    apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
    rw [map_add, map_mul, map_mul, hc, hd, h, mul_assoc _ f, mul_div_cancel₀ _ hf0]
    ring
  rw [e, map_add, map_mul, map_mul, stalkMap_eq_zero i y V hy f hV c hc, mul_zero, zero_mul,
    add_zero]

theorem exists_glue (i : Z ⟶ X) (V : Z.Opens) {J : Type} (O : J → X.Opens) (u : ∀ a, Γ(X, O a)ˣ)
    (hcov : ∀ y ∈ V, ∃ a, i y ∈ O a)
    (hcomp : ∀ a b, ∀ y ∈ V, i y ∈ O a → i y ∈ O b → gm i y (O a) (u a) = gm i y (O b) (u b)) :
    ∃ s : Γ(Z, V)ˣ, ∀ a, ∀ y ∈ V, i y ∈ O a → gm (𝟙 Z) y V s = gm i y (O a) (u a) := by
  have key : ∀ a, ∀ y (h : y ∈ V ⊓ i ⁻¹ᵁ O a),
      gm (𝟙 Z) y (V ⊓ i ⁻¹ᵁ O a) (res inf_le_right (pullU i (O a) (u a))) = gm i y (O a) (u a) := by
    intro a y h
    rw [gm_res (𝟙 Z) y inf_le_right h, gm_pull (𝟙 Z) i y (O a) h.2, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V (fun a => V ⊓ i ⁻¹ᵁ O a) (fun a => inf_le_left)
    (fun y hy => by obtain ⟨a, ha⟩ := hcov y hy; exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)
    (fun a => res inf_le_right (pullU i (O a) (u a)))
    (fun a b y hy => by rw [key a y hy.1, key b y hy.2]; exact hcomp a b y hy.1.1 hy.1.2 hy.2.2)
  refine ⟨s, fun a y hy ha => ?_⟩
  rw [← gm_res (𝟙 Z) y (inf_le_left : V ⊓ i ⁻¹ᵁ O a ≤ V) ⟨hy, ha⟩, hs a, key a y ⟨hy, ha⟩]

end GlobalTheory.TrivOnZeroLocus

open GlobalTheory.TrivOnZeroLocus in

theorem GlobalTheory.TrivOnZeroLocus.cls_pull_eq_zero : ∀ (X : Scheme.{0}) [IsIntegral X] (k : Type) [CommRing k] (q : X ⟶ Sp k) (M : HermLB q)
    (r : M.B.ι → X.functionFieldˣ), (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField)) →
    ∀ (B : HermLB q) (ρ : B.B.ι → X.functionFieldˣ), IsRatSec B.B ρ → ∀ (ι : Type) (U : ι → X.Opens) (t : ι → X.functionFieldˣ),
    (∀ i, ∀ x ∈ M.B.U i, ¬ UnitAt x (r i : X.functionField) → (∃ a, x ∈ U a) ∧
      (∀ a j, x ∈ U a → x ∈ B.B.U j → UnitAt x ((t a : X.functionField) * ρ j)) ∧
      ∀ a b, x ∈ U a → x ∈ U b → RegAt x (((t a / t b : X.functionFieldˣ) - 1 : X.functionField) / r i)) →
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i],
      (∀ (z' : Z) j, i z' ∈ M.B.U j → ¬ UnitAt (i z') (r j : X.functionField)) →
      cls (B.B.pull i) (LB.isLB_pull B.isLB i) = 0 := by
  intro X _ k _ q M r hr B ρ hρ ι U t H Z _ i _ hZ
  have hpt : ∀ z : Z, ∃ kk, i z ∈ M.B.U kk := fun z => exists_chart M.isLB (i z)
  choose κ hκ using hpt
  have hκu : ∀ z : Z, ¬ UnitAt (i z) (r (κ z) : X.functionField) := fun z => hZ z _ (hκ z)
  choose α hα using fun z : Z => (H _ _ (hκ z) (hκu z)).1
  have hloc : ∀ (j : B.B.ι) (z : {z : Z // i z ∈ B.B.U j}), ∃ (O : X.Opens) (u : Γ(X, O)ˣ),
      i z.1 ∈ O ∧ O ≤ U (α z.1) ∧
        ∀ hO, GlobalTheory.Cartier.fnOf O hO u = (t (α z.1) : X.functionField) * ρ j := by
    rintro j ⟨z, hz⟩
    obtain ⟨W, hW, hWu⟩ := ((H _ _ (hκ z) (hκu z)).2.1 (α z) j (hα z) hz).exists_nhds
    obtain ⟨u, hu⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq (U := W ⊓ U (α z)) fun x hx => hWu x hx.1
    exact ⟨_, u, ⟨hW, hα z⟩, inf_le_right, hu⟩
  choose O u hOm hOle hOu using hloc
  have hcomp : ∀ (j : B.B.ι) (a b : {z : Z // i z ∈ B.B.U j}) (y : Z), i y ∈ O j a → i y ∈ O j b →
      gm i y (O j a) (u j a) = gm i y (O j b) (u j b) := by
    intro j a b y ha hb
    apply Units.ext
    rw [gm_val i y _ ha, gm_val i y _ hb, ← Scheme.Hom.germ_stalkMap_apply,
      ← Scheme.Hom.germ_stalkMap_apply]
    have hy := H _ _ (hκ y) (hκu y)
    refine stalkMap_eq_of_congr i y (M.B.U (κ y)) (hκ y) _ (fun z' hz' => hZ z' _ hz')
      (hr _ _ (hκ y)) (r (κ y)).ne_zero _ (hy.2.2 (α a.1) (α b.1) (hOle j a ha) (hOle j b hb)) _ _ ?_
    rw [GlobalTheory.Cartier.algebraMap_germ, GlobalTheory.Cartier.algebraMap_germ, hOu, hOu, Units.val_div_eq_div_val,
      ← mul_assoc, div_mul_cancel₀ _ (Units.ne_zero _)]
  have hglue : ∀ P : (B.B.pull i).ι, ∃ s : Γ(Z, (B.B.pull i).U P)ˣ, ∀ a, ∀ y ∈ (B.B.pull i).U P,
      i y ∈ O (P PUnit.unit) a → gm (𝟙 Z) y _ s = gm i y (O (P PUnit.unit) a) (u (P PUnit.unit) a) :=
    fun P => exists_glue i _ (O (P PUnit.unit)) (u (P PUnit.unit))
      (fun y hy => ⟨⟨y, mem_pull.1 hy⟩, hOm _ _⟩) (fun a b y _ => hcomp _ a b y)
  choose s hs using hglue
  refine (cls_eq_zero_iff _).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y P Q hP hQ => ?_⟩
  have hp := mem_pull.1 hP
  have hq := mem_pull.1 hQ
  have hg : gm (𝟙 Z) y ((B.B.pull i).U P ⊓ (B.B.pull i).U Q) ((B.B.pull i).g P Q) =
      gm i y _ (B.B.g (P PUnit.unit) (Q PUnit.unit)) := by
    show gm (𝟙 Z) y _ (∏ _k : PUnit, (res _ (pullU i _ (B.B.g _ _))) ^ (1 : ℤ)) = _
    have hm : (𝟙 Z) y ∈ (B.B.pull i).U P ⊓ (B.B.pull i).U Q := ⟨hP, hQ⟩
    have hm' : i ((𝟙 Z) y) ∈ B.B.U (P PUnit.unit) ⊓ B.B.U (Q PUnit.unit) := ⟨hp, hq⟩
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 Z) y _ hm _).trans ((gm_pull (𝟙 Z) i y _ hm' _).trans ?_)
    rw [Category.id_comp]
  show gm (𝟙 Z) y _ (s P) = gm (𝟙 Z) y _ ((B.B.pull i).g P Q) * gm (𝟙 Z) y _ (s Q)
  rw [hs P ⟨y, hp⟩ y hP (hOm _ _), hs Q ⟨y, hq⟩ y hQ (hOm _ _), hg]
  apply Units.ext
  rw [Units.val_mul, gm_val i y _ (hOm _ _), gm_val i y _ (show i y ∈ B.B.U (P PUnit.unit) ⊓ B.B.U (Q PUnit.unit) from ⟨hp, hq⟩), gm_val i y _ (hOm _ _),
    ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply,
    ← Scheme.Hom.germ_stalkMap_apply, ← map_mul]
  congr 1
  apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
  rw [map_mul, GlobalTheory.Cartier.algebraMap_germ, GlobalTheory.Cartier.algebraMap_germ, GlobalTheory.Cartier.algebraMap_germ,
    hOu, hOu, hρ _ _ (GlobalTheory.Cartier.gen_mem ⟨hp, hq⟩)]
  ring
