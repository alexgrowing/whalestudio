import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullRatSec

theorem algebraMap_gs' {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (gs (𝟙 X) x U a) = fnOf U (gen_mem hx) a := by
  rw [gs_eq (𝟙 X) x U hx]
  exact algebraMap_germ hx a

theorem exists_glue_of_germ_eq {X Z : Scheme.{0}} (i : Z ⟶ X) (V : Z.Opens) (W : Z → X.Opens)
    (f : ∀ z, Γ(X, W z)) (hz : ∀ z ∈ V, i z ∈ W z) (hWV : ∀ z ∈ V, i ⁻¹ᵁ W z ≤ V)
    (hd : ∀ z₁ ∈ V, ∀ z₂ ∈ V, ∀ y : Z, ∀ (_ : i y ∈ W z₁) (_ : i y ∈ W z₂),
      gs (𝟙 X) (i y) (W z₁) (f z₁) = gs (𝟙 X) (i y) (W z₂) (f z₂)) :
    ∃ g : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V g = gs i z (W z) (f z) := by
  let O : V → Z.Opens := fun z => i ⁻¹ᵁ W z.1
  let a : ∀ z : V, Γ(Z, O z) := fun z => (i.app (W z.1)).hom (f z.1)
  have ga : ∀ (z : V) (y : Z) (hy : y ∈ O z), gs (𝟙 Z) y (O z) (a z) = gs i y (W z.1) (f z.1) := fun z y hy =>
    (gs_pull (𝟙 Z) i y _ hy _).trans (by rw [Category.id_comp])
  have hcov : V ≤ iSup O := fun z hzV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hzV⟩, hz z hzV⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.presheaf O a := by
    intro z₁ z₂
    apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext
    intro y hyO
    erw [gs_res (𝟙 Z) y inf_le_left hyO, gs_res (𝟙 Z) y inf_le_right hyO]
    rw [ga z₁ y hyO.1, ga z₂ y hyO.2, gs_stalkMap i y _ hyO.1, gs_stalkMap i y _ hyO.2,
      hd z₁.1 z₁.2 z₂.1 z₂.2 y hyO.1 hyO.2]
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' O V (fun z => homOfLE (hWV z.1 z.2)) hcov a hcomp
  refine ⟨g, fun z hzV => ?_⟩
  have hzO : z ∈ O ⟨z, hzV⟩ := hz z hzV
  rw [← gs_res (𝟙 Z) z (hWV z hzV) hzO g]
  erw [hg ⟨z, hzV⟩]
  exact ga _ z hzO

theorem exists_sec_pull : ∀ (X Z : Scheme.{0}) [IsIntegral X] (B : ReciprocityTheory.ChartRestriction.G.Semi.LB X), B.IsLB →
    ∀ (R : B.ι → X.functionFieldˣ), GlobalTheory.Cartier.IsRatSec B R → ∀ (f : X.functionField) (i : Z ⟶ X),
    (∀ (z : Z) (a : B.ι), i z ∈ B.U a → GlobalTheory.Cartier.RegAt (i z) (f * R a)) →
    ∃ s : (B.pull i).Sec, ∀ (z : Z) (a : B.ι), i z ∈ B.U a →
      (z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ GlobalTheory.Cartier.UnitAt (i z) (f * R a)) := by
  intro X Z _ B _ R hR f i hreg
  have hdata : ∀ (a : B.ι) (z : Z), ∃ (W : X.Opens) (g : Γ(X, W)), W ≤ B.U a ∧
      (i z ∈ B.U a → i z ∈ W) ∧ ∀ h, fnOf W h g = f * R a := by
    intro a z
    by_cases hz : i z ∈ B.U a
    · obtain ⟨W, hW, g, hg⟩ := (hreg z a hz).exists_fnOf
      refine ⟨W ⊓ B.U a, resG X inf_le_left g, inf_le_right, fun _ => ⟨hW, hz⟩, fun h => ?_⟩
      rw [fnOf_resG, hg]
    · exact ⟨⊥, 0, bot_le, fun h => (hz h).elim, fun h => absurd h (by simp)⟩
  choose W g hW hWz hg using hdata
  have hgs : ∀ (a : B.ι) (z₁ z₂ y : Z) (h₁ : i y ∈ W a z₁) (h₂ : i y ∈ W a z₂),
      gs (𝟙 X) (i y) (W a z₁) (g a z₁) = gs (𝟙 X) (i y) (W a z₂) (g a z₂) := by
    intro a z₁ z₂ y h₁ h₂
    apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
    rw [algebraMap_gs' h₁, algebraMap_gs' h₂, hg, hg]
  have hglue : ∀ (j : (B.pull i).ι), ∃ G : Γ(Z, (B.pull i).U j),
      ∀ z ∈ (B.pull i).U j, gs (𝟙 Z) z _ G = gs i z (W (j PUnit.unit) z) (g (j PUnit.unit) z) := by
    intro j
    exact exists_glue_of_germ_eq i _ (fun z => W (j PUnit.unit) z) (fun z => g (j PUnit.unit) z)
      (fun z hz => hWz _ _ (mem_pull.1 hz)) (fun z _ y hy => mem_pull.2 (hW _ _ hy))
      (fun z₁ _ z₂ _ y h₁ h₂ => hgs _ z₁ z₂ y h₁ h₂)
  choose G hG using hglue
  have hsec : ∀ (y : Z) (j j' : (B.pull i).ι), y ∈ (B.pull i).U j → y ∈ (B.pull i).U j' →
      gs (𝟙 Z) y _ (G j) =
        (gm (𝟙 Z) y ((B.pull i).U j ⊓ (B.pull i).U j') ((B.pull i).g j j')).val * gs (𝟙 Z) y _ (G j') := by
    intro y j j' hj hj'
    have ha := mem_pull.1 hj
    have ha' := mem_pull.1 hj'
    have hm : i y ∈ B.U (j PUnit.unit) ⊓ B.U (j' PUnit.unit) := ⟨ha, ha'⟩
    rw [hG j y hj, hG j' y hj', gm_pull_g B i (𝟙 Z) y j j' hj hj', Category.id_comp, ← gs_unit i y _ hm,
      gs_stalkMap i y _ (hWz _ _ ha), gs_stalkMap i y _ (hWz _ _ ha'), gs_stalkMap i y _ hm, ← map_mul]
    congr 1
    apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
    rw [map_mul, algebraMap_gs' (hWz _ _ ha), algebraMap_gs' hm, algebraMap_gs' (hWz _ _ ha'), hg, hg,
      hR _ _ (gen_mem hm)]
    ring
  refine ⟨LBGerm.secOfGerm G hsec, fun z a ha => ?_⟩
  have hz : z ∈ (B.pull i).U (fun _ => a) := mem_pull.2 ha
  rw [mem_nonzeroLocus_iff_isUnit _ hz]
  change IsUnit (gs (𝟙 Z) z _ (G (fun _ => a))) ↔ _
  rw [hG _ z hz, gs_stalkMap i z _ (hWz _ _ ha), isUnit_map_iff]
  refine ⟨fun hu => ⟨_, hu, by rw [algebraMap_gs' (hWz _ _ ha), hg]⟩, fun ⟨b, hb, e⟩ => ?_⟩
  have hb' : b = gs (𝟙 X) (i z) _ (g a z) :=
    IsFractionRing.injective _ X.functionField (by rw [e, algebraMap_gs' (hWz _ _ ha), hg])
  exact hb' ▸ hb

end GlobalTheory.PullRatSec
