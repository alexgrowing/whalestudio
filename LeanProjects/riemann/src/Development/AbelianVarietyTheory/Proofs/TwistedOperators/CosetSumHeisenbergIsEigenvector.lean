import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetEigen

theorem heisO_lincomb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) :
    heisO ψ S T y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • heisO ψ S T y (f i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cosetSum_eigen : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  intro D ψ S T ΛS ΛT P e he Λd R x hR h2 h3 h4 g hg y hy hyd
  classical
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm]; exact he.2
  have half_add : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a + b) :=
    fun ha hb i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  have half_neg : ∀ {a : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) (-a) :=
    fun ha i j => by rw [Matrix.neg_apply, mul_neg, ha i j]
  have half_sub : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a - b) :=
    fun ha hb => by rw [sub_eq_add_neg]; exact half_add ha (half_neg hb)
  have ann_add : ∀ {a b : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → (∀ u ∈ Λd, ψ (symplO S T u b) = 1) →
      ∀ u ∈ Λd, ψ (symplO S T u (a + b)) = 1 :=
    fun ha hb u hu => by rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  have ann_neg : ∀ {a : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → ∀ u ∈ Λd, ψ (symplO S T u (-a)) = 1 :=
    fun ha u hu => by rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, ha u hu, inv_one]
  choose! f hfR hfΛ using h2
  have hyz : ∀ z ∈ R, IsHalf (cA D e) (y + z) ∧ ∀ u ∈ Λd, ψ (symplO S T u (y + z)) = 1 := fun z hz =>
    ⟨half_add hy (hR z hz).1, ann_add hyd (hR z hz).2⟩
  have hzy : ∀ z ∈ R, IsHalf (cA D e) (z + -y) ∧ ∀ u ∈ Λd, ψ (symplO S T u (z + -y)) = 1 := fun z hz =>
    ⟨half_add (hR z hz).1 (half_neg hy), ann_add (hR z hz).2 (ann_neg hyd)⟩
  have hfix : ∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a →
      heisO ψ S T a g = g := fun a ha hh =>
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he a ha (Or.inr hh)
  have key : ∀ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T y (heisO ψ S T z g) =
      ψ (symplO S T x y) • (ψ (-symplO S T x (f (y + z))) • heisO ψ S T (f (y + z)) g) := by
    intro z hz
    obtain ⟨hh, ha⟩ := hyz z hz
    have hσR := hfR _ hh ha
    have ha0 := hfΛ _ hh ha
    generalize f (y + z) = s at hσR ha0 ⊢
    have hσh := (hR _ hσR).1
    have ha0h : IsHalf (cA D e) (y + z - s) := half_sub hh hσh
    have e1 : heisO ψ S T y (heisO ψ S T z g) = heisO ψ S T s g := by
      rw [← Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hy (hR z hz).1)]
      have hsplit : y + z = s + (y + z - s) := by abel
      rw [hsplit, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hσh ha0h), hfix _ ha0 ha0h]
    have hlin : symplO S T x y + symplO S T x z = symplO S T x s + symplO S T x (y + z - s) := by
      rw [← Formalism.IndefR.Fin.symplO_add_right, ← Formalism.IndefR.Fin.symplO_add_right]
      congr 1; abel
    have hph : -symplO S T x z = symplO S T x y + -symplO S T x s + -symplO S T x (y + z - s) := by
      linear_combination (-1 : AF D.host.F) * hlin
    rw [e1, hph, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv ψ (symplO S T x (y + z - s)),
      h4 _ ha0 ha0h, inv_one, mul_one, smul_smul]
  rw [heisO_lincomb, Finset.sum_congr rfl key, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun z => f (y + z)) (fun z => f (z + -y)) (fun z hz => hfR _ (hyz z hz).1 (hyz z hz).2)
    (fun z hz => hfR _ (hzy z hz).1 (hzy z hz).2) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl)
  · have hs := hfR _ (hyz z hz).1 (hyz z hz).2
    have h1 := hfΛ _ (hyz z hz).1 (hyz z hz).2
    have h2' := hfΛ _ (hzy _ hs).1 (hzy _ hs).2
    have ht := hfR _ (hzy _ hs).1 (hzy _ hs).2
    have hsum := add_mem h1 h2'
    have heq : y + z - f (y + z) + (f (y + z) + -y - f (f (y + z) + -y)) = z - f (f (y + z) + -y) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ ht hsum).symm
  · have ht := hfR _ (hzy z hz).1 (hzy z hz).2
    have h1 := hfΛ _ (hzy z hz).1 (hzy z hz).2
    have h2' := hfΛ _ (hyz _ ht).1 (hyz _ ht).2
    have hs := hfR _ (hyz _ ht).1 (hyz _ ht).2
    have hsum := add_mem h1 h2'
    have heq : z + -y - f (z + -y) + (y + f (z + -y) - f (y + f (z + -y))) = z - f (y + f (z + -y)) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ hs hsum).symm

end GlobalTheory.CosetEigen
