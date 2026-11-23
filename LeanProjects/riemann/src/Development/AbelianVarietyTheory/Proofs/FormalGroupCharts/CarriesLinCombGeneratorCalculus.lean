import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.CarryCalc

variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem carries_iff (w : LB.Iso L' (L.pull F)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) :
    Carries L F w φ ε g g' ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
        gm r z (LB.wchart L (fun k => φ k ≫ F) p) (g'.s p) = pw w φ ε r z p q * gm r z (LB.wchart L' φ q) (g.s q) := by
  refine (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g')
    (fun j x hx => wchart_pull_le L F φ j hx) (fun j => rfl)).trans ⟨fun H Z r z p q hp hq => ?_, fun H Z r z p q hp hq => ?_⟩
  · have := H Z r z p q (Set.mem_iInter.1 hp) (Set.mem_iInter.1 hq)
    rw [Category.comp_id] at this
    exact this
  · rw [Category.comp_id]
    exact H Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

def fac (w : LB.Iso L' (L.pull F)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_carries {w : LB.Iso L' (L.pull F)} {φ : K → (Y ⟶ X')} {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)}
    {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (H : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, fac w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine ((carries_iff w φ ε g g').1 H Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [pw, fac, Category.assoc]

theorem carries_of_val {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
  have hc := (carries_iff w φ ε g t).2 hv
  have e : ∀ j, g'.s j = t.s j := fun j => unit_ext fun y hy => by
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
    have v' : val g' (𝟙 Y) y J = val t (𝟙 Y) y J := (h y J J' hJ hJ').trans (val_of_carries hc (𝟙 Y) hJ hJ').symm
    exact (gen_trans hg' (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).trans ((congrArg _ v').trans
      (gen_trans ht (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).symm)
  obtain ⟨s⟩ := g'
  obtain ⟨s'⟩ := t
  obtain rfl : s = s' := funext e
  exact hc

theorem exists_good' {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hM (ψ z)
  exact ⟨J, hJ⟩

end GlobalTheory.ChartCmp.CarryCalc

namespace GlobalTheory.ChartCmp
open CarryCalc

theorem carries_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  intro X X' L' L F _ w hL' hL hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y K _ φ ε g hg
    obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
    exact ⟨t, ht, (carries_iff w φ ε g t).2 hv⟩
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' hs _ _ _ _ Hg Hh
    have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
        (val g (𝟙 Y) y J' = val h (𝟙 Y) y J' ↔ val g' (𝟙 Y) y J = val h' (𝟙 Y) y J) := fun y J J' hJ hJ' => by
      rw [val_of_carries Hg (𝟙 Y) hJ hJ', val_of_carries Hh (𝟙 Y) hJ hJ',
        DVR.prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => fac w y J J' (𝟙 Y ≫ ψ)), mul_right_inj]
    refine ⟨fun C => corr_of_val hL fun y J hJ => ?_, fun C => corr_of_val hL' fun y J' hJ' => ?_⟩
    · obtain ⟨J', hJ'⟩ := exists_good' hL' y
      exact (key y J J' hJ hJ').1 (val_corr hJ' C _)
    · obtain ⟨J, hJ⟩ := exists_good' hL y
      exact (key y J J' hJ hJ').2 (val_corr hJ C _)
  · intro Y Z K _ φ ε g g' r g'' hg _ hg'' H C
    refine carries_of_val hL' hL hw (DVR.pullGen_isGen _ _ _ _ hg r) hg'' fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_pull hJ, val_pull hJ', val_of_carries H _ hJ hJ']
    simp only [Category.assoc]
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' p hg hh _ _ hp Hg Hh C
    refine carries_of_val hL' hL hw (DVR.mulGen_isGen _ _ _ _ _ _ _ hg hh) hp fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_mul hJ, val_mul hJ', val_of_carries Hg _ hJ hJ', val_of_carries Hh _ hJ hJ',
      Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
    rfl
  · intro Y K _ φ ε g g' H
    refine (carries_iff w φ _ _ _).2 fun Z r z p q hp hq => ?_
    refine (map_inv _ _).trans ((congrArg (·⁻¹) ((carries_iff w φ ε g g').1 H Z r z p q hp hq)).trans ?_)
    refine (mul_inv _ _).trans (congrArg₂ (· * ·) ?_ (map_inv _ _).symm)
    simp only [pw, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.ChartCmp
