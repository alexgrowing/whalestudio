import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsMapOf.twoChart_rep_of_id {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} {d : ℕ}
    {x x' : Fam G (Fin d)} {φ : Pt R 1 d} (h : IsMapOf x x' (𝟙 G) φ) {n : ℕ} {a : Pt R n d}
    {y : Fam G (Fin n × Fin d)} (hy : Rep x a y) : Rep x' (comp1 φ a) y := by
  simpa only [Category.comp_id] using h.2 n a y hy

theorem twoChart_addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext l
  have : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self (F l)

theorem twoChart_of_rep_map : JetAlgSt → RepSt → MapSt → TwoChartSt := by
  intro _ hR hM R _ G _ d x x' hx hx'
  obtain ⟨φ, hφ, -⟩ := hM R G G d x' x hx' hx (𝟙 G) (Category.comp_id _)
  obtain ⟨φi, hφi, -⟩ := hM R G G d x x' hx hx' (𝟙 G) (Category.comp_id _)
  have uniq : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} {a b : Pt R n d}
      {y : Fam G (Fin n × Fin d)}, Rep z a y → Rep z b y → a = b := fun {z} hz {n a b y} ha hb =>
    ((hR R G d z hz (Fin n × Fin d)).2.1 y ((hR R G d z hz (Fin n × Fin d)).2.2.1 a y ha)).unique ha hb
  have ex : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} (j : Fin n),
      ∃ y : Fam G (Fin n × Fin d), Rep z (pt R d j) y := fun {z} hz {n} j =>
    ((hR R G d z hz (Fin n × Fin d)).1 (pt R d j) (gp_pt j)).exists
  refine ⟨φ, φi, ⟨hφ.1, hφi.1, ?_, ?_⟩, hφ, hφi, fun F F' hF hF' i => ?_, fun f α α' hα hα' => ?_⟩
  · obtain ⟨y, hy⟩ := ex hx (0 : Fin 1)
    have h := hφ.twoChart_rep_of_id (hφi.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h := hφi.twoChart_rep_of_id (hφ.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx' h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 2)
    obtain ⟨z, hz⟩ := ex hx' (1 : Fin 2)
    have h₁ := hF'.2 2 _ _ y z hy hz
    rw [twoChart_addOf_pt_pt] at h₁
    have h₂ := hφi.twoChart_rep_of_id (hF.2 2 _ _ y z (hφ.twoChart_rep_of_id hy) (hφ.twoChart_rep_of_id hz))
    exact congrFun (uniq hx' h₁ h₂) i
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h₁ := hα'.2 1 _ y hy
    have h₂ := hφi.twoChart_rep_of_id (hα.2 1 _ y (hφ.twoChart_rep_of_id hy))
    rw [gt_comp1_pt_right] at h₁ h₂
    exact uniq hx' h₁ h₂

end GlobalTheory.JetSer
