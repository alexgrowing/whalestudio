import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

theorem exists_index_of_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (e : Spec (CommRingCat.of R) ⟶ X) : ∃ j : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U j := by
  have h : e (IsLocalRing.closedPoint R) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) e hj).ge⟩

theorem exists_intChart : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g], LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom → ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s)) → FBOfSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G), (∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] Lr.L) (cubeLB G ![fst G G, snd G G ≫ act.act (star a)] Lr.L)) → ∃ (d : ℕ) (x : Fam G (Fin d)) (j : Lr.L.ι) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (B : FB R d O), IsUnivChart G d x ∧ ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, IsNormRos Lr.L _ _ (u a)) ∧ IsFBOf Lr c act u x j B := by
  intro hRos hFB R _ _ G _ _ _ h2 h3 Lr c O _ _ act hiso
  obtain ⟨d, x, hx⟩ := univChartLoc G
  obtain ⟨j, hj⟩ := exists_index_of_local Lr.L Lr.isLB η[G].left
  have hu : ∀ a : O, ∃ u, IsNormRos Lr.L (act.act a) (act.act (star a)) u := fun a => by
    have := act.hom a
    have := act.hom (star a)
    exact (hRos _ G Lr.L Lr.isLB _ _ (hiso a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := hFB R G h2 h3 Lr c O act u hu d x hx j hj
  exact ⟨d, x, j, u, B, hx, hj, hu, hB⟩

end GlobalTheory.JetSer
