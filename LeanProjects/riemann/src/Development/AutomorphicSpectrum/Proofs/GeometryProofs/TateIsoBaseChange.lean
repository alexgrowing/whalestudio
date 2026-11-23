import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.WeilBound.CoreStatements.HodgeTatePoints.MgTate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tate_iso_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (i : k →+* k') (x : Sp k ⟶ X), IsProper (pullback.snd t.G.hom x) → ∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t (spMap i ≫ x), ∀ n, 0 < n → (I'.ζ n : k') = i (I.ζ n) ∧ ∀ a, (I'.ev n a).left = spMap i ≫ (I.ev n a).left := by
  intro E _ _ _ H D X t k k' _ _ _ _ _ i x hprop I
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨_, _, -⟩ := PositivityTheory.HtPt.Mg.finrank_La D
  let e := PositivityTheory.HtPt.Mg.extPt i x
  have hprop' : IsProper (pullback.snd t.G.hom (spMap i ≫ x)) :=
    PositivityTheory.HtPt.Mg.proper_of_hom (A := t.G) e hprop
  have hone : ∀ g : Over.mk x ⟶ t.G, e ≫ g = 1 ↔ g = 1 := by
    intro g
    constructor
    · intro h
      exact PositivityTheory.HtPt.Mg.extPt_inj i x (h.trans (MonObj.comp_one e).symm)
    · intro h
      rw [h, MonObj.comp_one]
  have hfinT : ∀ n, 0 < n → Finite {y : Over.mk x ⟶ t.G // y ^ n = 1} := by
    intro n hn
    let N : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • (LinearMap.id : D.La →ₗ[ℤ] D.La))
    haveI : Finite (D.La ⧸ N) := Module.finite_of_fg_torsion _ (by
      intro q
      refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
      induction q using Submodule.Quotient.induction_on with
      | H a =>
        show (n : ℤ) • (Submodule.Quotient.mk a : D.La ⧸ N) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact ⟨a, rfl⟩)
    have hex : ∀ y : {y : Over.mk x ⟶ t.G // y ^ n = 1}, ∃ a, I.ev n a = y.1 :=
      fun y => (I.onto n hn y.1).1 y.2
    refine Finite.of_injective (fun y => (Submodule.Quotient.mk (hex y).choose : D.La ⧸ N)) ?_
    intro y y' hyy
    have h1 := (hex y).choose_spec
    have h2 := (hex y').choose_spec
    rw [Submodule.Quotient.eq] at hyy
    obtain ⟨c, hc⟩ := hyy
    apply Subtype.ext
    rw [← h1, ← h2]
    have hsm : ((n : ℤ) • LinearMap.id : D.La →ₗ[ℤ] D.La) c = n • c := by
      simp [natCast_zsmul]
    have hdec : (hex y).choose = (hex y').choose + n • c := by
      rw [← hsm, hc]
      abel
    rw [hdec, I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map (i : k →* k') (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective i.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n a => e ≫ I.ev n a
            add := fun n a b => by simp only [I.add, MonObj.comp_mul]
            lin := fun n c a => by simp only [I.lin, Category.assoc]
            ker := fun n hn a => by rw [← I.ker n hn a]; exact hone _
            onto := fun n hn g => by
              constructor
              · intro hg
                obtain ⟨y, hy, rfl⟩ := PositivityTheory.HtPt.Mg.torsion_desc t.G i x n (hfinT n hn) g hg
                obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
                exact ⟨a, rfl⟩
              · rintro ⟨a, rfl⟩
                rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
            tower := fun n m hn hm a => by rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              have h := PositivityTheory.HtPt.Mg.weilIs_pull_of_proper t.semi t.PP.isLB hprop' e (I.isom n hn a b)
              show Out.WeilIs t.G t.PP.L (n : ℤ) (e ≫ I.ev n a) (e ≫ I.ev n b)
                (unitOn ((Units.map (i : k →* k') (I.ζ n)) ^ D.EF a b))
              have hm : (Units.map (i : k →* k') (I.ζ n)) ^ D.EF a b
                  = Units.map (i : k →* k') (I.ζ n ^ D.EF a b) := by
                simp [map_zpow, map_pow]
              rw [hm]
              convert h using 1
              exact (PositivityTheory.HtPt.Mg.unitOn_map i _).symm }, ?_⟩
  intro n hn
  exact ⟨rfl, fun a => rfl⟩
