import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGeometricFibre

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.FiniteEtaleModels.O.tExt :
    UpperTheory.Gal.FiniteEtaleModels.O.TExt := by
  intro G R _ _ gb N Ω _ _ σ o I k _ _ x
  obtain ⟨f, rfl⟩ : ∃ f : Ω →+* k, x = spMap f := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  obtain ⟨g, rfl⟩ : ∃ g : R →+* Ω, σ = spMap g := ⟨(Spec.preimage σ).hom, by simp [spMap]⟩
  have hcomp : spMap f ≫ spMap g = spMap (f.comp g) := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨J, -⟩ := o.geom k (spMap f) (f.comp g) hcomp
  haveI := G.finLa
  let h : Over.mk (spMap f) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap f) (by simp)
  haveI : Epi h := by
    haveI : Epi h.left := (GlobalTheory.UPel.GeometricLevelExistence.epi_spMap_field f : _)
    exact Over.epi_of_epi_left h
  have hadd : ∀ n a b, h ≫ I.ev n (a + b) = (h ≫ I.ev n a) * (h ≫ I.ev n b) := by
    intro n a b
    rw [I.add, MonObj.comp_mul]
  have hker : ∀ n, 0 < n → ∀ a, h ≫ I.ev n a = 1 ↔ ∃ b, a = n • b := by
    intro n hn a
    rw [← I.ker n hn a]
    constructor
    · intro e
      apply (cancel_epi h).1
      rw [e, MonObj.comp_one]
    · intro e
      rw [e, MonObj.comp_one]
  have htors : ∀ n, 0 < n → ∀ a, (h ≫ I.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
  refine ⟨{ ζ := fun n => Units.map (f : Ω →* k) (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective f.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n y => h ≫ I.ev n y
            add := hadd
            lin := fun n b a => by
              show h ≫ I.ev n (b • a) = (h ≫ I.ev n a) ≫ o.act.act b
              rw [I.lin, Category.assoc]
            ker := hker
            onto := fun n hn q => by
              constructor
              · intro hq
                obtain ⟨c, rfl⟩ := (J.onto n hn q).1 hq
                obtain ⟨a, ha⟩ := GlobalTheory.UPel.GeometricLevelExistence.exists_eq_of_count n hn (fun a => h ≫ I.ev n a)
                  (J.ev n) (hadd n) (J.add n) (hker n hn) (J.ker n hn)
                  (fun a => (J.onto n hn _).1 (htors n hn a) |>.imp fun c hc => hc.symm) c
                exact ⟨a, ha⟩
              · rintro ⟨a, rfl⟩
                exact htors n hn a
            tower := fun n m hn hm a => by
              show (h ≫ I.ev (n * m) a) ^ m = h ≫ I.ev n a
              rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              have hw := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds o.ab
                (pull_isLB o.isLB _) h (I.isom n hn a b)
              convert hw using 1
              rw [← map_zpow]
              exact (GlobalTheory.UPel.GeometricLevelExistence.unitOn_pull_spMap f _).symm }, fun n hn y => rfl⟩
