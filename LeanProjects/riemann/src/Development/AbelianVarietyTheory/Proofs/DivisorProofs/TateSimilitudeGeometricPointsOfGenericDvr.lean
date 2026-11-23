import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingRootOfUnityLiftReduce
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTGeomExt

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem tateIsoO_transport {k k' : Type} [Field k] [Field k'] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → k'ˣ → Prop}
    (I : TateIsoO D k Q act e) (r : Q →* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn r {y : Q | y ^ n = 1} {y : Q' | y ^ n = 1})
    (ζ' : ℕ → k'ˣ) (hprim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ' n) n)
    (hpow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ' (n * m) ^ m = ζ' n)
    (hisom : ∀ n, 0 < n → n.Coprime p → ∀ x y,
      e' n (r (I.ev n x)) (r (I.ev n y)) (ζ' n ^ (2 * D.EF x y))) :
    ∃ I' : TateIsoO D k' Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) := by
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x ^ n = 1 :=
    fun n h1 h2 x => (I.onto n h1 h2 _).2 ⟨x, rfl⟩
  refine ⟨
    { ζ := ζ'
      ζ_prim := hprim
      ζ_pow := hpow
      ev := fun n x => r (I.ev n x)
      add := fun n x y => by simp only [I.add, map_mul]
      lin := fun n c x => by simp only [I.lin, hact]
      ker := fun n h1 h2 x => ?_
      onto := fun n h1 h2 q => ?_
      tower := fun n m h1 h2 h3 x => by simp only [← map_pow, I.tower n m h1 h2 h3]
      isom := hisom }, fun n x => rfl⟩
  · rw [← I.ker n h1 h2 x]
    constructor
    · intro h
      refine (hbij n h1 h2).injOn (htor n h1 h2 x) (show (1 : Q) ^ n = 1 from one_pow n) ?_
      rw [h, map_one]
    · intro h
      show r (I.ev n x) = 1
      rw [h, map_one]
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := (hbij n h1 h2).surjOn hq
      obtain ⟨x, hx⟩ := (I.onto n h1 h2 y).1 hy
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      show r (I.ev n x) ^ n = 1
      rw [← map_pow, htor n h1 h2 x, map_one]

end GlobalTheory.HTGeomExt

namespace GlobalTheory.HTGeomExt

theorem tateIsoO_geom_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm G _ _ hab act P hP y hy hgen k _ _ β
  obtain ⟨V, j, h, hj, hx⟩ := GlobalTheory.T.geometric_point_dvr_factors_valuation_subring_closure W L k (spMap β)
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : V) := fun n hn => by
    simpa using (b.unit n hn).map (j.comp gm)
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing V (AlgebraicClosure L) k h (Sp W) G hab (spMap j)
  have hs : spMap ((algebraMap V (AlgebraicClosure L)).comp j) =
      spMap (algebraMap V (AlgebraicClosure L)) ≫ spMap j := by
    dsimp only [spMap]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hg := hgen (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L))
  rw [← hj, hs] at hg
  obtain ⟨I, hI⟩ := hg
  rw [hx]
  have hz : ∀ n, ∃ z : Vˣ, 0 < n → n.Coprime p →
      (algebraMap V (AlgebraicClosure L) (z : V) = (I.ζ n : AlgebraicClosure L) ∧
        IsPrimitiveRoot (Units.map (h : V →* k) z) n) := by
    intro n
    by_cases hn : 0 < n ∧ n.Coprime p
    · obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := valuationRing_rootOfUnity_lift_reduce V (AlgebraicClosure L) k h n
        (hunit n hn.2) (I.ζ n) (I.ζ_prim n hn.1 hn.2).pow_eq_one
      exact ⟨z, fun _ _ => ⟨hz1, hz2 (I.ζ_prim n hn.1 hn.2)⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose z hz using hz
  have hzU : ∀ n, 0 < n → n.Coprime p →
      Units.map (algebraMap V (AlgebraicClosure L) : V →* AlgebraicClosure L) (z n) = I.ζ n :=
    fun n h1 h2 => Units.ext (hz n h1 h2).1
  have hinj : Function.Injective (algebraMap V (AlgebraicClosure L)) :=
    IsFractionRing.injective V (AlgebraicClosure L)
  have hLb := LB.isLB_pull hP (lift (𝟙 G) (𝟙 G)).left
  have hpow : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p →
      Units.map (h : V →* k) (z (n * m)) ^ m = Units.map (h : V →* k) (z n) := by
    intro n m h1 h2 h3
    have hn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) h3
    rw [← map_pow]
    congr 1
    apply Units.ext
    apply hinj
    rw [Units.val_pow_eq_pow_val, map_pow, (hz _ (Nat.mul_pos h1 h2) h3).1, (hz n h1 hn).1,
      ← Units.val_pow_eq_pow_val, I.ζ_pow n m h1 h2 h3]
  have hisom : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x x', Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n (r (I.ev n x)) (r (I.ev n x'))
      (unitOn (Units.map (h : V →* k) (z n) ^ (2 * D.EF x x'))) := by
    intro n h1 h2 x x'
    have hi := I.isom n h1 h2 x x'
    rw [← hzU n h1 h2, ← map_zpow] at hi
    have ho := hr4 _ hLb n (hunit n h2) _ _ (z n ^ (2 * D.EF x x'))
      ((I.onto n h1 h2 _).2 ⟨x, rfl⟩) ((I.onto n h1 h2 _).2 ⟨x', rfl⟩) hi
    rw [map_zpow] at ho
    exact ho
  obtain ⟨I', hI'⟩ := tateIsoO_transport (act' := fun c g => g ≫ act.act c)
    (e' := fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)) I r (fun c q => hr2 (act.act c) q)
    (fun n _ h2 => hr3 n (hunit n h2)) (fun n => Units.map (h : V →* k) (z n))
    (fun n h1 h2 => (hz n h1 h2).2) hpow hisom
  refine ⟨I', fun x => ?_⟩
  rw [hI', ← hI x]
  refine (hr1 (toUnit _ ≫ y x) _ _ ?_ ?_).symm
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _

end GlobalTheory.HTGeomExt
