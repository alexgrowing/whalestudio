import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open GlobalTheory.CompanionTheory.Ar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace Lev

theorem eq_iff {La Q : Type} [AddCommGroup La] [Group Q] (m : ℕ) (ev : La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ a, ev a = 1 ↔ ∃ b, a = m • b) (a b : La) :
    ev a = ev b ↔ (Submodule.Quotient.mk a : La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) =
      Submodule.Quotient.mk b := by
  have h : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
  rw [Submodule.Quotient.eq, h, mul_eq_right, hker]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem onto_of_count {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group Q] (m : ℕ) (hm : 0 < m)
    (ev ev' : La → Q) (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ a, ev a = 1 ↔ ∃ b, a = m • b)
    (hon : ∀ x, x ^ m = 1 ↔ ∃ a, ev a = x)
    (hadd' : ∀ a b, ev' (a + b) = ev' a * ev' b) (hker' : ∀ a, ev' a = 1 ↔ ∃ b, a = m • b)
    (ht : ∀ a, ev' a ^ m = 1) (x : Q) (hx : x ^ m = 1) : ∃ a, ev' a = x := by
  have : Finite (La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.ne')⟩, ?_⟩
    show (m : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by simp⟩
  choose g hg using fun a => (hon _).1 (ht a)
  choose s hs using Submodule.Quotient.mk_surjective (LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La)))
  have hinj : Function.Injective fun y => (Submodule.Quotient.mk (g (s y)) :
      La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) := by
    intro y y' h
    have h1 := (eq_iff m ev hadd hker _ _).2 h
    rw [hg, hg, eq_iff m ev' hadd' hker', hs, hs] at h1
    exact h1
  obtain ⟨c, rfl⟩ := (hon x).1 hx
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj (Submodule.Quotient.mk c)
  exact ⟨s y, by rw [← hg, eq_iff m ev hadd hker]; exact hy⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_ef_one (hpq : 0 < D.p + D.q) : ∃ a b, D.EF a b = 1 := by
  have : Module.Projective (𝓞 E) D.La := D.proj
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; exact hpq)
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem push {S : Scheme.{0}} (t : SAB H S) {k K : Type} [Field k] [Field K] (j : k →+* K) (q : Sp k ⟶ S)
    (q' : Sp K ⟶ S) (hq : q' = spMap j ≫ q)
    (I : TateIso D k (Over.mk q ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))
    (J : TateIso D K (Over.mk q' ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :
    ∃ I' : TateIso D K (Over.mk q' ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (∀ n, (I'.ζ n : K) = j (I.ζ n)) ∧ ∀ n a, (I'.ev n a).left = spMap j ≫ (I.ev n a).left := by
  subst hq
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Epi (spMap j) := WeilObj.epi_spMap_field k K j
  let ψ := WeilObj.extPt q j
  have inj : ∀ x x' : Over.mk q ⟶ t.G, ψ ≫ x = ψ ≫ x' → x = x' := fun x x' h => by
    have h' : spMap j ≫ x.left = spMap j ≫ x'.left := congrArg CommaMorphism.left h
    exact Over.OverMorphism.ext ((cancel_epi (spMap j)).1 h')
  have hadd : ∀ n a b, ψ ≫ I.ev n (a + b) = (ψ ≫ I.ev n a) * (ψ ≫ I.ev n b) := fun n a b => by
    rw [I.add, comp_mul]
  have hker : ∀ n, 0 < n → ∀ a, ψ ≫ I.ev n a = 1 ↔ ∃ b, a = n • b := fun n hn a => by
    rw [← I.ker n hn a]
    exact ⟨fun h => inj _ _ (by rw [h, MonObj.comp_one]), fun h => by rw [h, MonObj.comp_one]⟩
  have ht : ∀ n, 0 < n → ∀ a, (ψ ≫ I.ev n a) ^ n = 1 := fun n hn a => by
    rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n a => ψ ≫ I.ev n a
            add := hadd
            lin := fun n c a => by rw [I.lin, Category.assoc]
            ker := hker
            onto := fun n hn x => ⟨onto_of_count n hn (J.ev n) _ (J.add n) (J.ker n hn) (J.onto n hn) (hadd n)
              (hker n hn) (ht n hn) x, by rintro ⟨a, rfl⟩; exact ht n hn a⟩
            tower := fun n m hn hm a => by rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => ?_ }, fun n => rfl, fun n a => rfl⟩
  obtain ⟨a', ha'⟩ := (J.onto n hn _).1 (ht n hn a)
  obtain ⟨b', hb'⟩ := (J.onto n hn _).1 (ht n hn b)
  have h1 := J.isom n hn a' b'
  rw [ha', hb'] at h1
  have h2 := weilIs_fieldExt t.G t.PP.L t.PP.isLB k K j q _ rfl n _ _ _ _ rfl rfl _ _ (I.isom n hn a b) h1
  rw [h2, map_zpow] at h1
  exact h1

end Lev

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem level_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  intro E _ _ _ H D S t Ω _ _ ξ n hn hpq _ hfull hT
  obtain ⟨I⟩ := hT (AlgebraicClosure Ω) (algebraMap Ω _)
  choose ev hev using fun a => hfull (AlgebraicClosure Ω) (algebraMap Ω _) (I.ev n a) ((I.onto n hn _).2 ⟨a, rfl⟩)
  have hζ : ∃ z : Ω, algebraMap Ω (AlgebraicClosure Ω) z = I.ζ n := by
    obtain ⟨a, b, hab⟩ := Lev.exists_ef_one D hpq
    have h0 := I.isom n hn a b
    rw [hab, zpow_one] at h0
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := Ω) (I.ζ n : AlgebraicClosure Ω)).2 fun σ => ?_
    have hσ : spMap (σ : AlgebraicClosure Ω →+* AlgebraicClosure Ω) ≫ spMap (algebraMap Ω (AlgebraicClosure Ω)) =
        spMap (algebraMap Ω (AlgebraicClosure Ω)) := by
      rw [← WeilObj.spMap_comp_of]
      exact congrArg spMap (RingHom.ext fun x => σ.commutes x)
    have h2 := weilIs_fieldExt t.G t.PP.L t.PP.isLB _ _ (σ : AlgebraicClosure Ω →+* AlgebraicClosure Ω) _ _
      (by rw [← Category.assoc, hσ]) n _ _ _ _ (by rw [hev, ← Category.assoc, hσ])
      (by rw [hev, ← Category.assoc, hσ]) _ _ h0 h0
    exact (congrArg Units.val h2).symm
  obtain ⟨z, hz⟩ := hζ
  have hz0 : z ≠ 0 := fun h => (I.ζ n).ne_zero (by rw [← hz, h, map_zero])
  refine ⟨ev, Units.mk0 z hz0, ?_, fun k _ _ f => ?_⟩
  · refine IsPrimitiveRoot.coe_units_iff.1 ?_
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap Ω (AlgebraicClosure Ω)) ?_ (RingHom.injective _)
    rw [Units.val_mk0, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)
  · let _ : Algebra Ω k := f.toAlgebra
    let j : AlgebraicClosure Ω →ₐ[Ω] k := IsAlgClosed.lift
    have hj : spMap f = spMap j.toRingHom ≫ spMap (algebraMap Ω (AlgebraicClosure Ω)) := by
      rw [← WeilObj.spMap_comp_of]
      exact congrArg spMap (RingHom.ext fun x => (j.commutes x).symm)
    obtain ⟨J⟩ := hT k f
    obtain ⟨I', h1, h2⟩ := Lev.push D t j.toRingHom _ (spMap f ≫ ξ) (by rw [hj, Category.assoc]) I J
    refine ⟨I', ?_, fun a => ?_⟩
    · rw [h1, ← hz]
      exact j.commutes z
    · rw [h2, hev, ← Category.assoc, ← hj]

end PositivityTheory.HtPt.Htat
