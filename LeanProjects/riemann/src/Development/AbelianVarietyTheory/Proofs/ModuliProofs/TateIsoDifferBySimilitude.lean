import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in

theorem _root_.GlobalTheory.tateIso_ev_eq_iff (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ D.ModN n (a - b) := by
  have key : I.ev n (a - b) * I.ev n b = I.ev n a := by rw [← I.add, sub_add_cancel]
  rw [show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]
  exact mul_eq_right

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in

theorem _root_.GlobalTheory.tateIso_ev_pow (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a : D.La) :
    I.ev n a ^ n = 1 :=
  (I.onto n hn _).mpr ⟨a, rfl⟩

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
private lemma exists_linearMap_ev_eq_of_tateIso (I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, I.ev n (f a) = I'.ev n a := by
  classical
  haveI := D.proj
  let N : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ D.ModN n x := by
    intro x
    show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y
    simp only [Nat.cast_smul_eq_nsmul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N := fun x y =>
    (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm
  have hs : ∀ a, ∃ b, I.ev n b = I'.ev n a :=
    fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
  choose s hs using hs
  let g : D.La →ₗ[𝓞 E] D.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel,
          I.add, hs, hs, hs, I'.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)
  refine ⟨f, fun a => ?_⟩
  have h1 : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel] at h1
  rw [h1, hs]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by
  intro E _ _ _ H D k _ Q _ act e he I I'
  have hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨f, hf⟩ := exists_linearMap_ev_eq_of_tateIso I I' hn
      exact ⟨f, fun _ => hf⟩
  choose f hf using hf
  have hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n :=
        IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)
      have hpow : ((I'.ζ n : kˣ) : k) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
      refine ⟨i, fun _ => ?_⟩
      ext
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hi]
  choose ν hν using hk
  refine ⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩
  · intro n m hn hm a
    rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm),
      hf n hn, I'.tower n m hn hm]
  · intro n hn
    obtain ⟨g, hg⟩ := exists_linearMap_ev_eq_of_tateIso I' I hn
    refine ⟨g, fun a => ⟨?_, ?_⟩⟩
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]
  · intro n hn a b
    have h1 := I.isom n hn (f n a) (f n b)
    have h2 := I'.isom n hn a b
    rw [hf n hn, hf n hn] at h1
    have hc := he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
      (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2
    rw [hν n hn, ← zpow_mul] at hc
    rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]

end GlobalTheory
