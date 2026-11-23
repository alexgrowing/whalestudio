import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.SkewPairingCmp

theorem map_add_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (x y y' : M) : B x (y + y') = B x y * B x y' := by
  have h : ∀ a b, B a b = (B b a)⁻¹ := fun a b => eq_inv_of_mul_eq_one_left (hsk a b)
  rw [h x (y + y'), hadd, mul_inv, ← h, ← h]

theorem map_zero_left {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (y : M) : B 0 y = 1 := by
  have h := hadd 0 0 y
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem map_zero_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (x : M) : B x 0 = 1 := by
  have h := hsk x 0
  rwa [map_zero_left B hadd, _root_.mul_one] at h

theorem ext_right {M : Type} [AddCommGroup M] {G : Type} [CommGroup G] (B : M → M → G)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (hnd : ∀ x, (∀ y, B x y = 1) → x = 0) {y y' : M} (h : ∀ x, B x y = B x y') : y = y' := by
  have h' : ∀ a b, B a b = (B b a)⁻¹ := fun a b => eq_inv_of_mul_eq_one_left (hsk a b)
  refine sub_eq_zero.mp (hnd _ fun x => ?_)
  have h1 := hadd (y - y') y' x
  rw [sub_add_cancel, h' y x, h x, ← h'] at h1
  exact (right_eq_mul.mp h1)

theorem exists_repr {M : Type} [AddCommGroup M] [Finite M] {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (B : M → M → kˣ)
    (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hsk : ∀ x y, B x y * B y x = 1)
    (hnd : ∀ x, (∀ y, B x y = 1) → x = 0) (f : M → kˣ) (hf : ∀ x x', f (x + x') = f x * f x') :
    ∃ z, ∀ x, f x = B x z := by
  let φ : M → (Multiplicative M →* kˣ) := fun y =>
    MonoidHom.mk' (fun x => B x.toAdd y) (fun a b => hadd _ _ _)
  have hinj : Function.Injective φ := fun y y' h =>
    ext_right B hadd hsk hnd fun x => DFunLike.congr_fun h (Multiplicative.ofAdd x)
  haveI : NeZero (Monoid.exponent (Multiplicative M)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card (Multiplicative M →* kˣ) = Nat.card (Multiplicative M) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative M) k
  have hpos : 0 < Nat.card (Multiplicative M) := Nat.card_pos
  haveI : Finite (Multiplicative M →* kˣ) := Nat.finite_of_card_ne_zero (by omega)
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; exact le_of_eq rfl)
  obtain ⟨z, hz⟩ := hbij.2 (MonoidHom.mk' (fun x => f x.toAdd) (fun a b => hf _ _))
  exact ⟨z, fun x => (DFunLike.congr_fun hz (Multiplicative.ofAdd x)).symm⟩

theorem exists_linearEquiv : ∀ (O : Type) [Ring O] (st : O → O) (M : Type) [AddCommGroup M] [Module O M] [Finite M] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B E : M → M → kˣ) (e : O), (∀ c, st (st c) = c) → (∀ c, e * c = c * e) → (∀ c, st e * c = c * st e) → (∀ x : M, e • x + st e • x = x) → (∀ x : M, e • st e • x = 0) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, B x y * B y x = 1) → (∀ (c : O) x y, B (c • x) y = B x (st c • y)) → (∀ x, (∀ y, B x y = 1) → x = 0) → (∀ x x' y, E (x + x') y = E x y * E x' y) → (∀ x y, E x y * E y x = 1) → (∀ (c : O) x y, E (c • x) y = E x (st c • y)) → (∀ x, (∀ y, E x y = 1) → x = 0) → ∃ g : M ≃ₗ[O] M, ∀ x y, B (g x) (g y) = E x y := by
  intro O _ st M _ _ _ k _ _ _ B E e hst hce hcs hsum hzero Badd Bsk Badj Bnd Eadd Esk Eadj End
  choose h hh using fun y => exists_repr B Badd Bsk Bnd (fun x => E x y) (fun x x' => Eadd x x' y)
  have hh : ∀ x y, E x y = B x (h y) := fun x y => hh y x
  have hadd : ∀ y y', h (y + y') = h y + h y' := fun y y' =>
    ext_right B Badd Bsk Bnd fun x => by
      rw [← hh, map_add_right B Badd Bsk, map_add_right E Eadd Esk, hh, hh]
  have hsmul : ∀ (c : O) y, h (c • y) = c • h y := fun c y =>
    ext_right B Badd Bsk Bnd fun x => by
      have h1 := Eadj (st c) x y
      have h2 := Badj (st c) x (h y)
      rw [hst] at h1 h2
      rw [← hh, ← h1, ← h2, hh]
  have hzero' : ∀ x : M, st e • e • x = 0 := fun x => by
    rw [smul_smul, ← hce, ← smul_smul, hzero]
  have hss : ∀ x : M, st e • st e • x = st e • x := fun x => by
    have := hsum (st e • x)
    rwa [hzero, zero_add] at this
  have hee : ∀ x : M, e • e • x = e • x := fun x => by
    have := hsum (e • x)
    rwa [hzero', add_zero] at this
  let g : M →ₗ[O] M :=
    { toFun := fun x => e • x + st e • h x
      map_add' := fun x y => by rw [hadd, smul_add, smul_add]; abel
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, hsmul, smul_add, smul_smul, hce c, hcs c] }
  have hg : ∀ x y, B (g x) (g y) = E x y := fun x y => by
    change B (e • x + st e • h x) (e • y + st e • h y) = E x y
    have h1 : B (e • x) (e • y) = 1 := by rw [Badj, hzero', map_zero_right B Badd Bsk]
    have h4 : B (st e • h x) (st e • h y) = 1 := by
      rw [Badj, hst, hzero, map_zero_right B Badd Bsk]
    have h2 : B (e • x) (st e • h y) = E x (st e • y) := by
      rw [Badj, hss, ← hsmul, ← hh]
    have h3 : B (st e • h x) (e • y) = E x (e • y) := by
      have a1 := Bsk (e • y) (st e • h x)
      have a2 := Esk (e • y) (st e • x)
      rw [Eadj (st e), hst, hee, hh (e • y), hsmul] at a2
      exact mul_left_cancel (a1.trans a2.symm)
    rw [Badd, map_add_right B Badd Bsk, map_add_right B Badd Bsk, h1, h2, h3, h4, _root_.one_mul,
      _root_.mul_one, _root_.mul_comm, ← map_add_right E Eadd Esk, hsum]
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx =>
    End x fun y => by rw [← hg, hx, map_zero_left B Badd]
  exact ⟨LinearEquiv.ofBijective g ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hg⟩

end GlobalTheory.SkewPairingCmp
