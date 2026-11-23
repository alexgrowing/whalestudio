import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitForm

theorem exists_coords {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (τ : Forms.balForms ℤ O X B) :
    ∃ c : J → B, ∀ a b, (τ : Forms.Bil X B) a b = ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel O X)
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  refine ⟨fun k => ∑ j, ε.repr (β j) k • Forms.balTensorLift τ (e j), fun a b => ?_⟩
  have h1 (j) : e.repr (Forms.balTensorMk O a b) j =
      ∑ k, ε.repr (β j) k * (ε k : LinearMap.BilinForm ℤ X) a b := by
    have h := congrArg (fun g : PolFan.balForms (star : O → O) X =>
      (g : LinearMap.BilinForm ℤ X) a b) (ε.sum_repr (β j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  rw [← Forms.balTensorLift_mk, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
  simp only [map_zsmul]
  simp only [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_comm]

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    [IsAlgClosed (ResidueField V)] {n : ℕ} (hn : IsUnit (n : V)) (u : Vˣ) :
    ∃ v : Vˣ, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue V u) (Nat.pos_of_ne_zero hn0)
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsUnit a := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0] at hz
    exact (residue_ne_zero_iff_isUnit _).2 u.isUnit hz.symm
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (R := V) (I := maximalIdeal V)
    (Polynomial.X ^ n - Polynomial.C (u : V)) (Polynomial.monic_X_pow_sub_C _ hn0) a
    (by
      rw [← residue_eq_zero_iff]
      simp [hz])
    (by
      refine IsUnit.map _ ?_
      simpa [Polynomial.derivative_X_pow] using ⟨hn, ha.pow _⟩)
  have hy' : y ^ n = u := by
    simpa [sub_eq_zero] using hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by simpa using hy')⟩

theorem mem_of_diag {O : Type} [CommRing O] (bar : O → O) {w : O} (hw : w + bar w = 1)
    {X : Type} [AddCommGroup X] [Module O X] {G : Type} [CommGroup G] (U : Subgroup G)
    (q : X → X → G) (hs : ∀ a b, q a b = q b a) (ha : ∀ a a' b, q (a + a') b = q a b * q a' b)
    (hb : ∀ (x : O) a b, q (x • a) b = q a (bar x • b)) (hd : ∀ y, q y (w • y) ∈ U) (a b : X) :
    q a b ∈ U := by
  have hr (a b b') : q a (b + b') = q a b * q a b' := by rw [hs, ha, hs b, hs b']
  have h1 : q a (w • b) * q b (w • a) = q a b := by
    rw [hs b, hb, ← hr, ← add_smul, hw, one_smul]
  have h2 : q a b = q (a + b) (w • (a + b)) / (q a (w • a) * q b (w • b)) := by
    rw [smul_add, ha, hr, hr, ← h1, eq_div_iff_mul_eq']
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h2]
  exact U.div_mem (hd _) (U.mul_mem (hd _) (hd _))

theorem exists_unit_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  intro E _ _ _ H X _ _ _ _ V _ _ _ hV hk n hn m N ε t ht q hs ha hb hd
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  let φ : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V) : V →* FractionRing V)
  have hφ : Function.Injective φ := Units.map_injective hinj
  let τ : Fin m → (FractionRing V)ˣ := fun i =>
    Units.mk0 (algebraMap V (FractionRing V) (t i)) (fun h => ht i (hinj (by rw [h, map_zero])))
  let M : X → X → (FractionRing V)ˣ := fun a b =>
    ∏ i, τ i ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) a b)
  have Ms (a b) : M a b = M b a := Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.1 a b]
  have Ma (a a' b) : M (a + a') b = M a b * M a' b := by
    simp only [M, map_add, LinearMap.add_apply, mul_add, zpow_add, Finset.prod_mul_distrib]
  have Mb (x : 𝓞 E) (a b) : M (x • a) b = M a (H.bar x • b) :=
    Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.2 x a b]
  have hmem := mem_of_diag H.bar hw φ.range (fun a b => q a b / M a b)
    (fun a b => by rw [hs, Ms]) (fun a a' b => by rw [ha, Ma, mul_div_mul_comm])
    (fun x a b => by rw [hb, Mb]) (fun y => by
      obtain ⟨u, hu⟩ := hd y
      refine ⟨u, ?_⟩
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      rw [hu]
      simp [M, τ, φ])
  choose u hu using hmem
  have us (a b) : u a b = u b a := hφ (by rw [hu, hu, hs, Ms])
  have ua (a a' b) : u (a + a') b = u a b * u a' b :=
    hφ (by rw [map_mul, hu, hu, hu, ha, Ma, mul_div_mul_comm])
  have ub (x : 𝓞 E) (a b) : u (x • a) b = u a (H.bar x • b) := hφ (by rw [hu, hu, hb, Mb])
  have ur (a b b') : u a (b + b') = u a b * u a b' := by rw [us, ua, us b, us b']
  obtain ⟨c, hc⟩ := exists_coords (O := 𝓞 E) hw ε ⟨Forms.bilOfMul u ua ur, us, ub⟩
  choose v hv using fun k => exists_root hn (c k).toMul
  refine ⟨Sum.elim (fun i => t i * v (.inl i)) (fun j => v (.inr j)),
    fun i => ⟨(v (.inl i))⁻¹, by simp⟩, fun j => Units.isUnit _, fun a b => ?_⟩
  have h1 : u a b = ∏ k, v k ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
    have h := congrArg Additive.toMul (hc a b)
    simp only [toMul_sum, toMul_zsmul, ← hv] at h
    simp only [zpow_mul, zpow_natCast]
    exact h
  have h2 : q a b = M a b * φ (u a b) := by rw [hu, mul_div_cancel]
  rw [h2, h1]
  simp [M, τ, φ, Fintype.prod_sum_type, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.UnitForm
