import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ZPart

section Mod
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {n : ℕ}

def Kl (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → M) : Prop := ∀ i, ∑ j, mu i j • u j = 0

theorem Kl.mul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : Matrix (Fin n) (Fin n) O) :
    Kl (a * b) u := by
  intro i
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h _, smul_zero, Finset.sum_const_zero]

theorem Kl.smul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : O) : Kl (a • b) u := by
  intro i
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, h i, smul_zero]

theorem Kl.cancel {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} {a ℓ : O} (hc : IsCoprime a ℓ)
    (hu : ∀ j, ∃ e : ℕ, ℓ ^ e • u j = 0) (h : Kl (a • b) u) : Kl b u := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ j, ℓ ^ e • u j = 0 := by
    choose f hf using hu
    refine ⟨∑ j, f j, fun j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun x _ => Nat.zero_le (f x)) (Finset.mem_univ j))
    rw [hd, pow_add, mul_comm, mul_smul, hf j, smul_zero]
  intro i
  obtain ⟨x, y, hxy⟩ := hc.pow_right (n := e)
  have h1 : a • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    simpa only [Matrix.smul_apply, smul_eq_mul, mul_smul] using h i
  have h2 : ℓ ^ e • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_smul, mul_comm, mul_smul, he j, smul_zero]
  calc ∑ j, b i j • u j = (x * a + y * ℓ ^ e) • ∑ j, b i j • u j := by rw [hxy, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1, h2, smul_zero, smul_zero, add_zero]
end Mod

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ)

noncomputable def adj : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => IsCMField.complexConj E (A.ga j i)

theorem adj_mul : adj A * A.ga = 1 := by
  ext i j
  simp only [adj, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  exact A.unitary i j

theorem map_inj {a b : Matrix (Fin n) (Fin n) (𝓞 E)}
    (h : a.map (algebraMap (𝓞 E) E) = b.map (algebraMap (𝓞 E) E)) : a = b := by
  refine Matrix.ext fun i j => ?_
  have h' := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) h
  simp only [Matrix.map_apply] at h'
  exact FaithfulSMul.algebraMap_injective (𝓞 E) E h'

theorem map_smul' (c : ℕ) (a : Matrix (Fin n) (Fin n) (𝓞 E)) :
    ((c : 𝓞 E) • a).map (algebraMap (𝓞 E) E) = (c : E) • a.map (algebraMap (𝓞 E) E) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]

theorem exists_adj : ∃ r : Matrix (Fin n) (Fin n) (𝓞 E),
    r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • ((N ^ 2 : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
  let σ : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom (IsCMField.complexConj E).toRingHom
  refine ⟨Matrix.of fun i j => σ ((A.p * A.q) j i), map_inj ?_⟩
  have hr : (Matrix.of fun i j => σ ((A.p * A.q) j i)).map (algebraMap (𝓞 E) E) =
      ((A.k * N : ℕ) : E) • adj A := by
    ext i j
    have hji := congrArg (fun m : Matrix (Fin n) (Fin n) E => m j i) A.prod
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hji
    have hσ : algebraMap (𝓞 E) E (σ ((A.p * A.q) j i)) =
        IsCMField.complexConj E (algebraMap (𝓞 E) E ((A.p * A.q) j i)) := rfl
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, adj, hσ, hji, map_mul,
      map_natCast]
  rw [Matrix.map_mul, hr, A.prod, Matrix.smul_mul, Matrix.mul_smul, adj_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem exists_factor (mu : Matrix (Fin n) (Fin n) E) (hmu : ∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) (c : ℕ)
    (cm : Matrix (Fin n) (Fin n) (𝓞 E)) (hcm : ∀ i j, (cm i j : E) = ((c * N : ℕ) : E) * mu i j) :
    ∃ r : Matrix (Fin n) (Fin n) (𝓞 E), r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • cm := by
  have hW : ∀ j : Fin n, ∃ w ∈ Λ.La, (A.k : E) • (Pi.single j 1 : Fin n → E) = A.ga.mulVec w := by
    intro j
    refine A.onto _ ?_
    simp only [stdLat, Submodule.mem_pi]
    intro i _
    refine Submodule.mem_one.mpr ⟨(Pi.single j (1 : 𝓞 E) : Fin n → 𝓞 E) i, ?_⟩
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  choose w hwΛ hw using hW
  have hy : ∀ i j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = mu.mulVec (w j) i := by
    intro i j
    have hm := hmu _ (hwΛ j)
    simp only [stdLat, Submodule.mem_pi] at hm
    exact Submodule.mem_one.mp (hm i (Set.mem_univ i))
  choose y hy using hy
  refine ⟨Matrix.of fun i j => (c : 𝓞 E) * y i j, map_inj ?_⟩
  have hGW : A.ga * Matrix.of (fun b j => w j b) = (A.k : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext b j
    have hb := congrFun (hw j) b
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at hb
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [← hb]
  have hWadj : Matrix.of (fun b j => w j b) = (A.k : E) • adj A := by
    calc Matrix.of (fun b j => w j b) = adj A * A.ga * Matrix.of (fun b j => w j b) := by
          rw [adj_mul, Matrix.one_mul]
      _ = (A.k : E) • adj A := by rw [Matrix.mul_assoc, hGW, Matrix.mul_smul, Matrix.mul_one]
  have hr : (Matrix.of fun i j => (c : 𝓞 E) * y i j).map (algebraMap (𝓞 E) E) =
      (c : E) • (mu * Matrix.of (fun b j => w j b)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_natCast, hy, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.map_mul, hr, A.prod, hWadj]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, adj_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, hcm]
  push_cast
  ring
end Lat

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (T : Over Xo.X)

@[reducible] noncomputable def ptMod : Module (𝓞 E) (Additive (T ⟶ Xo.univ.t.G)) where
  smul a x := Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act a)
  one_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 1) = x
    rw [Xo.univ.t.act.one, Category.comp_id]; rfl
  mul_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a * b)) =
      Additive.ofMul ((x.toMul ≫ Xo.univ.t.act.act b) ≫ Xo.univ.t.act.act a)
    rw [_root_.mul_comm, Xo.univ.t.act.mul, Category.assoc]
  smul_zero a := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.one_comp (Xo.univ.t.act.act a))
  smul_add a x y := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul (Xo.univ.t.act.act a))
  add_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a + b)) = _
    rw [Xo.univ.t.act.add, MonObj.comp_mul]; rfl
  zero_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 0) = _
    have h := ZhStable.act_natCast Xo 0
    rw [Nat.cast_zero, pow_zero] at h
    rw [h, MonObj.comp_one]; rfl

variable {T}

theorem kills_iff {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (u : Fin n → (T ⟶ Xo.univ.t.G)) :
    letI := ptMod Xo T
    Kills Xo mu u ↔ Kl mu (fun j => Additive.ofMul (u j)) := by
  refine forall_congr' fun i => ?_
  change (List.ofFn fun j => u j ≫ Xo.univ.t.act.act (mu i j)).prod = 1 ↔
    ∑ j, Additive.ofMul (u j ≫ Xo.univ.t.act.act (mu i j)) = 0
  rw [List.prod_ofFn, ← ofMul_prod, ofMul_eq_zero]

theorem pow_iff (m : ℕ) (x : T ⟶ Xo.univ.t.G) :
    letI := ptMod Xo T
    x ^ m = 1 ↔ (m : 𝓞 E) • Additive.ofMul x = 0 := by
  change x ^ m = 1 ↔ Additive.ofMul (x ≫ Xo.univ.t.act.act (m : 𝓞 E)) = 0
  rw [ZhStable.act_natCast Xo m, MonObj.comp_pow, Category.comp_id, ofMul_eq_zero]

theorem inZh_iff {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ) (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) (c : ℕ) (hc : Nat.Coprime c ℓ) :
    InZh Xo Λ (c * N) u ↔ Kills Xo (A.p * A.q) u := by
  letI := ptMod Xo T
  have tors : ∀ j, ∃ e : ℕ, (ℓ : 𝓞 E) ^ e • Additive.ofMul (u j) = 0 := by
    intro j
    obtain ⟨e, he⟩ := hu j
    have h := (pow_iff Xo (ℓ ^ e) (u j)).mp he
    rw [Nat.cast_pow] at h
    exact ⟨e, h⟩
  have cop : ∀ m : ℕ, Nat.Coprime m ℓ → IsCoprime (m : 𝓞 E) (ℓ : 𝓞 E) := by
    intro m hm
    simpa using (Nat.isCoprime_iff_coprime.mpr hm).map (Int.castRingHom (𝓞 E))
  constructor
  · rintro ⟨-, hZ⟩
    have hK : Kills Xo ((c : 𝓞 E) • (A.p * A.q)) u := by
      refine hZ ((A.k : E) • A.ga) (fun v hv => ?_) _ (fun i j => ?_)
      · rw [Matrix.smul_mulVec]
        exact A.into v hv
      · have hij := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) A.prod
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
        change algebraMap (𝓞 E) E ((c : 𝓞 E) * (A.p * A.q) i j) = _
        rw [map_mul, map_natCast, hij, Matrix.smul_apply, smul_eq_mul]
        push_cast
        ring
    exact (kills_iff Xo _ u).mpr (((kills_iff Xo _ u).mp hK).cancel (cop c hc) tors)
  · intro hK
    have hKl := (kills_iff Xo _ u).mp hK
    refine ⟨fun b => ?_, fun mu hmu cm hcm => ?_⟩
    · obtain ⟨r, hr⟩ := exists_adj A
      have h1 := hKl.mul r
      rw [hr] at h1
      have h2 := (h1.cancel (cop _ (A.cop.pow_left 2)) tors) b
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, ite_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
      have h3 := (pow_iff Xo (N ^ 2) (u b)).mpr h2
      rw [mul_pow, _root_.mul_comm, pow_mul, h3, one_pow]
    · obtain ⟨r, hr⟩ := exists_factor A mu hmu c cm hcm
      have h1 := hKl.mul r
      rw [hr] at h1
      exact (kills_iff Xo cm u).mpr (h1.cancel (cop _ (A.cop.pow_left 2)) tors)
end Pts

end GlobalTheory.ZPart

namespace GlobalTheory

theorem inZh_iff_kills_adapted :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N ℓ : ℕ), ℓ.Prime → 0 < N → ∀ (A : Adapt Λ N ℓ) (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) → (InZh Xo Λ N u ↔ Kills Xo (A.p * A.q) u) ∧ (InZh Xo Λ (A.k * N) u ↔ Kills Xo (A.p * A.q) u) := by
  intro E _ _ _ H Dw l Xo n Λ N ℓ _ _ A T u hu
  refine ⟨?_, ZPart.inZh_iff Xo A u hu A.k A.cop⟩
  have h1 := ZPart.inZh_iff Xo A u hu 1 (Nat.coprime_one_left ℓ)
  rwa [Nat.one_mul] at h1

end GlobalTheory
