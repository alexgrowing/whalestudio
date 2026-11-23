import Mathlib
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Columns.RowFormsNZ
import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Idem

variable {K : Type} [Field K] {A : Type} [Group A] {M : Type} [Group M] [Fintype M]

def v0eZ (j : M →* A) (ε : M →* Kˣ) : MonoidAlgebra K A :=
  ∑ ζ : M, MonoidAlgebra.single (j ζ) ((Fintype.card M : K)⁻¹ * (((ε ζ)⁻¹ : Kˣ) : K))

open Classical in
theorem centralIdempotent_coeff (j : M →* A) (ε : M →* Kˣ) (u : A) :
    (v0eZ j ε).coeff u = ∑ ζ : M, if j ζ = u then (Fintype.card M : K)⁻¹ * (((ε ζ)⁻¹ : Kˣ) : K) else 0 := by
  classical
  rw [v0eZ, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]

end Idem

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] [Fintype A]
  (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
  {M : Type} [Group M] [Fintype M] (j : M →* A) (ε : M →* X.Kˣ)

theorem representation_asAlgebraHom_sum (a : MonoidAlgebra X.K A) :
    (trRep C Λ ι hι).asAlgebraHom a = ∑ t : A, a.coeff t • trRep C Λ ι hι t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]

theorem trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (hj : Function.Injective j)
    (hscal : ∀ (ζ : M) (φ : (formGSD C Λ).EqFun), trRep C Λ ι hι (j ζ) φ = ((ε ζ : X.Kˣ) : X.K) • φ)
    (d : DecoSet X.E n ST SG) (v : C.V) (hv0 : v ≠ 0)
    (hfix : ∀ (γ : UF X.E n) (h : ↥Λ.grp), (γ, h.1) • d = d → ((Λ.chr h : X.Kˣ) : X.K) • C.rho γ v = v)
    (hfree : ∀ (γ : UF X.E n) (h : ↥Λ.grp) (t : A), (γ, h.1 * ι t) • d = d → ∃ ζ, j ζ = t)
    (a : MonoidAlgebra X.K A) (ha : a * v0eZ j ε ≠ 0) : (trRep C Λ ι hι).asAlgebraHom a ≠ 0 := by
  classical
  have hcard : (Fintype.card M : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hv : ∀ g : (formGSD C Λ).G, g • d = d → (formGSD C Λ).ρ g v = v := by
    rintro ⟨γ, h⟩ hg
    exact hfix γ h hg
  let φ0 : (formGSD C Λ).EqFun := ⟨(formGSD C Λ).orbFun d v, GSD.orbFun_mem hv⟩
  have hφd : (φ0 : DecoSet X.E n ST SG → C.V) d = v := by
    have h1 := GSD.orbFun_smul hv 1
    rw [one_smul, map_one] at h1
    exact h1
  have hval : ∀ u : A, (φ0 : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), ι u) • d) =
      ((Fintype.card M : X.K) * (v0eZ j ε).coeff u) • v := by
    intro u
    by_cases hu : ∃ ζ, j ζ = u
    · obtain ⟨ζ0, rfl⟩ := hu
      have h1 : ((trRep C Λ ι hι (j ζ0⁻¹) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d =
          ((((ε ζ0⁻¹ : X.Kˣ) : X.K) • φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d := by
        rw [hscal]
      rw [trRep_apply] at h1
      simp only [map_inv, inv_inv] at h1
      rw [h1, Submodule.coe_smul, Pi.smul_apply, hφd, centralIdempotent_coeff,
        Finset.sum_eq_single_of_mem ζ0 (Finset.mem_univ _) (fun b _ hb => if_neg (fun e => hb (hj e))), if_pos rfl,
        ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    · have h0 : (v0eZ j ε).coeff u = 0 := by
        rw [centralIdempotent_coeff]
        exact Finset.sum_eq_zero fun ζ _ => if_neg fun e => hu ⟨ζ, e⟩
      rw [h0, mul_zero, zero_smul]
      show (formGSD C Λ).orbFun d v _ = 0
      unfold GSD.orbFun
      rw [dif_neg]
      rintro ⟨⟨γ, h⟩, hg⟩
      obtain ⟨h', e1, -⟩ := Λ.normBy (ι u) (fun w => hι u w) h
      apply hu
      have hst : ((γ, h'.1 * ι u⁻¹) : UF X.E n × GLG X.E n SG) = ((1 : UF X.E n), ι u)⁻¹ * (γ, h.1) :=
        Prod.ext (by simp) (by simp only [Prod.snd_mul, Prod.snd_inv, map_inv]; exact e1.symm)
      have hg' : ((γ, h.1) : UF X.E n × GLG X.E n SG) • d = ((1 : UF X.E n), ι u) • d := hg
      obtain ⟨ζ, hζ⟩ := hfree γ h' u⁻¹ (by rw [hst, mul_smul, hg', inv_smul_smul])
      exact ⟨ζ⁻¹, by rw [map_inv, hζ, inv_inv]⟩
  have hterm : ∀ t s : A, ((trRep C Λ ι hι t φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V)
      (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (v0eZ j ε).coeff (t⁻¹ * s)) • v := by
    intro t s
    rw [trRep_apply, smul_smul, Prod.mk_mul_mk, one_mul, ← map_inv, ← map_mul, hval]
  have hall : ∀ s : A, ((((trRep C Λ ι hι).asAlgebraHom a) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V)
      (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v := by
    intro s
    rw [representation_asAlgebraHom_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hterm, smul_smul]
    rw [← Finset.sum_smul, coeff_mul_fin, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring
  intro hz
  apply ha
  have hc : ∀ s : A, (a * v0eZ j ε).coeff s = 0 := by
    intro s
    have h1 := hall s
    rw [hz] at h1
    have h2 : ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v = 0 := by
      rw [← h1]
      rfl
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)).resolve_left hcard
  rw [eq_sum_single (a * v0eZ j ε)]
  exact Finset.sum_eq_zero fun t _ => by rw [hc t, MonoidAlgebra.single_zero]

end Gen

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

def v0N (r : ℕ) (c : Fin n → κ) : Matrix (Fin n) (Fin n) κ :=
  Matrix.of fun a b => if r ≤ a.val ∧ b.val < r then c b else 0

theorem nilpotentBlock_apply (r : ℕ) (c : Fin n → κ) (a b : Fin n) : v0N κ r c a b = if r ≤ a.val ∧ b.val < r then c b else 0 := rfl

theorem nilpotentBlock_sq_eq_zero (r : ℕ) (c : Fin n → κ) : v0N κ r c * v0N κ r c = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [nilpotentBlock_apply, nilpotentBlock_apply]
  by_cases h1 : r ≤ a.val ∧ x.val < r
  · by_cases h2 : r ≤ x.val ∧ b.val < r
    · exact absurd h2.1 (Nat.not_le.mpr h1.2)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

def v0A (r : ℕ) (c : Fin n → κ) : GL (Fin n) κ where
  val := 1 + v0N κ r c
  inv := 1 - v0N κ r c
  val_inv := by
    have : (1 + v0N κ r c) * (1 - v0N κ r c) = 1 - v0N κ r c * v0N κ r c := by noncomm_ring
    rw [this, nilpotentBlock_sq_eq_zero, sub_zero]
  inv_val := by
    have : (1 - v0N κ r c) * (1 + v0N κ r c) = 1 - v0N κ r c * v0N κ r c := by noncomm_ring
    rw [this, nilpotentBlock_sq_eq_zero, sub_zero]

variable {κ}

theorem perm_lt_iff_lt {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n))
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (b : Fin n) : (s b).val < r ↔ b.val < r := by
  rw [← coarse_eq_zero (bl := bl), hco, coarse_eq_zero]

theorem lt_iff_perm_inv_lt {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n))
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (b : Fin n) : (s⁻¹ b).val < r ↔ b.val < r := by
  rw [← perm_lt_iff_lt s hco (s⁻¹ b), show s (s⁻¹ b) = b by simp]

theorem conj_nilpotent_scalar_relation {r : ℕ} {bl : List ℕ} (c : Fin n → κ) (s : Equiv.Perm (Fin n)) (u : Fin n → κ)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (M : Matrix (Fin n) (Fin n) κ)
    (hM : ∀ a b, M a b = if a = s b then u b else 0) (h : GL (Fin n) κ) (hh : h ∈ blockUT n κ r bl)
    (e : (v0A κ r c).1 * h.1 = M * (v0A κ r c).1) (a i : Fin n) (ha : r ≤ a.val) (hi : i.val < r) :
    c (s i) * u i = u (s⁻¹ a) * c i := by
  have e' : ∀ a' c', h.1 a' c' + ∑ b, v0N κ r c a' b * h.1 b c' =
      M a' c' + u (s⁻¹ a') * v0N κ r c (s⁻¹ a') c' := by
    intro a' c'
    have := congrFun (congrFun e a') c'
    change ((1 + v0N κ r c) * h.1) a' c' = (M * (1 + v0N κ r c)) a' c' at this
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.mul_apply] at this
    rw [this]
    congr 1
    rw [Finset.sum_eq_single (s⁻¹ a')]
    · rw [hM, if_pos (by simp)]
    · intro b _ hb
      rw [hM, if_neg (fun h' => hb (by rw [h']; simp)), zero_mul]
    · simp
  have hrow : ∀ b : Fin n, b.val < r → h.1 b i = M b i := by
    intro b hb
    have h1 := e' b i
    have h2 : ∑ x, v0N κ r c b x * h.1 x i = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr hb)), zero_mul]
    rw [h2, nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr ((lt_iff_perm_inv_lt s hco b).mpr hb))), mul_zero,
      add_zero, add_zero] at h1
    exact h1
  have h1 := e' a i
  have hsi : (s i).val < r := (perm_lt_iff_lt s hco i).mpr hi
  have h3 : h.1 a i = 0 := by
    apply mem_btG.mp hh
    rw [coarse_of_lt hi, coarse_of_le ha]
    omega
  have h4 : M a i = 0 := by
    rw [hM, if_neg]
    intro hc
    rw [hc] at ha
    omega
  have h5 : ∑ x, v0N κ r c a x * h.1 x i = c (s i) * u i := by
    rw [Finset.sum_eq_single (s i)]
    · rw [nilpotentBlock_apply, if_pos ⟨ha, hsi⟩, hrow _ hsi, hM, if_pos rfl]
    · intro b _ hb
      rw [nilpotentBlock_apply]
      by_cases hb' : b.val < r
      · rw [if_pos ⟨ha, hb'⟩, hrow b hb', hM, if_neg hb, mul_zero]
      · rw [if_neg (fun hh => hb' hh.2), zero_mul]
    · simp
  have hsa : r ≤ (s⁻¹ a).val := Nat.not_lt.mp fun hc => absurd ((lt_iff_perm_inv_lt s hco a).mp hc) (Nat.not_lt.mpr ha)
  rw [h3, h4, h5, nilpotentBlock_apply, if_pos ⟨hsa, hi⟩, zero_add, zero_add] at h1
  exact h1

theorem permutation_commutes_nilpotent {r : ℕ} (c : Fin n → κ) (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b) (x : κ) :
    (x • pM κ s) * (v0A κ r c).1 = (v0A κ r c).1 * (x • pM κ s) := by
  have hPN : pM κ s * v0N κ r c = v0N κ r c * pM κ s := by
    ext a b
    rw [mul_pM_apply, pM_mul_apply, nilpotentBlock_apply, nilpotentBlock_apply]
    have h1 : r ≤ (s⁻¹ a).val ↔ r ≤ a.val := by
      have := nz_ge_of_fix s hfix (s⁻¹ a)
      rw [show s (s⁻¹ a) = a by simp] at this
      exact this.symm
    by_cases hb : b.val < r
    · rw [hfix b hb]
      by_cases ha : r ≤ a.val
      · rw [if_pos ⟨h1.mpr ha, hb⟩, if_pos ⟨ha, hb⟩]
      · rw [if_neg (fun hh => ha (h1.mp hh.1)), if_neg (fun hh => ha hh.1)]
    · have h2 : ¬ (s b).val < r := fun hc => by
        have := (nz_ge_of_fix s hfix b).mpr (Nat.not_lt.mp hb)
        omega
      rw [if_neg (fun hh => hb hh.2), if_neg (fun hh => h2 hh.2)]
  show (x • pM κ s) * (1 + v0N κ r c) = (1 + v0N κ r c) * (x • pM κ s)
  rw [mul_add, add_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul, hPN]

end StabComb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem normOne_mul {x y : 𝓞 E} (hx : star ((x : 𝓞 E) : E) * ((x : 𝓞 E) : E) = 1)
    (hy : star ((y : 𝓞 E) : E) * ((y : 𝓞 E) : E) = 1) : star (((x * y : 𝓞 E)) : E) * (((x * y : 𝓞 E)) : E) = 1 := by
  have h : (((x * y : 𝓞 E)) : E) = ((x : 𝓞 E) : E) * ((y : 𝓞 E) : E) := by push_cast; rfl
  rw [h, star_mul, mul_assoc, ← mul_assoc (star ((x : 𝓞 E) : E)), hx, one_mul, hy]

theorem normOne_conj {x x' : 𝓞 E} (hx : star ((x : 𝓞 E) : E) * ((x : 𝓞 E) : E) = 1)
    (hx' : ((x' : 𝓞 E) : E) = star ((x : 𝓞 E) : E)) : star ((x' : 𝓞 E) : E) * ((x' : 𝓞 E) : E) = 1 := by
  rw [hx', star_star, mul_comm, hx]

theorem normOne_integer_is_torsion (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {z : 𝓞 E}
    (hz : star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1) :
    ∃ ζ : NumberField.Units.torsion E, (((ζ : (𝓞 E)ˣ) : 𝓞 E)) = z := by
  obtain ⟨z', hz', -⟩ := nz_exists_inv hz
  let u : (𝓞 E)ˣ := ⟨z, z', by rw [mul_comm]; exact hz', hz'⟩
  refine ⟨⟨u, (NumberField.Units.mem_torsion E).mpr fun w => ?_⟩, rfl⟩
  have h1 := congrArg w.embedding hz
  rw [map_mul, hconj, map_one] at h1
  have h2 : ‖w.embedding ((z : 𝓞 E) : E)‖ ^ 2 = 1 := by
    have h3 : ((Complex.normSq (w.embedding ((z : 𝓞 E) : E)) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h1
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h3
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

end Stab

section StabPt

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}

open Classical in

def v0Fr (pos : Equiv.Perm (Fin n)) (r : ℕ) (c : Fin n → 𝓞 X.E) (w1 : SG) : GLG X.E n SG := fun w =>
  if w = w1 then (v0A _ r fun b => Ideal.Quotient.mk w.1.asIdeal (c b))⁻¹ * permGL _ pos⁻¹ else permGL _ pos⁻¹

theorem stabilizer_eq_scalar_mul_permMatrix (hX : X.Ok) (pos : Equiv.Perm (Fin n)) {r : ℕ} (bl : List ℕ) (hr : 0 < r) (hn : r < n)
    (c : Fin n → 𝓞 X.E) (w1 w2 : SG) (hne : w2 ≠ w1) (hc0 : ∀ i : Fin n, i.val < r → c i ∉ w1.1.asIdeal)
    (hc : ∀ i i' : Fin n, i.val < r → i'.val < r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
      c i' - z * c i ∈ w1.1.asIdeal → i' = i)
    {g1 : ℕ} (hg1 : g1.Prime) (hgw1 : (g1 : 𝓞 X.E) ∈ w1.1.asIdeal) (hb1 : 2 * X.f + 1 < g1)
    (γ : UF X.E n) (h : GLG X.E n SG) (h2 : h w2 ∈ blockUT n _ r bl) (h1 : h w1 ∈ blockUT n _ r bl)
    (e : (γ, h) • nzPt (v0Fr pos r c w1) = nzPt (v0Fr pos r c w1)) :
    ∃ (z : 𝓞 X.E) (s : Equiv.Perm (Fin n)), star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 ∧
      (∀ b : Fin n, b.val < r → s b = b) ∧ (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) ∧
      (∀ i j : Fin n, ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j =
        if i = (pos * s * pos⁻¹) j then algebraMap (𝓞 X.E) X.E z else 0) ∧
      ∀ (w : SG) (i j : Fin n), ((h w : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j =
        if i = s j then Ideal.Quotient.mk w.1.asIdeal z else 0 := by
  have : w1.1.asIdeal.IsPrime := w1.1.isPrime
  obtain ⟨G, hG, hh⟩ := nz_stab _ γ h e
  obtain ⟨s0, hs1, hs2⟩ := nz_monomial hX.conjE G (nz_unitary γ G hG)
  set s : Equiv.Perm (Fin n) := pos⁻¹ * s0 * pos with hs
  have hsa : ∀ a b : Fin n, a = s b ↔ pos a = s0 (pos b) := by
    intro a b
    rw [hs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
  set z : Fin n → 𝓞 X.E := fun b => G (s0 (pos b)) (pos b) with hz
  have hzu : ∀ b, star ((z b : 𝓞 X.E) : X.E) * ((z b : 𝓞 X.E) : X.E) = 1 := fun b => hs1 (pos b)
  have hGz : ∀ a b, G (pos a) (pos b) = if a = s b then z b else 0 := by
    intro a b
    by_cases hab : a = s b
    · rw [if_pos hab, hz]
      show G (pos a) (pos b) = G (s0 (pos b)) (pos b)
      rw [(hsa a b).mp hab]
    · rw [if_neg hab]
      exact hs2 _ _ fun hc => hab ((hsa a b).mpr hc)
  let Gh : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹
  have hGh : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal (z b) else 0 := by
    intro w a b
    have e1 : ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w).1 = G.map (Ideal.Quotient.mk w.1.asIdeal) := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hh w, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (Gh w).1 = pM _ pos⁻¹ * G.map (Ideal.Quotient.mk w.1.asIdeal) * pM _ pos := by
      show (permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹).1 = _
      rw [Units.val_mul, Units.val_mul, e1, ← map_inv, inv_inv]
      rfl
    rw [e2, mul_pM_apply, pM_mul_apply, inv_inv, Matrix.map_apply, hGz]
    split_ifs <;> simp
  have hGhw : ∀ w : SG, w ≠ w1 → Gh w = h w := by
    intro w hw
    show permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹ = h w
    have : v0Fr (X := X) pos r c w1 w = permGL _ pos⁻¹ := if_neg hw
    rw [this]
    group
  have hne0 : ∀ (w : SG) (b : Fin n), Ideal.Quotient.mk w.1.asIdeal (z b) ≠ 0 := fun w b hc =>
    nz_unit_notMem (hzu b) w.1 (Ideal.Quotient.eq_zero_iff_mem.mp hc)
  have hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val := by
    intro b
    refine nz_perm_of_le (φ := fun b : Fin n => coarse r bl b.val) s (fun b => ?_) b
    by_contra hcon
    have h0 := mem_btG.mp h2 (s b) b (Nat.lt_of_not_le hcon)
    rw [← hGhw w2 hne, hGh, if_pos rfl] at h0
    exact hne0 w2 b h0
  have hA : v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b)) * h w1 =
      Gh w1 * v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b)) := by
    show _ = permGL _ pos⁻¹ * ((v0Fr pos r c w1 w1)⁻¹ * h w1 * v0Fr pos r c w1 w1) * (permGL _ pos⁻¹)⁻¹ * _
    have : v0Fr (X := X) pos r c w1 w1 =
        (v0A _ r fun b => Ideal.Quotient.mk w1.1.asIdeal (c b))⁻¹ * permGL _ pos⁻¹ := if_pos rfl
    rw [this]
    group
  set Q := Ideal.Quotient.mk w1.1.asIdeal with hQ
  have key : ∀ a i : Fin n, r ≤ a.val → i.val < r → Q (c (s i)) * Q (z i) = Q (z (s⁻¹ a)) * Q (c i) :=
    fun a i ha hi => conj_nilpotent_scalar_relation (fun b => Q (c b)) s (fun b => Q (z b)) hco (Gh w1).1 (hGh w1) (h w1) h1
      (by rw [← Units.val_mul, ← Units.val_mul, hA]) a i ha hi
  have hci : ∀ i : Fin n, i.val < r → Q (c i) ≠ 0 := fun i hi h0 => hc0 i hi (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  let i0 : Fin n := ⟨0, lt_trans hr hn⟩
  let a0 : Fin n := ⟨r, hn⟩
  have hi0 : i0.val < r := hr
  have ha0 : r ≤ a0.val := le_refl r
  have hzb : ∀ b : Fin n, r ≤ b.val → Q (z b) = Q (z (s⁻¹ a0)) := by
    intro b hb
    have hsb : r ≤ (s b).val := Nat.not_lt.mp fun hc => absurd ((perm_lt_iff_lt s hco b).mp hc) (Nat.not_lt.mpr hb)
    have k1 := key (s b) i0 hsb hi0
    have k2 := key a0 i0 ha0 hi0
    rw [show s⁻¹ (s b) = b by simp] at k1
    exact mul_right_cancel₀ (hci i0 hi0) (k1.symm.trans k2)
  have hsi : ∀ i : Fin n, i.val < r → s i = i := by
    intro i hi
    obtain ⟨zi', hzi', hzi'c⟩ := nz_exists_inv (hzu i)
    have k := key a0 i ha0 hi
    refine hc i (s i) hi ((perm_lt_iff_lt s hco i).mpr hi) (z (s⁻¹ a0) * zi')
      (normOne_mul (hzu _) (normOne_conj (hzu i) hzi'c)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul]
    have hq : Q zi' * Q (z i) = 1 := by rw [← map_mul, hzi', map_one]
    linear_combination (Q zi') * k - (Q (c (s i))) * hq
  have hzi : ∀ i : Fin n, i.val < r → Q (z i) = Q (z (s⁻¹ a0)) := by
    intro i hi
    have k := key a0 i ha0 hi
    rw [hsi i hi, mul_comm (Q (z (s⁻¹ a0)))] at k
    exact mul_left_cancel₀ (hci i hi) k
  have hQall : ∀ b : Fin n, Q (z b) = Q (z (s⁻¹ a0)) := fun b =>
    if hb : b.val < r then hzi b hb else hzb b (Nat.not_lt.mp hb)
  set Z := z (s⁻¹ a0) with hZ
  have hzall : ∀ b : Fin n, z b = Z := by
    intro b
    obtain ⟨Z', hZ', hZ'c⟩ := nz_exists_inv (hzu (s⁻¹ a0))
    have h1' : z b * Z' = 1 :=
      nz_root_one hX w1.1 hg1 hgw1 hb1 (normOne_mul (hzu b) (normOne_conj (hzu _) hZ'c))
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hQ, hQall b, ← map_mul, mul_comm, hZ', map_one, sub_self])
    calc z b = z b * Z' * Z := by rw [mul_assoc, hZ', mul_one]
      _ = Z := by rw [h1', one_mul]
  have hGp : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal Z else 0 :=
    fun w a b => by rw [hGh, hzall]
  have hGw1 : Gh w1 = h w1 := by
    have hcm : Gh w1 * v0A _ r (fun b => Q (c b)) = v0A _ r (fun b => Q (c b)) * Gh w1 := by
      have hGm : (Gh w1).1 = Q Z • pM _ s := by
        ext a b
        rw [hGp, Matrix.smul_apply, pM_apply, smul_eq_mul]
        split_ifs <;> simp [hQ]
      apply Units.ext
      show (Gh w1).1 * (v0A _ r (fun b => Q (c b))).1 = (v0A _ r (fun b => Q (c b))).1 * (Gh w1).1
      rw [hGm]
      exact permutation_commutes_nilpotent _ s hsi _
    exact (mul_left_cancel (hA.trans hcm)).symm
  refine ⟨Z, s, hzu _, hsi, hco, fun i j => ?_, fun w i j => ?_⟩
  · rw [nz_ufGL_apply, ← hG]
    have h3 := hGz (pos⁻¹ i) (pos⁻¹ j)
    rw [show pos (pos⁻¹ i) = i by simp, show pos (pos⁻¹ j) = j by simp, hzall] at h3
    rw [h3]
    have h4 : pos⁻¹ i = s (pos⁻¹ j) ↔ i = (pos * s * pos⁻¹) j := by
      show pos⁻¹ i = s (pos⁻¹ j) ↔ i = pos (s (pos⁻¹ j))
      exact Equiv.Perm.inv_eq_iff_eq
    by_cases h5 : pos⁻¹ i = s (pos⁻¹ j)
    · rw [if_pos h5, if_pos (h4.mp h5)]
    · rw [if_neg h5, if_neg (fun hc => h5 (h4.mpr hc)), map_zero]
  · by_cases hw : w = w1
    · subst hw
      rw [← hGw1, hGp]
    · rw [← hGhw w hw, hGp]

end StabPt

section Scal

variable {E : Type} [Field E] [NumberField E]

noncomputable instance unitTorsionFintype : Fintype (NumberField.Units.torsion E) := Fintype.ofFinite _

def unitsReductionAtPlace (w : HeightOneSpectrum (𝓞 E)) : (𝓞 E)ˣ →* (𝓞 E ⧸ w.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom

def diagonalUnitsHom (κ : Type) [CommRing κ] (n : ℕ) : (Fin n → κˣ) →* GL (Fin n) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem v0diag_val (κ : Type) [CommRing κ] (n : ℕ) (u : Fin n → κˣ) :
    ((diagonalUnitsHom κ n u : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((u i : κˣ) : κ) := rfl

theorem v0diag_mem_btG (κ : Type) [CommRing κ] (n : ℕ) (β : ℕ → ℕ) (u : Fin n → κˣ) : diagonalUnitsHom κ n u ∈ btG n κ β := by
  refine mem_btG.mpr fun i j hij => ?_
  rw [v0diag_val, Matrix.diagonal_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

def v0Z (V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : NumberField.Units.torsion E →* G0 E V r :=
  MonoidHom.pi fun w => (diagonalUnitsHom _ r).comp (MonoidHom.pi fun _ : Fin r => (unitsReductionAtPlace w.1).comp (NumberField.Units.torsion E).subtype)

open Classical in

def v0kG (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : NumberField.Units.torsion E →* GLG E n SG :=
  MonoidHom.pi fun w => (diagonalUnitsHom _ n).comp (MonoidHom.pi fun i : Fin n =>
    if w.1 ∈ V ∧ i.val < r then 1 else (unitsReductionAtPlace w.1).comp (NumberField.Units.torsion E).subtype)

open Classical in
theorem torsionLevelElement_apply (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) (ζ : NumberField.Units.torsion E) (w : SG) (i j : Fin n) :
    Units.val (v0kG n SG V r ζ w) i j =
      if i = j then (if w.1 ∈ V ∧ i.val < r then 1 else Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E)) else 0 := by
  show Units.val (diagonalUnitsHom (𝓞 E ⧸ w.1.asIdeal) n _) i j = _
  rw [v0diag_val, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hc : w.1 ∈ V ∧ i.val < r
    · simp [hc]
    · simp [hc, unitsReductionAtPlace]
  · simp [hij]

end Scal

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

theorem torsionLevelElement_mem_X (ζ : NumberField.Units.torsion X.E) :
    v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r ζ ∈ (rowTyKK Ch sel mu).inv.grp := by
  intro w _
  show _ ∈ (rowTyKK Ch sel mu w).H
  by_cases h : w.1 ∈ Pr.vGs
  · rw [rowTyKK, LevFam.glue_of_mem _ _ w h]
    show _ ∈ HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t)
    refine mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩
    rw [torsionLevelElement_apply]
    by_cases hij : i = i'
    · subst hij
      simp [h, hi]
    · rw [if_neg hij, Matrix.one_apply_ne hij]
  · rw [rowTyKK, LevFam.glue_of_not _ _ w h]
    exact v0diag_mem_btG _ _ _ _

def v0kX : NumberField.Units.torsion X.E →* ↥(rowTyKK Ch sel mu).inv.grp :=
  (v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r).codRestrict _ (torsionLevelElement_mem_X Ch sel mu)

def v0cX : NumberField.Units.torsion X.E →* X.Kˣ :=
  ∏ τ : X.Tau, (zpowGroupHom (∑ i, (W.sgTrue τ).w i)).comp
    ((Units.map (X.emb τ).toMonoidHom).comp ((Units.map (algebraMap (𝓞 X.E) X.E).toMonoidHom).comp (NumberField.Units.torsion X.E).subtype))

def torsionScalarCharacterAtBase : NumberField.Units.torsion X.E →* X.Kˣ :=
  ((rowTyKK Ch sel mu).inv.chr.comp (v0kX Ch sel mu)) * v0cX W

def RegModZX : Prop :=
  ∀ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r),
    a * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) ≠ 0 → (g0HatRepEqFunX W Ch sel mu).asAlgebraHom a ≠ 0

def InvariantSubspaceNonzeroAtBase (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  goodAt Xg P.grp P.chr * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) ≠ 0 → V0X W Ch sel mu Xg P ≠ ⊥

theorem invariantSubspaceNonzeroX_of_regular (h : RegModZX W Ch sel mu) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) :
    InvariantSubspaceNonzeroAtBase W Ch sel mu Xg P := by
  intro hne hbot
  exact h _ hne (LinearMap.range_eq_bot.mp hbot)

open Classical in

theorem torsionLevelElement_mem_V (j : ℕ) (ζ : NumberField.Units.torsion X.E) :
    v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r ζ ∈ (mtTyKK Ch sel mu j).inv.grp := by
  intro w _
  show _ ∈ (mtTyKK Ch sel mu j w).H
  by_cases h : w.1 ∈ Pr.vGs
  · rw [mtTyKK, LevFam.glue_of_mem _ _ w h]
    show _ ∈ HK R.nV _ R.r [R.t]
    refine mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩
    rw [torsionLevelElement_apply]
    by_cases hij : i = i'
    · subst hij
      simp [h, hi]
    · rw [if_neg hij, Matrix.one_apply_ne hij]
  · rw [mtTyKK, LevFam.glue_of_not _ _ w h]
    exact v0diag_mem_btG _ _ _ _

def v0kV (j : ℕ) : NumberField.Units.torsion X.E →* ↥(mtTyKK Ch sel mu j).inv.grp :=
  (v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r).codRestrict _ (torsionLevelElement_mem_V Ch sel mu j)

def v0cV (j : ℕ) : NumberField.Units.torsion X.E →* X.Kˣ :=
  ∏ τ : X.Tau, (zpowGroupHom (-∑ i, (W.lamV j τ).w i)).comp
    ((Units.map (X.emb τ).toMonoidHom).comp ((Units.map (algebraMap (𝓞 X.E) X.E).toMonoidHom).comp (NumberField.Units.torsion X.E).subtype))

def torsionScalarCharacterAtLevel (j : ℕ) : NumberField.Units.torsion X.E →* X.Kˣ :=
  ((mtTyKK Ch sel mu j).inv.chr.comp (v0kV Ch sel mu j)) * v0cV W j

def RegModZV (j : ℕ) : Prop :=
  ∀ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r),
    a * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) ≠ 0 → (unipotentRightActionFormsV W Ch sel mu j).asAlgebraHom a ≠ 0

def InvariantSubspaceNonzeroAtLevel (j : ℕ) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  goodAt Xg P.grp P.chr⁻¹ * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) ≠ 0 → invariantSubspaceOfForms W Ch sel mu j Xg P ≠ ⊥

theorem invariantSubspaceNonzeroV_of_regular (j : ℕ) (h : RegModZV W Ch sel mu j) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K))
    (P : LevFam X.E X.K R.r Pr.vGs) : InvariantSubspaceNonzeroAtLevel W Ch sel mu j Xg P := by
  intro hne hbot
  exact h _ hne (LinearMap.range_eq_bot.mp hbot)

end Rows

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem torsion_normOne (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (ζ : NumberField.Units.torsion E) :
    star ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) * ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have h1 := (NumberField.Units.mem_torsion E).mp ζ.2 w
  rw [← NumberField.InfinitePlace.norm_embedding_eq] at h1
  apply w.embedding.injective
  rw [map_mul, hconj, map_one, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h1]
  norm_num

def v0uE (ζ : NumberField.Units.torsion E) : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom (ζ : (𝓞 E)ˣ)

theorem torsionUnit_val (ζ : NumberField.Units.torsion E) : ((v0uE ζ : Eˣ) : E) = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) := rfl

def v0sc (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) : UF E n :=
  ⟨LinearEquiv.smulOfUnit (v0uE ζ), fun x y => by
    have hu := torsion_normOne hconj ζ
    show hStd E n ((v0uE ζ : Eˣ) • x) ((v0uE ζ : Eˣ) • y) = hStd E n x y
    rw [hStd_apply, hStd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, star_mul', torsionUnit_val]
    linear_combination (star (x i) * y i) * hu⟩

theorem torsionScalar_apply (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) (x : Sp E n) :
    (v0sc hconj n ζ).1 x = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) • x := rfl

theorem torsionScalar_symm_apply (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) {z' : 𝓞 E} (hz' : z' * ((ζ : (𝓞 E)ˣ) : 𝓞 E) = 1) (x : Sp E n) :
    (v0sc hconj n ζ).1.symm x = z' • x := by
  apply (v0sc hconj n ζ).1.injective
  rw [LinearEquiv.apply_symm_apply, torsionScalar_apply, ← algebraMap_smul E z' x, smul_smul, ← map_mul, mul_comm, hz', map_one,
    one_smul]

theorem torsionLevelElement_scalar_val (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (ζ : NumberField.Units.torsion E) (w : SG) :
    Units.val (v0kG n SG ∅ 0 ζ w) = Matrix.diagonal fun _ => Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E) := by
  ext i j
  rw [torsionLevelElement_apply, Matrix.diagonal_apply]
  simp

theorem torsionScalar_fixes_decoration (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {n : ℕ}
    {SG : Finset (HeightOneSpectrum (𝓞 E))} (ζ : NumberField.Units.torsion E) (d : DecoSet E n ∅ SG) :
    ((v0sc hconj n ζ, v0kG n SG ∅ 0 ζ) : UF E n × GLG E n SG) • d = d := by
  obtain ⟨z', hz'1, -⟩ := nz_exists_inv (torsion_normOne hconj ζ)
  set z : 𝓞 E := ((ζ : (𝓞 E)ˣ) : 𝓞 E) with hz
  have hzz : z * z' = 1 := by rw [mul_comm]; exact hz'1
  have hsymm := torsionScalar_symm_apply hconj n ζ hz'1
  apply Subtype.ext
  show d.1.act (v0sc hconj n ζ).1 (v0kG n SG ∅ 0 ζ) = d.1
  ext1
  · show gmap _ d.1.N = d.1.N
    ext x
    rw [mem_gmap, hsymm]
    constructor
    · intro h
      have := d.1.N.smul_mem z h
      rwa [smul_smul, hzz, one_smul] at this
    · intro h
      exact d.1.N.smul_mem z' h
  · funext P
    exact (Finset.notMem_empty P.1 P.2).elim
  · funext w x
    show (v0kG n SG ∅ 0 ζ w).1.mulVec (d.1.be w ((v0sc hconj n ζ).1.symm x)) = d.1.be w x
    rw [hsymm, torsionLevelElement_scalar_val]
    by_cases hx : x ∈ d.1.at w.1
    · rw [d.2.be_smul w z' x hx]
      funext i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hzz, map_one, one_mul]
    · have hx' : z' • x ∉ d.1.at w.1 := fun h => hx (by
        have := (d.1.at w.1).smul_mem z h
        rwa [smul_smul, hzz, one_smul] at this)
      rw [d.2.be_off w _ hx', d.2.be_off w x hx, Matrix.mulVec_zero]

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

section RhoScal2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n]

theorem embeddedGL_torsionScalar (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (emb : ι → (E →+* K))
    (ζ : NumberField.Units.torsion E) :
    embGL emb (ufGL E n (v0sc hconj n ζ)) = fun τ => brpSc K (Units.map (emb τ).toMonoidHom (v0uE ζ)) := by
  funext τ
  apply Units.ext
  ext i j
  show (RingHom.mapMatrix (emb τ) ((ufGL E n (v0sc hconj n ζ) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) i j = _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, nz_ufGL_apply, torsionScalar_apply, brpSc_coe]
  by_cases hij : i = j
  · subst hij
    simp [torsionUnit_val]
  · simp [hij]

omit [NeZero n] in
theorem inverseTranspose_scalars (t : ι → Kˣ) :
    invTrK (fun τ => (brpSc K (t τ) : GL (Fin n) K)) = fun τ => (brpSc K (t τ)⁻¹ : GL (Fin n) K) := by
  funext τ
  apply Units.ext
  show ((((brpSc K (t τ))⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).transpose = _
  have e : (brpSc K (t τ))⁻¹ = (brpSc K (t τ)⁻¹ : GL (Fin n) K) := by
    unfold brpSc
    rw [map_inv]
  rw [e, brpSc_coe, Matrix.transpose_smul, Matrix.transpose_one]

end RhoScal2

section RowsScal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem torsionCenter_val (V : Finset (HeightOneSpectrum (𝓞 X.E))) (r : ℕ) (ζ : NumberField.Units.torsion X.E) (w : V) :
    Units.val (v0Z V r ζ w) = Matrix.diagonal fun _ => Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 X.E)ˣ) : 𝓞 X.E) := by
  show Units.val (diagonalUnitsHom (𝓞 X.E ⧸ w.1.asIdeal) r _) = _
  rw [v0diag_val]
  rfl

open Classical in
theorem torsionLevelElement_diagonal (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 X.E))) (r : ℕ) (ζ : NumberField.Units.torsion X.E) (w : SG) :
    Units.val (v0kG n SG V r ζ w) =
      Matrix.diagonal fun i : Fin n => if w.1 ∈ V ∧ i.val < r then 1 else Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 X.E)ˣ) : 𝓞 X.E) := by
  ext i j
  rw [torsionLevelElement_apply, Matrix.diagonal_apply]

theorem diagonalBlock_scalar {κ : Type} [CommRing κ] {r n : ℕ} (x : κ) :
    diagMat r n (Matrix.diagonal fun _ : Fin r => x) = Matrix.diagonal fun i : Fin n => if i.val < r then x else 1 := by
  ext i j
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [diagMat_of_lt _ hi hj, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp [hi]
      · rw [if_neg (fun e => hij (Fin.ext (by simpa using congrArg Fin.val e))), if_neg hij]
    · have hne : i ≠ j := fun e => hj (by rw [← e]; exact hi)
      rw [diagMat_of_not_right _ _ hj, Matrix.diagonal_apply, Matrix.one_apply_ne hne, if_neg hne]
  · rw [diagMat_of_not_left _ _ hi, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hi]
    · simp [hij]

open Classical in

theorem unipotentHat_mul_torsionLevel {n : ℕ} (h : R.r ≤ n) (ζ : NumberField.Units.torsion X.E) :
    unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) * v0kG n (rowSG Pr sel mu) Pr.vGs R.r ζ = v0kG n (rowSG Pr sel mu) ∅ 0 ζ := by
  funext w
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, torsionLevelElement_diagonal, torsionLevelElement_diagonal]
  by_cases hw : w.1 ∈ Pr.vGs
  · have e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = diagEmb _ h (v0Z Pr.vGs R.r ζ ⟨w.1, hw⟩) := extGLG_of_mem _ w hw
    rw [e, diagEmb_val, torsionCenter_val, diagonalBlock_scalar, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i.val < R.r
    · simp [hi, hw]
    · simp [hi]
  · have e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = 1 := extGLG_of_not _ w hw
    rw [e, Units.val_one, one_mul]
    congr 1
    funext i
    simp [hw]

theorem torsion_scalar_acts_X (hX : X.Ok) (ζ : NumberField.Units.torsion X.E) :
    (rowVal W (rowSG Pr sel mu)).rho (v0sc hX.conjE (R.N R.m - 1) ζ) = ((v0cX W ζ : X.Kˣ) : X.K) • 1 := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  show rhoK W.sgTrue (embGL X.emb (ufGL X.E _ (v0sc hX.conjE (R.N R.m - 1) ζ))) = _
  rw [embeddedGL_torsionScalar, tensorWeights_scalar_action, v0cX, MonoidHom.finsetProd_apply, Units.coe_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  rfl

theorem torsion_scalar_acts_V (hX : X.Ok) (j : ℕ) (ζ : NumberField.Units.torsion X.E) :
    (mtVal W j (rowSG Pr sel mu)).rho (v0sc hX.conjE R.nV ζ) = ((v0cV W j ζ : X.Kˣ) : X.K) • 1 := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  show rhoK (W.lamV j) (invTrK (embGL X.emb (ufGL X.E _ (v0sc hX.conjE R.nV ζ)))) = _
  rw [embeddedGL_torsionScalar, inverseTranspose_scalars, tensorWeights_scalar_action, v0cV, MonoidHom.finsetProd_apply, Units.coe_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow',
    zpow_neg]
  rfl

theorem torsionCenter_scalar_X (hX : X.Ok) (ζ : NumberField.Units.torsion X.E) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    g0HatRepEqFunX W Ch sel mu (v0Z Pr.vGs R.r ζ) φ = ((torsionScalarCharacterAtBase W Ch sel mu ζ : X.Kˣ) : X.K) • φ := by
  apply Subtype.ext
  funext d
  have hk := unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_X' R) ζ
  have e1 : (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) =
      (v0sc hX.conjE _ ζ, v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r ζ) *
        (v0sc hX.conjE _ ζ, v0kG (R.N R.m - 1) (rowSG Pr sel mu) ∅ 0 ζ)⁻¹ := by
    rw [← hk]
    ext <;> simp [mul_inv_rev]
  have hfx := torsionScalar_fixes_decoration hX.conjE ζ d
  have h2 := φ.2 ((v0sc hX.conjE _ ζ, v0kX Ch sel mu ζ) : (mtildeKGSD W Ch sel mu).G) d
  show φ.1 (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _
  rw [e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]
  refine h2.trans ?_
  show (((rowTyKK Ch sel mu).inv.chr (v0kX Ch sel mu ζ) : X.Kˣ) : X.K) •
    (rowVal W (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _
  rw [torsion_scalar_acts_X W sel mu hX ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]
  congr 1

theorem torsionCenter_scalar_V (hX : X.Ok) (j : ℕ) (ζ : NumberField.Units.torsion X.E) (φ : (mtKGSD W Ch sel mu j).EqFun) :
    unipotentRightActionFormsV W Ch sel mu j (v0Z Pr.vGs R.r ζ) φ = ((torsionScalarCharacterAtLevel W Ch sel mu j ζ : X.Kˣ) : X.K) • φ := by
  apply Subtype.ext
  funext d
  have hk := unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_nV R) ζ
  have e1 : (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) :
      UF X.E R.nV × GLG X.E R.nV (rowSG Pr sel mu)) =
      (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r ζ) *
        (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) ∅ 0 ζ)⁻¹ := by
    rw [← hk]
    ext <;> simp [mul_inv_rev]
  have hfx := torsionScalar_fixes_decoration hX.conjE ζ d
  have h2 := φ.2 ((v0sc hX.conjE _ ζ, v0kV Ch sel mu j ζ) : (mtKGSD W Ch sel mu j).G) d
  show φ.1 (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _
  rw [e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]
  refine h2.trans ?_
  show (((mtTyKK Ch sel mu j).inv.chr (v0kV Ch sel mu j ζ) : X.Kˣ) : X.K) •
    (mtVal W j (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _
  rw [torsion_scalar_acts_V W sel mu hX j ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]
  congr 1

end RowsScal

section LamKEv

theorem levelCharacter_permutation_eq_one {κ K : Type} [CommRing κ] [Field K] {n r : ℕ} (bl : List ℕ) (χ : ℕ → κˣ →* Kˣ)
    (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (hχ : ∀ (c : ℕ) (ε : ℤˣ), χ c (sgnU κ ε) = 1) :
    (⟨HK n κ r bl, lamK χ n r bl⟩ : Lev κ K n).ev (permGL κ s) = 1 := by
  have hm : permGL κ s ∈ HK n κ r bl := by
    refine mem_HK.mpr ⟨nz_pM_bt κ s hco, fun i j hi _ => ?_⟩
    rw [permGL_val, pM_apply, Matrix.one_apply, hfix j ‹_›]
  rw [Lev.ev_of_mem _ hm]
  show detChar χ n r bl ⟨permGL κ s, HK_le_blockUT n κ r bl hm⟩ = 1
  rw [detChar_apply]
  refine Finset.prod_eq_one fun c _ => ?_
  obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse r bl) s hco (c + 1)
  rw [hε κ, hχ]

end LamKEv

section RowsMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in
theorem character_permutation_X_trivial (hPr : Pr.Ok) (hCh : Ch.Ok) (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (s : Equiv.Perm (Fin (R.N R.m - 1)))
    (hfix : ∀ b : Fin (R.N R.m - 1), b.val < R.r → s b = b)
    (hco : ∀ b : Fin (R.N R.m - 1), coarse R.r (List.replicate R.m R.t) (s b).val = coarse R.r (List.replicate R.m R.t) b.val)
    (h : ↥(rowTyKK Ch sel mu).inv.grp) (hh : ∀ w, h.1 w = permGL _ s) : (rowTyKK Ch sel mu).inv.chr h = 1 := by
  obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix
  have key : ∀ w : rowSG Pr sel mu, ((rowTyKK Ch sel mu).inv w).ev (h.1 w) =
      if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε) := by
    intro w
    rw [hh w]
    show ((rowTyKK Ch sel mu w).inv).ev _ = _
    rw [Lev.inv_ev]
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [if_pos hw, rowTyKK, LevFam.glue_of_mem _ _ w hw]
      show ((⟨HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t),
        lamK (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.r (List.replicate R.m R.t)⟩ : Lev _ X.K _).ev _)⁻¹ = 1
      rw [levelCharacter_permutation_eq_one _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]
    · rw [if_neg hw, rowTyKK, LevFam.glue_of_not _ _ w hw]
      show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ :
        Lev _ X.K _).inv).ev _)⁻¹ = _
      rw [Lev.inv_ev, inv_inv, hε]
  rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]
  exact hξ.prod ε

open Classical in
theorem levelGroup_X_block (h : ↥(rowTyKK Ch sel mu).inv.grp) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) :
    h.1 w ∈ HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t) := by
  have hm : h.1 w ∈ ((rowTyKK Ch sel mu).inv w).H := (rowTyKK Ch sel mu).inv.mem_at h w
  have e : ((rowTyKK Ch sel mu).inv w).H = HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t) := by
    show (rowTyKK Ch sel mu w).H = _
    rw [rowTyKK, LevFam.glue_of_mem _ _ w hw]
    rfl
  rw [e] at hm
  exact hm

theorem restrict_eq_one_of_mem_blockLevel {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (bl : List ℕ) {M : GL (Fin n) κ} (hM : M ∈ HK n κ r bl) :
    restr hrn (M : Matrix (Fin n) (Fin n) κ) = 1 := by
  ext a b
  simp only [restr, Matrix.submatrix_apply]
  rw [(mem_HK.mp hM).2 _ _ a.2 b.2]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.one_apply_ne (fun e => hab (Fin.castLE_injective hrn e)), Matrix.one_apply_ne hab]

theorem restrict_diagonalBlock {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (g : Matrix (Fin r) (Fin r) κ) :
    restr hrn (diagMat r n g) = g := by
  ext a b
  simp only [restr, Matrix.submatrix_apply]
  rw [diagMat_of_lt _ (show (Fin.castLE hrn a).val < r from a.2) (show (Fin.castLE hrn b).val < r from b.2)]
  rfl

open Classical in

theorem regModZX_of (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hlam : ∃ w1 ∈ Pr.vG 0, ∃ c : ℕ → 𝓞 X.E, (∀ i < R.r, c i ∉ w1.asIdeal) ∧
      ∀ i i', i < R.r → i' < R.r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
        c i' - z * c i ∈ w1.asIdeal → i' = i) :
    RegModZX W Ch sel mu := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  obtain ⟨w1, h1, c, hc0, hc⟩ := hlam
  obtain ⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have hne : w2 ≠ w1 := fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  have hW12 : W2 ≠ W1 := fun h => hne (congrArg Subtype.val h)
  have hr : 0 < R.r := nz_r_pos R
  have hn : R.r < R.N R.m - 1 := by
    rw [rank_X'_eq R]
    have := Nat.mul_pos (by have := R.two_le_m; omega : 0 < R.m) (nz_t_pos R)
    omega
  let cF : Fin (R.N R.m - 1) → 𝓞 X.E := fun b => c b.val
  let bl := List.replicate R.m R.t
  have hstab := fun (γ : UF X.E (R.N R.m - 1)) (g : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))
      (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e =>
    stabilizer_eq_scalar_mul_permMatrix hX (posX R) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi)
      (fun i i' hi hi' z hz hm => Fin.ext (hc i.val i'.val hi hi' z hz hm)) (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) γ g hg2 hg1 e
  have hinj : Function.Injective (v0Z (E := X.E) Pr.vGs R.r) := by
    rw [injective_iff_map_eq_one]
    intro ζ hζ
    have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ
    simp only at e
    rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
    have h1' := nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ)
      (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])
    exact Subtype.ext (Units.ext h1')
  intro a ha
  refine trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (rowVal W (rowSG Pr sel mu)) (rowTyKK Ch sel mu).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R))
    (rowTyKK_inv_normBy_g0Hat Ch sel mu) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) hinj (torsionCenter_scalar_X W Ch sel mu hX)
    (nzPt (v0Fr (posX R) R.r cF W1)) (nzExt X.K W.sgTrue) (nzExt_ne_zero _ _) ?_ ?_ a ha
  · intro γ h e
    obtain ⟨z, s, hz, hsfix, hco, hγ, hhw⟩ := hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W2 m2))
      (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W1 m1)) e
    have hz1 : z = 1 := by
      have h0 := (mem_HK.mp (levelGroup_X_block Ch sel mu h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr
      rw [hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq] at h0
      exact nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])
    subst hz1
    have hγ' : ufGL X.E _ γ = permGL X.E (posX R * s * (posX R)⁻¹) := by
      apply Units.ext
      ext i j
      rw [hγ, permGL_val, pM_apply, map_one]
    have hh' : ∀ w, h.1 w = permGL _ s := fun w => by
      apply Units.ext
      ext i j
      rw [hhw, permGL_val, pM_apply, map_one]
    rw [character_permutation_X_trivial Ch sel mu hPr hCh hξ s hsfix hco h hh', Units.val_one, one_smul]
    show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _
    rw [hγ']
    have hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posX R ((posX R)⁻¹ x) = x := fun x => by simp
    apply nz_rhoV_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posX R)⁻¹ x).val < R.r
      · rw [hsfix _ hb, hx']
      · rw [nz_sg_const hW τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posX R)⁻¹ x).val < R.r := fun hb => hne' (by rw [hsfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro γ h t e
    have hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs),
        unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t w = diagEmb _ (r_le_X' R) (t ⟨w.1, hw⟩) := fun w hw => extGLG_of_mem _ w hw
    have hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) w ∈ blockUT _ _ R.r bl := by
      intro w hw
      rw [Pi.mul_apply, hD w hw]
      exact Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h w hw)) (diagEmb_mem_blockUT _ _ _)
    obtain ⟨z, s, hz, hsfix, -, -, hhw⟩ := hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) (hgb W2 m2) (hgb W1 m1) e
    obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hX.conjE hz
    refine ⟨ζ, funext fun w => ?_⟩
    let W' : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩
    have e2 : restr (r_le_X' R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) W')) = Units.val (t w) := by
      rw [Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_X' R) bl _ (diagEmb_mem_blockUT (r_le_X' R) bl (t ⟨w.1, w.2⟩)),
        restrict_eq_one_of_mem_blockLevel (r_le_X' R) bl (levelGroup_X_block Ch sel mu h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]
    apply Units.ext
    ext a b
    rw [torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]
    simp only [restr, Matrix.submatrix_apply]
    rw [hhw, hsfix _ (show (Fin.castLE (r_le_X' R) b).val < R.r from b.2)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => hab (Fin.castLE_injective (r_le_X' R) e)), if_neg hab]

end RowsMain

section RowsMainV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in
theorem character_permutation_V_trivial (hPr : Pr.Ok) (hCh : Ch.Ok) (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (j : ℕ) (s : Equiv.Perm (Fin R.nV))
    (hfix : ∀ b : Fin R.nV, b.val < R.r → s b = b)
    (hco : ∀ b : Fin R.nV, coarse R.r [R.t] (s b).val = coarse R.r [R.t] b.val)
    (h : ↥(mtTyKK Ch sel mu j).inv.grp) (hh : ∀ w, h.1 w = permGL _ s) : (mtTyKK Ch sel mu j).inv.chr h = 1 := by
  obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix
  have key : ∀ w : rowSG Pr sel mu, ((mtTyKK Ch sel mu j).inv w).ev (h.1 w) =
      (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹ := by
    intro w
    rw [hh w]
    show ((mtTyKK Ch sel mu j w).inv).ev _ = _
    rw [Lev.inv_ev]
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [if_pos hw, mtTyKK, LevFam.glue_of_mem _ _ w hw]
      show ((⟨HK R.nV _ R.r [R.t], lamK (fun _ => (chiAt Ch ⟨w.1, hw⟩ (j - 1))⁻¹) R.nV R.r [R.t]⟩ :
        Lev _ X.K _).ev _)⁻¹ = 1⁻¹
      rw [levelCharacter_permutation_eq_one _ _ s hfix hco (fun _ ε' => by rw [MonoidHom.inv_apply, nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1) ε', inv_one])]
    · rw [if_neg hw, mtTyKK, LevFam.glue_of_not _ _ w hw]
      show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _
      rw [hε]
  rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]

open Classical in
theorem levelGroup_V_block (j : ℕ) (h : ↥(mtTyKK Ch sel mu j).inv.grp) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) :
    h.1 w ∈ HK R.nV _ R.r [R.t] := by
  have hm : h.1 w ∈ ((mtTyKK Ch sel mu j).inv w).H := (mtTyKK Ch sel mu j).inv.mem_at h w
  have e : ((mtTyKK Ch sel mu j).inv w).H = HK R.nV _ R.r [R.t] := by
    show (mtTyKK Ch sel mu j w).H = _
    rw [mtTyKK, LevFam.glue_of_mem _ _ w hw]
    rfl
  rw [e] at hm
  exact hm

open Classical in

theorem regModZV_of (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hlam : ∃ w1 ∈ Pr.vG 0, ∃ c : ℕ → 𝓞 X.E, (∀ i < R.r, c i ∉ w1.asIdeal) ∧
      ∀ i i', i < R.r → i' < R.r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
        c i' - z * c i ∈ w1.asIdeal → i' = i) :
    RegModZV W Ch sel mu j := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  obtain ⟨w1, h1, c, hc0, hc⟩ := hlam
  obtain ⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have hne : w2 ≠ w1 := fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  have hW12 : W2 ≠ W1 := fun h => hne (congrArg Subtype.val h)
  have hr : 0 < R.r := nz_r_pos R
  have hn : R.r < R.nV := by
    show R.r < R.r + R.t
    have := nz_t_pos R
    omega
  let cF : Fin R.nV → 𝓞 X.E := fun b => c b.val
  let bl := [R.t]
  have hstab := fun (γ : UF X.E R.nV) (g : GLG X.E R.nV (rowSG Pr sel mu))
      (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e =>
    stabilizer_eq_scalar_mul_permMatrix hX (posV R j) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi)
      (fun i i' hi hi' z hz hm => Fin.ext (hc i.val i'.val hi hi' z hz hm)) (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) γ g hg2 hg1 e
  have hinj : Function.Injective (v0Z (E := X.E) Pr.vGs R.r) := by
    rw [injective_iff_map_eq_one]
    intro ζ hζ
    have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ
    simp only at e
    rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
    have h1' := nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ)
      (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])
    exact Subtype.ext (Units.ext h1')
  intro a ha
  refine trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (mtVal W j (rowSG Pr sel mu)) (mtTyKK Ch sel mu j).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R))
    (mtTyKK_inv_normBy_g0Hat Ch sel mu j) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) hinj (torsionCenter_scalar_V W Ch sel mu hX j)
    (nzPt (v0Fr (posV R j) R.r cF W1)) (nzExt X.K (W.lamV j)) (nzExt_ne_zero _ _) ?_ ?_ a ha
  · intro γ h e
    obtain ⟨z, s, hz, hsfix, hco, hγ, hhw⟩ := hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W2 m2))
      (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W1 m1)) e
    have hz1 : z = 1 := by
      have h0 := (mem_HK.mp (levelGroup_V_block Ch sel mu j h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr
      rw [hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq] at h0
      exact nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])
    subst hz1
    have hγ' : ufGL X.E _ γ = permGL X.E (posV R j * s * (posV R j)⁻¹) := by
      apply Units.ext
      ext i j
      rw [hγ, permGL_val, pM_apply, map_one]
    have hh' : ∀ w, h.1 w = permGL _ s := fun w => by
      apply Units.ext
      ext i j
      rw [hhw, permGL_val, pM_apply, map_one]
    rw [character_permutation_V_trivial Ch sel mu hPr hCh hξ j s hsfix hco h hh', Units.val_one, one_smul]
    show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _
    rw [hγ']
    have hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x := fun x => by simp
    apply nz_rhoVr_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posV R j)⁻¹ x).val < R.r
      · rw [hsfix _ hb, hx']
      · rw [nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posV R j)⁻¹ x).val < R.r := fun hb => hne' (by rw [hsfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro γ h t e
    have hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs),
        unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t w = diagEmb _ (r_le_nV R) (t ⟨w.1, hw⟩) := fun w hw => extGLG_of_mem _ w hw
    have hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) w ∈ blockUT _ _ R.r bl := by
      intro w hw
      rw [Pi.mul_apply, hD w hw]
      exact Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h w hw)) (diagEmb_mem_blockUT _ _ _)
    obtain ⟨z, s, hz, hsfix, -, -, hhw⟩ := hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) (hgb W2 m2) (hgb W1 m1) e
    obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hX.conjE hz
    refine ⟨ζ, funext fun w => ?_⟩
    let W' : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩
    have e2 : restr (r_le_nV R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) W')) = Units.val (t w) := by
      rw [Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_nV R) bl _ (diagEmb_mem_blockUT (r_le_nV R) bl (t ⟨w.1, w.2⟩)),
        restrict_eq_one_of_mem_blockLevel (r_le_nV R) bl (levelGroup_V_block Ch sel mu j h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]
    apply Units.ext
    ext a b
    rw [torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]
    simp only [restr, Matrix.submatrix_apply]
    rw [hhw, hsfix _ (show (Fin.castLE (r_le_nV R) b).val < R.r from b.2)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => hab (Fin.castLE_injective (r_le_nV R) e)), if_neg hab]

end RowsMainV

section Card

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_separating_residues (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (w : HeightOneSpectrum (𝓞 E))
    (r : ℕ) (hcard : r * Nat.card (NumberField.Units.torsion E) < Nat.card (𝓞 E ⧸ w.asIdeal)) :
    ∃ c : ℕ → 𝓞 E, (∀ i < r, c i ∉ w.asIdeal) ∧
      ∀ i i', i < r → i' < r → ∀ z : 𝓞 E, star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1 →
        c i' - z * c i ∈ w.asIdeal → i' = i := by
  classical
  set Q := 𝓞 E ⧸ w.asIdeal
  set red : NumberField.Units.torsion E → Q := fun ζ => Ideal.Quotient.mk w.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E)
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite Q
  have hQ : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
  have hμ : Nat.card (NumberField.Units.torsion E) = Fintype.card (NumberField.Units.torsion E) := Nat.card_eq_fintype_card
  have hμ1 : 1 ≤ Fintype.card (NumberField.Units.torsion E) := Fintype.card_pos
  have step : ∀ k, k ≤ r → ∃ x : ℕ → Q, (∀ i < k, x i ≠ 0) ∧
      ∀ i i' (ζ : NumberField.Units.torsion E), i < k → i' < k → x i' = red ζ * x i → i' = i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hx0, hx⟩ := ih (by omega)
      let F : Finset Q := insert 0 ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image
        fun p => red p.2 * x p.1)
      have hF : F.card < Fintype.card Q := by
        have h1 : F.card ≤ 1 + k * Fintype.card (NumberField.Units.torsion E) := by
          have h3 := Finset.card_insert_le (0 : Q) ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image
            fun p => red p.2 * x p.1)
          have h4 := Finset.card_image_le (s := Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E)))
            (f := fun p => red p.2 * x p.1)
          rw [Finset.card_product, Finset.card_range, Finset.card_univ] at h4
          show (insert 0 _ : Finset Q).card ≤ _
          omega
        have h2 : k * Fintype.card (NumberField.Units.torsion E) + Fintype.card (NumberField.Units.torsion E) ≤
            r * Fintype.card (NumberField.Units.torsion E) := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right _ hk
        rw [← hQ]
        rw [hμ] at hcard
        omega
      obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ F := by
        by_contra hc
        push Not at hc
        have : (Finset.univ : Finset Q) ⊆ F := fun y _ => hc y
        have := Finset.card_le_card this
        rw [Finset.card_univ] at this
        omega
      have hy0 : y ≠ 0 := fun h => hy (h ▸ Finset.mem_insert_self _ _)
      have hyF : ∀ i < k, ∀ ζ, y ≠ red ζ * x i := fun i hi ζ h => hy (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(i, ζ), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ _⟩, h.symm⟩))
      refine ⟨fun i => if i = k then y else x i, fun i hi => ?_, fun i i' ζ hi hi' e => ?_⟩
      · dsimp only
        by_cases hik : i = k
        · rw [if_pos hik]
          exact hy0
        · rw [if_neg hik]
          exact hx0 i (by omega)
      · dsimp only at e
        by_cases hik : i = k <;> by_cases hik' : i' = k
        · rw [hik, hik']
        · rw [if_pos hik, if_neg hik'] at e
          exfalso
          have hrinv : red ζ⁻¹ * red ζ = 1 := by
            simp only [red]
            rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, map_one]
          exact hyF i' (by omega) ζ⁻¹ (by rw [e, ← mul_assoc, hrinv, one_mul])
        · rw [if_neg hik, if_pos hik'] at e
          exact absurd e (hyF i (by omega) ζ)
        · rw [if_neg hik, if_neg hik'] at e
          exact hx i i' ζ (by omega) (by omega) e
  obtain ⟨x, hx0, hx⟩ := step r le_rfl
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := w.asIdeal) (x i)
  refine ⟨c, fun i hi h0 => hx0 i hi (by rw [← hc i]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h0),
    fun i i' hi hi' z hz hm => ?_⟩
  obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hconj hz
  refine hx i i' ζ hi hi' ?_
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [map_sub, map_mul, hc, hc, ← hζ] at h1
  exact sub_eq_zero.mp h1

end Card

section RowsCard

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem regModZX_of_card (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hsize : ∃ w1 ∈ Pr.vG 0, R.r * Nat.card (NumberField.Units.torsion X.E) < Nat.card (𝓞 X.E ⧸ w1.asIdeal)) :
    RegModZX W Ch sel mu := by
  obtain ⟨w1, h1, hs⟩ := hsize
  exact regModZX_of W Ch sel mu hX hPr hCh hW hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩

theorem regModZV_of_card (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hsize : ∃ w1 ∈ Pr.vG 0, R.r * Nat.card (NumberField.Units.torsion X.E) < Nat.card (𝓞 X.E ⧸ w1.asIdeal)) :
    RegModZV W Ch sel mu j := by
  obtain ⟨w1, h1, hs⟩ := hsize
  exact regModZV_of W Ch sel mu hX hPr hCh hW j hj1 hj2 hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩

end RowsCard

section NotFaithful

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def v0m1 (E : Type) [Field E] [NumberField E] : NumberField.Units.torsion E :=
  ⟨-1, (CommGroup.mem_torsion _).mpr ((isOfFinOrder_iff_pow_eq_one).mpr ⟨2, two_pos, by simp⟩)⟩

open Classical in

theorem negOneCenter_ne_one (hX : X.Ok) (hPr : Pr.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i) : v0Z Pr.vGs R.r (v0m1 X.E) ≠ 1 := by
  have hr : 0 < R.r := nz_r_pos R
  obtain ⟨w1, h1⟩ : (Pr.vG 0).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  intro hz
  have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hz
  simp only at e
  rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
  have h2 : (2 : 𝓞 X.E) ∈ w1.asIdeal := by
    have : ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 ∈ w1.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
      exact sub_eq_zero.mpr e
    have h3 : ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 = -2 := by push_cast; ring
    rw [h3] at this
    simpa using w1.asIdeal.neg_mem this
  have hgm : ((Pr.g 0 : ℕ) : 𝓞 X.E) ∈ w1.asIdeal := hPr.g_mem h1
  obtain ⟨q, hq⟩ : ∃ q, Pr.g 0 = 2 * q + 1 := by
    rcases (hPr.g_prime 0).eq_two_or_odd' with h | h
    · have := hg 0
      have := hX.f_pos
      omega
    · obtain ⟨q, hq⟩ := h
      exact ⟨q, by omega⟩
  have h1' : (1 : 𝓞 X.E) ∈ w1.asIdeal := by
    have : (1 : 𝓞 X.E) = ((Pr.g 0 : ℕ) : 𝓞 X.E) - 2 * (q : 𝓞 X.E) := by
      rw [hq]
      push_cast
      ring
    rw [this]
    exact w1.asIdeal.sub_mem hgm (w1.asIdeal.mul_mem_right _ h2)
  exact w1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

open Classical in

theorem unipotentAction_not_faithful_X (hX : X.Ok) (hPr : Pr.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i) :
    ∃ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r), a ≠ 0 ∧ (g0HatRepEqFunX W Ch sel mu).asAlgebraHom a = 0 := by
  classical
  set ζ := v0m1 X.E
  refine ⟨MonoidAlgebra.single 1 1 - MonoidAlgebra.single (v0Z Pr.vGs R.r ζ) (((torsionScalarCharacterAtBase W Ch sel mu ζ)⁻¹ : X.Kˣ) : X.K), ?_, ?_⟩
  · intro h0
    have := congrArg (fun x : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r) => x.coeff 1) h0
    simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_zero] at this
    simp only [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [if_pos trivial, if_neg (negOneCenter_ne_one hX hPr hg), sub_zero] at this
    exact one_ne_zero this
  · rw [map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, map_one, one_smul]
    apply LinearMap.ext
    intro φ
    rw [LinearMap.sub_apply, LinearMap.smul_apply, torsionCenter_scalar_X W Ch sel mu hX ζ φ, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul, Module.End.one_apply, sub_self, LinearMap.zero_apply]

end NotFaithful

end Formalism.L2.Col
