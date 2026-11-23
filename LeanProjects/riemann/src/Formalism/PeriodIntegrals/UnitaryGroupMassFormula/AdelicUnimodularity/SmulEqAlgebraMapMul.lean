import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CoordTmulOneMul
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct

theorem exists_den {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp

variable {F : Type} [Field F] [NumberField F]

def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F

theorem ohat_mul {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a * c ∈ Ohat F := by
  intro v
  exact mul_mem (ha v) (hc v)

theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F := by
  intro v
  exact add_mem (ha v) (hc v)

theorem ohat_neg {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) : -a ∈ Ohat F := by
  intro v
  exact neg_mem (ha v)

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).zero_mem

theorem ohat_one : (1 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F := by
  intro v
  exact (v.adicCompletionIntegers F).one_mem

theorem ohat_sum {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ohat_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ohat_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => rw [zero_nsmul]; exact ohat_zero
  | succ n ih => rw [succ_nsmul]; exact ohat_add ih ha

theorem ohat_zsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [natCast_zsmul]; exact ohat_nsmul ha n
  · rw [neg_zsmul, natCast_zsmul]; exact ohat_neg (ohat_nsmul ha n)

theorem intF_of_int (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := by
  unfold IntF Ohat
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_den_fin {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have key : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((c : 𝓞 F) * a i) := by
    rw [hc, Nat.cast_mul, map_mul, ← ha i, map_natCast]; ring
  rw [key]
  exact intF_of_int _

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

theorem intC_add {x y : E ⊗[F] Af} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := by
  intro k
  rw [map_add]
  exact ohat_add (hx k) (hy k)

theorem intC_nsmul {x : E ⊗[F] Af} (hx : IntC b x) (m : ℕ) : IntC b (m • x) := by
  intro k
  rw [map_nsmul]
  exact ohat_nsmul (hx k) m

theorem intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := by
  intro k
  rw [map_sum, Finset.sum_apply]
  exact ohat_sum s fun i hi => hf i hi k

theorem smul_eq_algebraMap_mul (c : F) (a : Af) : c • a = algebraMap F Af c * a :=
  Algebra.smul_def c a

theorem exists_den_mul (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))

theorem intC_incl {e : E} (he : ∀ k, IntF (b.repr e k)) :
    IntC b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := Af) e) := by
  intro k
  rw [Algebra.TensorProduct.includeLeftRingHom_apply]
  simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  rw [← Algebra.algebraMap_eq_smul_one]
  exact he k

end Coord

end PI.WAU
