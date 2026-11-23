import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

section Abstract

variable {V : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsAddRightInvariant]
  {L : AddSubgroup V} [Countable L] {D : Set V}

theorem setIntegral_add_right_of_periodic (hD : IsAddFundamentalDomain L D ν) {h : V → ℂ}
    (hper : ∀ ξ ∈ L, ∀ s, h (ξ + s) = h s) (y : V) :
    ∫ t in D, h (t + y) ∂ν = ∫ t in D, h t ∂ν := by
  have hD' : IsAddFundamentalDomain L ((· + (-y)) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_right ν (-y)).quasiMeasurePreserving
      (e := id) bijective_id fun g x => by
        simp only [id, AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  calc ∫ t in D, h (t + y) ∂ν
      = ∫ u in (· + (-y)) ⁻¹' D, (fun t => h (t + y)) (u + (-y)) ∂ν :=
        ((measurePreserving_add_right ν (-y)).setIntegral_preimage_emb
          (MeasurableEquiv.addRight (-y)).measurableEmbedding (fun t => h (t + y)) D).symm
    _ = ∫ u in (· + (-y)) ⁻¹' D, h u ∂ν := by
        simp only [neg_add_cancel_right]
    _ = ∫ t in D, h t ∂ν := hD'.setIntegral_eq hD fun ξ x => hper ξ ξ.2 x

theorem norm_le_of_forall_altSum_le (hD : IsAddFundamentalDomain L D ν) (hD1 : ν D = 1) :
    ∀ (k : ℕ) (h : V → ℂ), (∀ ξ ∈ L, ∀ s, h (ξ + s) = h s) →
      (∀ t, IntegrableOn (fun y => h (t + y)) D ν) → ∫ y in D, h y ∂ν = 0 →
      ∀ B : ℝ, (∀ y : Fin k → V, (∀ i, y i ∈ D) → ‖altSum k h y 0‖ ≤ B) → ‖h 0‖ ≤ B
  | 0, h, _, _, _, B, hB => by
    simpa using hB Fin.elim0 fun i => i.elim0
  | k + 1, h, hper, hint, hmean, B, hB => by
    have hi0 : IntegrableOn h D ν := by simpa using hint 0
    have hstep : ∀ y ∈ D, ‖h (0 + y) - h 0‖ ≤ B := by
      intro y hy
      set g : V → ℂ := fun t => h (t + y) - h t with hg
      have hper' : ∀ ξ ∈ L, ∀ s, g (ξ + s) = g s := fun ξ hξ s => by
        simp only [hg, add_assoc, hper ξ hξ]
      have hint' : ∀ t, IntegrableOn (fun y' => g (t + y')) D ν := by
        intro t
        have h1 := hint (t + y)
        have e : (fun y' => h (t + y + y')) = fun y' => h (t + y' + y) :=
          funext fun y' => by rw [add_right_comm]
        rw [e] at h1
        exact h1.sub (hint t)
      have hiy : IntegrableOn (fun t => h (t + y)) D ν := by
        have h1 := hint y
        have e : (fun y' => h (y + y')) = fun t => h (t + y) := funext fun t => by rw [add_comm]
        rwa [e] at h1
      have hmean' : ∫ t in D, g t ∂ν = 0 := by
        rw [show (∫ t in D, g t ∂ν) = (∫ t in D, h (t + y) ∂ν) - ∫ t in D, h t ∂ν from
          integral_sub hiy hi0, setIntegral_add_right_of_periodic hD hper y, sub_self]
      have hB' : ∀ z : Fin k → V, (∀ i, z i ∈ D) → ‖altSum k g z 0‖ ≤ B := by
        intro z hz
        have hmem : ∀ i, (Fin.cons y z : Fin (k + 1) → V) i ∈ D := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hy
          · simpa using hz j
        have := hB (Fin.cons y z) hmem
        rwa [altSum_succ, Fin.cons_zero, Fin.tail_cons] at this
      have := norm_le_of_forall_altSum_le hD hD1 k g hper' hint' hmean' B hB'
      simpa [hg] using this
    have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
    have hkey : ∫ y in D, (h (0 + y) - h 0) ∂ν = -h 0 := by
      have hi0' : IntegrableOn (fun y => h (0 + y)) D ν := by simpa using hi0
      rw [integral_sub hi0' (integrableOn_const hfin.ne)]
      simp only [zero_add, hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one,
        one_smul, zero_sub]
    calc ‖h 0‖ = ‖∫ y in D, (h (0 + y) - h 0) ∂ν‖ := by rw [hkey, norm_neg]
      _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hstep
      _ = B := by simp [measureReal_def, hD1]

end Abstract

section Scaled

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def scaledUnipFD (r M : ℕ) : Set (UPos n r → 𝔸[K]) :=
  {X | (fun p => algebraMap K 𝔸[K] ((M : K)⁻¹) * X p) ∈ unipFundamentalDomain K n r}

variable {r M : ℕ}

theorem mem_scaledUnipFD {X : UPos n r → 𝔸[K]} :
    X ∈ scaledUnipFD K n r M ↔
      ∀ p, algebraMap K 𝔸[K] ((M : K)⁻¹) * X p ∈ GroundTheory.Global.fundamentalSet K := by
  simp [scaledUnipFD, unipFundamentalDomain, Set.mem_pi]

theorem measurableSet_scaledUnipFD : MeasurableSet (scaledUnipFD K n r M) :=
  measurableSet_unipFundamentalDomain.preimage
    (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable

theorem algebraMap_inv_mul_natCast (hM : 0 < M) :
    algebraMap K 𝔸[K] ((M : K)⁻¹) * (M : 𝔸[K]) = 1 := by
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← map_natCast (algebraMap K 𝔸[K]) M, ← map_mul, inv_mul_cancel₀ hM', map_one]

theorem existsUnique_vadd_mem_scaledUnipFD (hM : 0 < M) (X : UPos n r → 𝔸[K]) :
    ∃! ξ : unipLattice K n r, ξ +ᵥ X ∈ scaledUnipFD K n r M := by
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  set c := algebraMap K 𝔸[K] ((M : K)⁻¹) with hc
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (c * X p)
  have hmul : ∀ η : K, c * algebraMap K 𝔸[K] η = algebraMap K 𝔸[K] ((M : K)⁻¹ * η) := fun η => by
    rw [hc, map_mul]
  have hmem : (fun p => algebraMap K 𝔸[K] (-((M : K) * k p))) ∈ unipLattice K n r :=
    ⟨fun p => -((M : K) * k p), funext fun p => rfl⟩
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · show (fun p => algebraMap K 𝔸[K] (-((M : K) * k p))) + X ∈ scaledUnipFD K n r M
    rw [mem_scaledUnipFD]
    intro p
    change c * (algebraMap K 𝔸[K] (-((M : K) * k p)) + X p) ∈ GroundTheory.Global.fundamentalSet K
    rw [mul_add, hmul, show (M : K)⁻¹ * -((M : K) * k p) = -k p by field_simp, map_neg, add_comm,
      ← sub_eq_add_neg]
    exact hk p
  · rintro ⟨_, η, rfl⟩ hη
    rw [mem_scaledUnipFD] at hη
    refine Subtype.ext (funext fun p => ?_)
    have h1 := hη p
    change c * (algebraMap K 𝔸[K] (η p) + X p) ∈ GroundTheory.Global.fundamentalSet K at h1
    rw [mul_add, hmul, add_comm, ← sub_neg_eq_add, ← map_neg] at h1
    have h2 := huniq p _ h1
    change algebraMap K 𝔸[K] (η p) = algebraMap K 𝔸[K] (-((M : K) * k p))
    rw [← h2]
    congr 1
    field_simp

theorem isAddFundamentalDomain_scaledUnipFD (hM : 0 < M) :
    IsAddFundamentalDomain (unipLattice K n r) (scaledUnipFD K n r M) (unipMeasure K n r) :=
  IsAddFundamentalDomain.mk' measurableSet_scaledUnipFD.nullMeasurableSet
    (existsUnique_vadd_mem_scaledUnipFD hM)

theorem unipMeasure_scaledUnipFD (hM : 0 < M) :
    unipMeasure K n r (scaledUnipFD K n r M) = 1 := by
  rw [(isAddFundamentalDomain_scaledUnipFD hM).measure_eq
    isAddFundamentalDomain_unipFundamentalDomain, unipMeasure_unipFundamentalDomain]

theorem eq_natCast_mul_of_mem_scaledUnipFD (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) :
    X p = (M : 𝔸[K]) * (algebraMap K 𝔸[K] ((M : K)⁻¹) * X p) ∧
      algebraMap K 𝔸[K] ((M : K)⁻¹) * X p ∈ GroundTheory.Global.fundamentalSet K := by
  refine ⟨?_, mem_scaledUnipFD.1 hX p⟩
  rw [← mul_assoc, mul_comm (M : 𝔸[K]), algebraMap_inv_mul_natCast hM, one_mul]

theorem exists_finite_eq_natCast_mul (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      (X p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  obtain ⟨h1, h2⟩ := eq_natCast_mul_of_mem_scaledUnipFD hM hX p
  refine ⟨(algebraMap K 𝔸[K] ((M : K)⁻¹) * X p).2, h2.2, ?_⟩
  conv_lhs => rw [h1]
  rfl

variable (K) in

def scaledInfSet (M : ℕ) : Set (InfiniteAdeleRing K) :=
  (fun x => (M : InfiniteAdeleRing K) * x) '' closure (GroundTheory.Global.fundamentalSetInfinite K)

theorem isCompact_scaledInfSet (M : ℕ) : IsCompact (scaledInfSet K M) :=
  (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).image (continuous_const_mul _)

theorem infinite_mem_scaledInfSet (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) : (X p).1 ∈ scaledInfSet K M := by
  obtain ⟨h1, h2⟩ := eq_natCast_mul_of_mem_scaledUnipFD hM hX p
  refine ⟨(algebraMap K 𝔸[K] ((M : K)⁻¹) * X p).1, subset_closure h2.1, ?_⟩
  conv_rhs => rw [h1]
  rfl

theorem exists_finite_sum_eq_natCast_mul (hM : 0 < M) {ι : Type*} (s : Finset ι)
    (y : ι → UPos n r → 𝔸[K]) (hy : ∀ i ∈ s, y i ∈ scaledUnipFD K n r M) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      ((∑ i ∈ s, y i) p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [Finset.sum_empty, mul_zero]
    rfl
  | insert i s hi ih =>
    obtain ⟨a, ha, hae⟩ := exists_finite_eq_natCast_mul hM (hy i (Finset.mem_insert_self i s)) p
    obtain ⟨b, hb, hbe⟩ := ih fun j hj => hy j (Finset.mem_insert_of_mem hj)
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [Finset.sum_insert hi, Pi.add_apply,
      show (y i p + (∑ x ∈ s, y x) p).2 = (y i p).2 + ((∑ x ∈ s, y x) p).2 from rfl, hae, hbe,
      mul_add]

theorem exists_finite_altPoint_eq_natCast_mul (hM : 0 < M) {k : ℕ} (y : Fin k → UPos n r → 𝔸[K])
    (hy : ∀ i, y i ∈ scaledUnipFD K n r M) (ε : Fin k → Bool) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      ((altPoint y ε) p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  classical
  have : altPoint y ε = ∑ i ∈ Finset.univ.filter (fun i => ε i = true), y i := by
    rw [altPoint, Finset.sum_filter]
  rw [this]
  exact exists_finite_sum_eq_natCast_mul hM _ y (fun i _ => hy i) p

end Scaled

end

end GroundTheory.Automorphic
