import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfFrobeniusDvdEisensteinPowMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.CoeffIdeal

theorem principal_of_saturated {S k : Type} [CommRing S] [IsNoetherianRing S] [CommRing k]
    [IsPrincipalIdealRing k] (π : S →+* k) (hπ : Function.Surjective π) (p : S)
    (hker : ∀ x, π x = 0 → p ∣ x) (hp : Ideal.span {p} ≤ Ideal.jacobson ⊥) (P : Ideal S)
    (hP : ∀ x, p * x ∈ P → x ∈ P) : ∃ g, P = Ideal.span {g} := by
  obtain ⟨g', hg'⟩ := (IsPrincipalIdealRing.principal (P.map π)).principal
  have h0 : g' ∈ P.map π := by rw [hg']; exact Submodule.mem_span_singleton_self _
  obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 h0
  refine ⟨g, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hg)⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian P) hp fun x hx => ?_
  have h1 : π x ∈ P.map π := Ideal.mem_map_of_mem π hx
  rw [hg'] at h1
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨c, rfl⟩ := hπ c'
  obtain ⟨y, hy⟩ := hker (x - c * g) (by rw [map_sub, map_mul, ← hc', smul_eq_mul, sub_self])
  have hyP : y ∈ P := hP y (hy ▸ P.sub_mem hx (P.mul_mem_left c hg))
  have e : x = c * g + p • y := by rw [smul_eq_mul, ← hy]; ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self g))
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hyP)

theorem c_frob_mem {S A : Type} [CommRing S] [IsNoetherianRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (hI : I ≤ Ideal.jacobson ⊥) (φ : S →+* S) (Φ : A →+* A)
    (hφ : ∀ a, s (φ a) = Φ (s a)) (hφI : I.map φ ≤ I) (x : A) (N : Ideal S) (hN : ∀ i, φ (TB.c i x) ∈ N)
    (j : ι) : TB.c j (Φ x) ∈ N := by
  have hH : IsHausdorff I (S ⧸ N) := IsHausdorff.of_le_jacobson _ _ hI
  refine Ideal.Quotient.eq_zero_iff_mem.1 (hH.haus _ fun n => ?_)
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by simpa using hi
  have h1 := Ideal.mem_map_of_mem Φ (TB.approx x n _ hF)
  have e : Φ.comp s = s.comp φ := RingHom.ext fun a => (hφ a).symm
  rw [Ideal.map_map, e, ← Ideal.map_map, Ideal.map_pow] at h1
  have h2 := TB.c_mem_of_mem_map _ _ (Ideal.map_mono (Ideal.pow_right_mono hφI n) h1) j
  rw [map_sub, map_sub, map_sum, map_sum] at h2
  have h3 : ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i)) ∈ N :=
    N.sum_mem fun i _ => by
      rw [map_mul, ← hφ, TB.c_mul]
      exact N.mul_mem_right _ (hN i)
  have h4 : Ideal.Quotient.mk N (TB.c j (Φ x)) =
      (TB.c j (Φ x) - ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i))) • (1 : S ⧸ N) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simpa using h3
  rw [SModEq.zero, h4]
  exact Submodule.smul_mem_smul h2 Submodule.mem_top

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

theorem prime_l : Prime (l : (Wq l a)⟦X⟧) := by
  have key : ∀ x : (Wq l a)⟦X⟧, (l : (Wq l a)⟦X⟧) ∣ x →
      PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) x = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [map_mul, map_natCast, l_eq_zero, zero_mul]
  refine ⟨l_ne_zero l a, fun h => ?_, fun x y h => ?_⟩
  · have := key 1 h.dvd
    rw [map_one] at this
    exact one_ne_zero this
  · have := key _ h
    rw [map_mul] at this
    exact (mul_eq_zero.1 this).imp (dvd_of_map_eq_zero l a x) (dvd_of_map_eq_zero l a y)

theorem ne_zero_of_isPer {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := h
  rw [map_zero, eq_comm, Units.mul_right_eq_zero, sub_eq_zero] at h
  have h1 : ε = 1 := by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa using this
  exact hδ1 (by rw [h1, map_one, map_one])

end GlobalTheory.BSP.CoeffIdeal

open GlobalTheory.BSP.CoeffIdeal in

theorem GlobalTheory.BSP.pow_l_mem_span_coeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  intro l _ K bk τ hτ ι TB M
  set I : Ideal bk.S := Ideal.span (Set.range fun i => TB.c i (τ ^ M)) with hI
  have hJ : bk.J ≤ Ideal.jacobson ⊥ := by
    have := bk.complete
    exact IsAdicComplete.le_jacobson_bot _
  have hpr := prime_l l bk.a
  let P : Ideal bk.S :=
    { carrier := {x | ∃ r : ℕ, (l : bk.S) ^ r * x ∈ I}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨t, ht⟩
        refine ⟨r + t, ?_⟩
        have := I.add_mem (I.mul_mem_left ((l : bk.S) ^ t) hr) (I.mul_mem_left ((l : bk.S) ^ r) ht)
        convert this using 1
        ring
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact I.mul_mem_left c hr }
  have hsat : ∀ x, (l : bk.S) * x ∈ P → x ∈ P := by
    rintro x ⟨r, hr⟩
    exact ⟨r + 1, by rwa [pow_succ, mul_assoc]⟩
  have hIP : I ≤ P := fun x hx => ⟨0, by simpa using hx⟩
  obtain ⟨g, hg⟩ := principal_of_saturated
    (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)))
    (PowerSeries.map_surjective _ (WittVector.constantCoeff_surjective l)) (l : bk.S)
    (dvd_of_map_eq_zero l bk.a) (le_sup_left.trans hJ) P hsat
  have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
  have hdvd : ∀ i, g ∣ TB.c i (τ ^ M) := fun i => by
    rw [← Ideal.mem_span_singleton, ← hg]
    exact hIP (Ideal.subset_span ⟨i, rfl⟩)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact pow_ne_zero M (ne_zero_of_isPer l bk hτ) (TB.eq_zero_of_c _ fun i => zero_dvd_iff.1 (hdvd i))
  have hlg : ¬ (l : bk.S) ∣ g := by
    rintro ⟨y, hy⟩
    have h1 : y ∈ P := hsat y (hy ▸ hgP)
    rw [hg, Ideal.mem_span_singleton] at h1
    obtain ⟨z, hz⟩ := h1
    refine hpr.not_unit (IsUnit.of_mul_eq_one z (mul_left_cancel₀ hg0 ?_))
    rw [mul_one]
    conv_rhs => rw [hy, hz]
    ring
  have hφJ : bk.J.map (frobS l bk.a) ≤ bk.J := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    obtain ⟨b, hb⟩ := frobS_eq l bk.a bk.E
    rw [hb, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Fact.out : l.Prime).pos)
  have hE : ∀ j, frobS l bk.a g ∣ bk.E ^ M * TB.c j (τ ^ M) := fun j => by
    have := c_frob_mem TB hJ (frobS l bk.a) WittVector.frobenius bk.ev_frob hφJ (τ ^ M)
      (Ideal.span {frobS l bk.a g}) (fun i => Ideal.mem_span_singleton.2 (map_dvd _ (hdvd i))) j
    rwa [map_pow, hτ.1, mul_pow, ← map_pow, TB.c_mul, Ideal.mem_span_singleton] at this
  have hEI : ∀ x ∈ I, frobS l bk.a g ∣ bk.E ^ M * x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hE i
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left c
  obtain ⟨r, hr⟩ := hgP
  have hlφ : ¬ (l : bk.S) ∣ frobS l bk.a g := by
    obtain ⟨b, hb⟩ := frobS_eq l bk.a g
    rw [hb]
    intro h
    exact hlg (hpr.dvd_of_dvd_pow ((dvd_add_left (dvd_mul_right _ b)).1 h))
  have hfin : frobS l bk.a g ∣ bk.E ^ M * g := by
    obtain ⟨z, hz⟩ := hEI _ hr
    obtain ⟨w, hw⟩ : (l : bk.S) ^ r ∣ z :=
      hpr.pow_dvd_of_dvd_mul_left r hlφ ⟨bk.E ^ M * g, by rw [← hz]; ring⟩
    refine ⟨w, mul_left_cancel₀ (pow_ne_zero r hpr.ne_zero) ?_⟩
    rw [mul_left_comm, hz, hw]
    ring
  have hu := GlobalTheory.T.isUnit_of_frobenius_dvd_eisenstein_pow_mul l K bk g hlg M hfin
  exact ⟨r, (I.mul_unit_mem_iff_mem hu).1 hr⟩
