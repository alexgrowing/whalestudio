import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions

theorem qcs_bound {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (B : LinearMap.BilinForm ℚ W) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (f : W →ₗ[ℚ] ℚ) : ∃ K : ℚ, ∀ x, f x ^ 2 ≤ K * B x x := by
  let Bl : W →ₗ[ℚ] Module.Dual ℚ W := B
  have hinj : Function.Injective Bl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have h1 := hp w hne
    have h0 : B w w = 0 := by simpa [Bl] using LinearMap.congr_fun hw w
    linarith
  have hsurj : Function.Surjective Bl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w, hw⟩ := hsurj f
  refine ⟨B w w, fun x => ?_⟩
  have hfx : f x = B w x := by rw [← hw]
  rw [hfx]
  by_cases hw0 : w = 0
  · subst hw0
    simp
  · have hww := hp w hw0
    have hyy : 0 ≤ B (B w w • x - B w x • w) (B w w • x - B w x • w) := by
      by_cases hy : B w w • x - B w x • w = 0
      · rw [hy]
        simp
      · exact le_of_lt (hp _ hy)
    have hexp : B (B w w • x - B w x • w) (B w w • x - B w x • w) =
        B w w * (B w w * B x x - B w x ^ 2) := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hs x w]
      ring
    rw [hexp] at hyy
    have h2 := (mul_nonneg_iff_of_pos_left hww).1 hyy
    linarith

theorem trace_pos_of_re_pos {E : Type} [Field E] [NumberField E] (z : E)
    (h : ∀ τ : E →+* ℂ, 0 < (τ z).re) : 0 < Algebra.trace ℚ E z := by
  haveI : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
    trace_eq_sum_embeddings ℂ
  have h2 : (algebraMap ℚ ℂ (Algebra.trace ℚ E z)).re = ∑ σ : E →ₐ[ℚ] ℂ, (σ z).re := by
    rw [h1, Complex.re_sum]
  have h3 : (algebraMap ℚ ℂ (Algebra.trace ℚ E z)).re = ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
    simp
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ z).re := by
    apply Finset.sum_pos
    · intro σ _
      exact h σ.toRingHom
    · exact Finset.univ_nonempty
  have h4 : (0 : ℝ) < ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
    rw [← h3, h2]
    exact hpos
  exact_mod_cast h4

theorem exists_common_den {E : Type} [Field E] [NumberField E] (t : Finset E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ e ∈ t, IsIntegral ℤ ((d : E) * e) := by
  have hintC : ∀ m : ℤ, IsIntegral ℤ (m : E) := fun m => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)
  have hone : ∀ a : E, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * a) := by
    intro a
    have hbint : ∀ k, IsIntegral ℤ (integralBasis E k) := by
      intro k
      rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hsum : ∀ Y : ℤ, (Y : E) * a = ∑ k, ((Y : ℚ) * (integralBasis E).repr a k) • integralBasis E k := by
      intro Y
      have h1 : (Y : E) * (∑ k, (integralBasis E).repr a k • integralBasis E k) =
          ∑ k, ((Y : ℚ) * (integralBasis E).repr a k) • integralBasis E k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [Algebra.smul_def, map_mul, map_intCast]
        ring
      rwa [(integralBasis E).sum_repr a] at h1
    refine ⟨∏ j, (((integralBasis E).repr a j).den : ℤ), ?_, ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro k _
      exact_mod_cast ((integralBasis E).repr a k).den_nz
    · rw [hsum]
      apply IsIntegral.sum
      intro k _
      obtain ⟨c, hc⟩ : (((integralBasis E).repr a k).den : ℤ) ∣ ∏ j, (((integralBasis E).repr a j).den : ℤ) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      have hm : ((∏ j, (((integralBasis E).repr a j).den : ℤ) : ℤ) : ℚ) * (integralBasis E).repr a k =
          ((c * ((integralBasis E).repr a k).num : ℤ) : ℚ) := by
        rw [hc]
        push_cast
        have h2 := Rat.den_mul_eq_num ((integralBasis E).repr a k)
        linear_combination (c : ℚ) * h2
      rw [hm, Algebra.smul_def, map_intCast]
      exact (hintC _).mul (hbint k)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun e he => by simp at he⟩
  | @insert a t ha ih =>
    obtain ⟨d, hd, hdint⟩ := ih
    obtain ⟨y, hy, hyint⟩ := hone a
    refine ⟨d * y, mul_ne_zero hd hy, fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he'
    · have h1 : ((d * y : ℤ) : E) * e = (d : E) * ((y : E) * e) := by
        push_cast
        ring
      rw [h1]
      exact (hintC d).mul hyint
    · have h1 : ((d * y : ℤ) : E) * e = (y : E) * ((d : E) * e) := by
        push_cast
        ring
      rw [h1]
      exact (hintC y).mul (hdint e he')

theorem eq_of_trace_basis {E : Type} [Field E] [NumberField E] (a b : E)
    (h : ∀ k, Algebra.trace ℚ E (integralBasis E k * a) = Algebra.trace ℚ E (integralBasis E k * b)) :
    a = b := by
  have hφ : (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (a - b)) = 0 := by
    apply (integralBasis E).ext
    intro k
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
    rw [sub_mul, map_sub, mul_comm a, mul_comm b, h k, sub_self]
  have hall : ∀ n : E, Algebra.traceForm ℚ E (a - b) n = 0 := by
    intro n
    rw [Algebra.traceForm_apply]
    exact LinearMap.congr_fun hφ n
  have hab : a - b = 0 := by
    first
    | exact (traceForm_nondegenerate ℚ E) (a - b) hall
    | exact (traceForm_nondegenerate ℚ E).1 (a - b) hall
    | exact (traceForm_nondegenerate (K := ℚ) (L := E)) (a - b) hall
  exact sub_eq_zero.1 hab

theorem trace_int_of_isIntegral {E : Type} [Field E] [NumberField E] (z : E) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E z := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E z) := Algebra.isIntegral_trace hz
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact ⟨n, by simpa using hn⟩

theorem shortFin_holds : ShortFin := by
  intro E _ _ _ S Λ hΛ P hpos c
  have hsl : ∀ (q : ℚ) (x y : S.V),
      S.hT (algebraMap ℚ E q • x) y = algebraMap ℚ E q * S.hT x y := by
    intro q x y
    rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, eq_ratCast, star_ratCast, smul_eq_mul]
  have hsr : ∀ (q : ℚ) (x y : S.V),
      S.hT x (algebraMap ℚ E q • y) = algebraMap ℚ E q * S.hT x y := by
    intro q x y
    rw [LinearMap.map_smul, smul_eq_mul]
  have htq : ∀ (q : ℚ) (z : E),
      Algebra.trace ℚ E (algebraMap ℚ E q * z) = q * Algebra.trace ℚ E z := by
    intro q z
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  letI : Module ℚ P := Module.compHom P (algebraMap ℚ E)
  haveI : IsScalarTower ℚ E P := ⟨fun q e x => by
    show (q • e) • x = algebraMap ℚ E q • (e • x)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : FiniteDimensional ℚ P := Module.Finite.trans E P
  have hcoe : ∀ (q : ℚ) (x : P), ((q • x : P) : S.V) = algebraMap ℚ E q • (x : S.V) :=
    fun q x => rfl
  let B : LinearMap.BilinForm ℚ P := LinearMap.mk₂ ℚ
    (fun x y : P => Algebra.trace ℚ E (S.hT x y) + Algebra.trace ℚ E (S.hT y x))
    (fun x1 x2 y => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; ring)
    (fun q x y => by simp only [hcoe, hsl, hsr, htq, smul_eq_mul]; ring)
    (fun x y1 y2 => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; ring)
    (fun q x y => by simp only [hcoe, hsl, hsr, htq, smul_eq_mul]; ring)
  have hBapp : ∀ x y : P,
      B x y = Algebra.trace ℚ E (S.hT x y) + Algebra.trace ℚ E (S.hT y x) := fun x y => rfl
  have hsym : ∀ x y : P, B x y = B y x := fun x y => by rw [hBapp, hBapp]; ring
  have hp : ∀ x : P, x ≠ 0 → 0 < B x x := by
    intro x hx
    have hx' : (x : S.V) ≠ 0 := by
      intro h; apply hx; exact Subtype.ext h
    have := trace_pos_of_re_pos _ (hpos x x.2 hx')
    rw [hBapp]; linarith

  obtain ⟨sg, hsg⟩ := hΛ.fg
  obtain ⟨d, hd0, hd⟩ :=
    exists_common_den (sg.biUnion fun g => Finset.univ.image fun j => S.frame.repr g j)
  have hΛint : ∀ x ∈ Λ, ∀ j, IsIntegral ℤ ((d : E) * S.frame.repr x j) := by
    intro x hx
    rw [← hsg] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro j
      exact hd _ (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add x y _ _ hx hy =>
      intro j
      simp only [map_add, Finsupp.add_apply, mul_add]
      exact (hx j).add (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hx j)

  let Φ : S.V → Fin S.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℚ := fun x p =>
    Algebra.trace ℚ E (integralBasis E p.2 * ((d : E) * S.frame.repr x p.1))
  have hlin : ∀ p, ∃ f : P →ₗ[ℚ] ℚ, ∀ x : P, f x = Φ x p := by
    intro p
    refine ⟨{ toFun := fun x => Φ x p, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      simp only [Φ, Submodule.coe_add, map_add, Finsupp.add_apply, mul_add]
    · intro q x
      simp only [Φ, hcoe, map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← htq]
      congr 1
      ring
  choose f hf using hlin
  choose K hK using fun p => qcs_bound B hsym hp (f p)
  have hint : ∀ x ∈ Λ, ∀ p, ∃ n : ℤ, (n : ℚ) = Φ x p := by
    intro x hx p
    have hμ : IsIntegral ℤ (integralBasis E p.2) := by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    exact trace_int_of_isIntegral _ (hμ.mul (hΛint x hx p.1))
  let R : Fin S.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ := fun p =>
    ⌈K p * (2 * Algebra.trace ℚ E c)⌉
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun p => ((Int.cast : ℤ → ℚ) '' Set.Icc (-R p) (R p))) ?_ ?_
    (Set.Finite.pi fun p => (Set.finite_Icc _ _).image _)
  · rintro x ⟨hxΛ, hxP, hxc⟩ p _
    obtain ⟨n, hn⟩ := hint x hxΛ p
    have hB : B ⟨x, hxP⟩ ⟨x, hxP⟩ = 2 * Algebra.trace ℚ E c := by
      rw [hBapp]; simp only [hxc]; ring
    have h1 : (Φ x p) ^ 2 ≤ K p * (2 * Algebra.trace ℚ E c) := by
      have := hK p ⟨x, hxP⟩
      rw [hf, hB] at this
      exact this
    have h2 : ((n ^ 2 : ℤ) : ℚ) ≤ (R p : ℚ) := by
      push_cast
      rw [hn]
      exact h1.trans (Int.le_ceil _)
    have h3 : n ^ 2 ≤ R p := by exact_mod_cast h2
    refine ⟨n, ⟨?_, ?_⟩, hn⟩
    · rcases le_or_gt n 0 with h | h <;> nlinarith
    · rcases le_or_gt n 0 with h | h <;> nlinarith
  · rintro x ⟨hxΛ, -, -⟩ y ⟨hyΛ, -, -⟩ hxy
    apply S.frame.ext_elem
    intro j
    have hj : (d : E) * S.frame.repr x j = (d : E) * S.frame.repr y j :=
      eq_of_trace_basis _ _ (fun k => congrFun hxy (j, k))
    exact mul_left_cancel₀ (Int.cast_ne_zero.2 hd0) hj

end PI.TermsAtPtFiniteW
