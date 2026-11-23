import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CanonicalTranslateJets

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SD

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem mm_unimod (x : D.host.E) :
    x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ↔
      ∀ y ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
        Algebra.trace D.host.K D.host.E (x * D.host.conj y) ∈
          (algebraMap (𝓞 D.host.K) D.host.K).range :=
  D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x

theorem bb_ne_zero :
    (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  intro h
  have := D.host.𝔟_spec.2
  rw [h] at this
  simp at this

theorem ideal_mul_inverse_integral {b a : D.host.E}
    (hb : b ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    b * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := FractionalIdeal.mul_mem_mul hb ha
  rw [Host.AA0] at h
  rw [mul_inv_cancel₀ (bb_ne_zero D), FractionalIdeal.mem_one_iff] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr⟩

theorem one_mem_ideal_mul_inverse :
    (1 : D.host.E) ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      D.host.AA0 := by
  rw [Host.AA0, mul_inv_cancel₀ (bb_ne_zero D)]
  exact FractionalIdeal.one_mem_one _

variable {D}

theorem stdH_eq {N : ℕ} (x y : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N x y) = ∑ i, D.host.conj (x i) * y i := by
  unfold stdH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CU.star_conj]

theorem hom_step {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (Z : Matrix (Fin N') (Fin N) D.host.E)
    (hZ : ∀ x ∈ L, ∀ y ∈ L', (∑ i, D.host.conj (y i) * Z.mulVec x i) ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    Z ∈ YYl D L L' := by
  have key : ∀ r ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      D.host.AA0, r • Z ∈ YYl D L L' := by
    intro r hr
    refine FractionalIdeal.mul_induction_on hr ?_ ?_
    · intro b hb a ha
      have hbZ : b • Z ∈ homL D L L' := by
        refine Submodule.subset_span ?_
        intro x hx
        refine (hL'.2.2 _).mpr ?_
        intro y hy
        rw [stdH_eq, Matrix.smul_mulVec]
        have : (∑ i, D.host.conj (y i) * (b • Z.mulVec x) i) =
            b * ∑ i, D.host.conj (y i) * Z.mulVec x i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul]; ring
        rw [this]
        exact ideal_mul_inverse_integral D hb (hZ x hx y hy)
      have : (b * a) • Z = a • (b • Z) := by rw [smul_smul, mul_comm]
      rw [this]
      exact Submodule.subset_span ⟨a, ha, b • Z, hbZ, rfl⟩
    · intro x y hx hy
      rw [add_smul]
      exact Submodule.add_mem _ hx hy
  simpa using key 1 (one_mem_ideal_mul_inverse D)

theorem rank_one_mem_hom_lattice {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    {x : Fin N → D.host.E} (hx : x ∈ L) {y : Fin N' → D.host.E} (hy : y ∈ L') :
    (Matrix.of fun i j => y i * D.host.conj (x j)) ∈ homL D L L' := by
  refine Submodule.subset_span ?_
  intro v hv
  obtain ⟨r, hr⟩ := (hL.2.2 v).mp hv x hx
  have e : (Matrix.of fun i j => y i * D.host.conj (x j)).mulVec v = r • y := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, hr, stdH_eq]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact L'.smul_mem r hy

theorem hYY_rank1 {N N' : ℕ} (X : Matrix (Fin N') (Fin N) D.host.E) (a : D.host.E)
    (x : Fin N → D.host.E) (y : Fin N' → D.host.E) :
    hYY D X (a • Matrix.of fun i j => y i * D.host.conj (x j)) =
      Algebra.trace D.host.K D.host.E
        ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
  unfold hYY
  congr 1
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, CU.conj_conj,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem alg_step (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (X : Matrix (Fin N') (Fin N) D.host.E)
    (hX : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, hYY D X Y = ((c : 𝓞 D.host.K) : D.host.K)) :
    X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
  obtain ⟨c0, hc0, hc0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
  have hdvd : cc ∣ Ideal.span {c0} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨cc', hcc'⟩ := hdvd
  have hc0K : ((c0 : D.host.K)) ≠ 0 := by
    intro h; apply hc0ne; exact RingOfIntegers.ext (by simpa using h)
  have hc0E : (((c0 : D.host.K) : D.host.E)) ≠ 0 := by
    intro h; apply hc0K; exact Subtype.ext (by simpa using h)
  have key : ∀ e ∈ cc', ((((e : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      YYl D L L' := by
    intro e he
    apply hom_step L L' hA.2.2.2
    intro x hx y hy
    rw [mm_unimod]
    intro a ha
    obtain ⟨c', hc', hh⟩ := hX _
      (Submodule.subset_span ⟨a, ha, _, rank_one_mem_hom_lattice L L' hA.2.2.1 hx hy, rfl⟩)
    rw [hYY_rank1] at hh
    have hmem : c' * e ∈ Ideal.span {c0} := by rw [hcc']; exact Ideal.mul_mem_mul hc' he
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨r, ?_⟩
    set k : D.host.K := (e : D.host.K) / (c0 : D.host.K)
    have e1 : (∑ i, D.host.conj (y i) * ((k : D.host.E) • X).mulVec x i) * D.host.conj a =
        k • ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
      rw [Algebra.smul_def, Matrix.smul_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.algebraMap_apply]
      ring
    rw [e1, LinearMap.map_smul_of_tower, hh, smul_eq_mul]
    have hr' : ((r : D.host.K)) * (c0 : D.host.K) = (c' : D.host.K) * (e : D.host.K) := by
      have := congrArg (fun t : 𝓞 D.host.K => (t : D.host.K)) hr
      simpa using this
    show (r : D.host.K) = k * (c' : D.host.K)
    simp only [k]
    field_simp
    linear_combination hr'
  have main : ∀ z ∈ cc * cc', ((((z : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
        B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro c hc e he
      refine AddSubgroup.subset_closure ⟨c, hc, _, key e he, ?_⟩
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · intro u w hu hw
      have : ((((u + w : 𝓞 D.host.K) : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E) • X =
          ((((u : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X +
          ((((w : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X := by
        rw [← add_smul]; congr 1; push_cast; ring
      rw [this]
      exact AddSubgroup.add_mem _ hu hw
  have h1 := main c0 (by rw [← hcc']; exact Ideal.mem_span_singleton_self c0)
  rwa [div_self hc0K, IntermediateField.coe_one, one_smul] at h1

variable (D) in

theorem coord (δ : ℂ) (hδ : δ ≠ 0) (u : D.what₂.Tau → ℂ)
    (hu : ∀ y : D.host.E, ∃ k : D.host.K,
      ∑ τ, u τ * embT D τ y = δ * D.host.φ₀ (k : D.host.E)) :
    ∃ x : D.host.E, ∀ τ, u τ = δ * embT D τ x := by
  choose g hg using hu
  have ginj : ∀ k k' : D.host.K, δ * D.host.φ₀ (k : D.host.E) = δ * D.host.φ₀ (k' : D.host.E) →
      k = k' := fun k k' h => Subtype.ext (D.host.φ₀.injective (mul_left_cancel₀ hδ h))
  let lam : D.host.E →ₗ[D.host.K] D.host.K :=
    { toFun := g
      map_add' := fun y1 y2 => by
        apply ginj
        calc δ * D.host.φ₀ (g (y1 + y2) : D.host.E)
            = ∑ τ, u τ * embT D τ (y1 + y2) := (hg _).symm
          _ = ∑ τ, u τ * embT D τ y1 + ∑ τ, u τ * embT D τ y2 := by
              simp only [map_add, mul_add, Finset.sum_add_distrib]
          _ = δ * D.host.φ₀ (g y1 : D.host.E) + δ * D.host.φ₀ (g y2 : D.host.E) := by
              rw [hg, hg]
          _ = δ * D.host.φ₀ ((g y1 + g y2 : D.host.K) : D.host.E) := by
              simp only [IntermediateField.coe_add, map_add]; ring
      map_smul' := fun k y => by
        apply ginj
        calc δ * D.host.φ₀ (g (k • y) : D.host.E)
            = ∑ τ, u τ * embT D τ (k • y) := (hg _).symm
          _ = D.host.φ₀ (k : D.host.E) * ∑ τ, u τ * embT D τ y := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul,
                FL.embT_K D τ _ k.2]
              ring
          _ = δ * D.host.φ₀ ((k * g y : D.host.K) : D.host.E) := by
              rw [hg, IntermediateField.coe_mul, map_mul]; ring }
  have hB := traceForm_nondegenerate D.host.K D.host.E
  set x := ((Algebra.traceForm D.host.K D.host.E).toDual hB).symm lam with hxdef
  have hx : ∀ y, Algebra.trace D.host.K D.host.E (x * y) = g y := by
    intro y
    have := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := Algebra.traceForm D.host.K D.host.E) (hB := hB) lam y
    rw [Algebra.traceForm_apply] at this
    exact this
  refine ⟨x, ?_⟩
  set u' : D.what₂.Tau → ℂ := fun τ => u τ - δ * embT D τ x with hu'
  have h0 : ∀ y : D.host.E, ∑ τ, u' τ * embT D τ y = 0 := by
    intro y
    have h1 := FL.sum_tau_trace D (x * y)
    rw [hx] at h1
    simp only [u', sub_mul, Finset.sum_sub_distrib]
    rw [hg y, ← h1, Finset.mul_sum]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul]; ring
  have hspan : ∀ z ∈ Submodule.span ℝ (Set.range (fun b : 𝓞 D.host.E => FL.embP D (b : D.host.E))),
      ∑ τ, u' τ * z τ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact h0 _
    | zero => simp
    | add z w _ _ h1 h2 =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
    | smul r z _ h1 =>
      have : ∑ τ, u' τ * (r • z) τ = (r : ℂ) * ∑ τ, u' τ * z τ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Pi.smul_apply, Complex.real_smul]; ring
      rw [this, h1, mul_zero]
  have hc := hspan (fun τ => starRingEnd ℂ (u' τ)) (by rw [FL.span_embP]; trivial)
  have hsq : ∑ τ, (Complex.normSq (u' τ) : ℂ) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Complex.mul_conj]
  have hsq' : ∑ τ, Complex.normSq (u' τ) = 0 := by exact_mod_cast hsq
  intro τ
  have hτ := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Complex.normSq_nonneg (u' τ))).mp hsq'
    τ (Finset.mem_univ _)
  rw [Complex.normSq_eq_zero] at hτ
  have : u τ - δ * embT D τ x = 0 := hτ
  exact sub_eq_zero.mp this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SD

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

def CurveSelfDualRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∀ x : ℂ, (∀ w ∈ lamOf D cc δ, ∃ b : ℤ,
      (x * starRingEnd ℂ w / (area (lamOf D cc δ) : ℂ)).im = b) → x ∈ lamOf D cc δ

namespace SD

variable {D : D7}

theorem mem_La_of {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {X : Matrix (Fin N') (Fin N) D.host.E}
    (hX : X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z}) :
    (fun τ i j => δ * embT D τ (X i j) : VC D N N') ∈ La D (tor0 D cc δ) L L' := by
  induction hX using AddSubgroup.closure_induction with
  | mem B hB =>
    obtain ⟨c, hc, Z, hZ, rfl⟩ := hB
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Z, hZ, ?_⟩
    funext τ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, embV, tor0]
    rw [FL.embT_K D τ _ (c : D.host.K).2]
    ring
  | zero =>
    have : (fun τ i j => δ * embT D τ ((0 : Matrix (Fin N') (Fin N) D.host.E) i j) : VC D N N') = 0 := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.zero_mem _
  | add A B _ _ h1 h2 =>
    have : (fun τ i j => δ * embT D τ ((A + B) i j) : VC D N N') =
        (fun τ i j => δ * embT D τ (A i j)) + (fun τ i j => δ * embT D τ (B i j)) := by
      funext τ i j; simp [mul_add]
    rw [this]; exact AddSubgroup.add_mem _ h1 h2
  | neg A _ h1 =>
    have : (fun τ i j => δ * embT D τ ((-A) i j) : VC D N N') =
        -(fun τ i j => δ * embT D τ (A i j)) := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.neg_mem _ h1

end SD

theorem SelfDualRec_of_curve (hC : CurveSelfDualRec) : SelfDualRec := by
  intro D cc hcc δ _ h0 N N' L L' hA v hv
  set ℓ : Matrix (Fin N') (Fin N) D.host.E → ℂ := fun Y =>
    ∑ τ, ∑ i, ∑ j, v τ i j * starRingEnd ℂ (embT D τ (Y i j)) with hℓdef

  have hℓ : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, ℓ Y = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
    intro Y hY
    apply FL.lam_mem
    apply hC D cc hcc δ h0
    intro w hw
    obtain ⟨b, hb⟩ := hv (w • embV D (tor0 D cc δ) Y)
      (AddSubgroup.subset_closure ⟨w, hw, Y, hY, rfl⟩)
    refine ⟨b, ?_⟩
    rw [← hb]
    congr 1
    unfold Hf
    congr 1
    simp only [ℓ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, embV, tor0]
    ring

  obtain ⟨M, hM, hMY⟩ := FL.YY_lower D L L' hA.2.2.1 hA.2.2.2
  have hcoord : ∀ i j, ∃ x : D.host.E, ∀ τ, v τ i j = δ * embT D τ x := by
    intro i j
    apply SD.coord D δ h0
    intro y
    obtain ⟨m, hm, hmy⟩ := FL.exists_int_mul D {D.host.conj y}
    have hy' := hmy _ (Finset.mem_singleton_self _)
    set A : Matrix (Fin N') (Fin N) D.host.E :=
      Matrix.of fun i' j' => if i' = i ∧ j' = j then (m : D.host.E) * D.host.conj y else 0
    have hAint : ∀ i' j', IsIntegral ℤ (A i' j') := by
      intro i' j'
      simp only [A, Matrix.of_apply]
      split_ifs
      · exact hy'
      · exact isIntegral_zero
    obtain ⟨c, hc, hcY⟩ := hℓ _ (hMY A hAint)
    have hMm : ((M * m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hM hm
    have hval : ℓ ((M : D.host.E) • A) = ((M * m : ℤ) : ℂ) * ∑ τ, v τ i j * embT D τ y := by
      simp only [ℓ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp only [A, Matrix.smul_apply, Matrix.of_apply, and_self, if_true, smul_eq_mul,
          map_mul, map_intCast, FL.emb_conj, Complex.conj_conj, map_intCast]
        push_cast; ring
      · intro j' _ hj'
        simp [A, hj']
      · intro h; exact absurd (Finset.mem_univ j) h
      · intro i' _ hi'
        refine Finset.sum_eq_zero fun j' _ => ?_
        simp [A, hi']
      · intro h; exact absurd (Finset.mem_univ i) h
    refine ⟨((c : D.host.K)) / ((M * m : ℤ) : D.host.K), ?_⟩
    rw [hval] at hcY
    rw [IntermediateField.coe_div, map_div₀]
    have e2 : D.host.φ₀ ((((M * m : ℤ) : D.host.K)) : D.host.E) = ((M * m : ℤ) : ℂ) := by
      simp
    rw [e2]
    field_simp
    linear_combination hcY
  choose X hXv using hcoord

  have hXc : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, hYY D (Matrix.of X) Y = ((c : 𝓞 D.host.K) : D.host.K) := by
    intro Y hY
    obtain ⟨c, hc, hcY⟩ := hℓ Y hY
    refine ⟨c, hc, ?_⟩
    have e1 : ℓ Y = δ * D.host.φ₀ ((hYY D (Matrix.of X) Y : D.host.K) : D.host.E) := by
      unfold hYY
      rw [← FL.sum_tau_trace, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [map_sum, map_mul, FL.emb_conj, Finset.mul_sum, Matrix.of_apply, hXv]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1] at hcY
    exact Subtype.ext (D.host.φ₀.injective (mul_left_cancel₀ h0 hcY))

  have hXS := SD.alg_step cc hcc.1 L L' hA (Matrix.of X) hXc
  have hv' : v = (fun τ i j => δ * embT D τ ((Matrix.of X) i j) : VC D N N') := by
    funext τ i j
    exact hXv i j τ
  rw [hv']
  exact SD.mem_La_of hXS

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CS

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Polynomial

theorem im_comb (w1 w2 : ℂ) (m1 n1 m2 n2 : ℤ) :
    (starRingEnd ℂ ((m1 : ℂ) * w1 + (n1 : ℂ) * w2) * ((m2 : ℂ) * w1 + (n2 : ℂ) * w2)).im =
      ((m1 * n2 - n1 * m2 : ℤ) : ℝ) * (starRingEnd ℂ w1 * w2).im := by
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem area_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hb : ∀ w ∈ Λ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) :
    area Λ = |(starRingEnd ℂ w1 * w2).im| := by
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.mpr hD, w1, h1, w2, h2, rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨m1, n1, rfl⟩ := hb u hu
  obtain ⟨m2, n2, rfl⟩ := hb v hv
  rw [im_comb, abs_mul] at ha ⊢
  have hk : (m1 * n2 - n1 * m2 : ℤ) ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have : (1 : ℝ) ≤ |((m1 * n2 - n1 * m2 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  nlinarith [abs_nonneg (starRingEnd ℂ w1 * w2).im]

theorem cramer (x w1 w2 : ℂ) :
    x * ((starRingEnd ℂ w1 * w2).im : ℂ) =
      ((x * starRingEnd ℂ w1).im : ℂ) * w2 - ((x * starRingEnd ℂ w2).im : ℂ) * w1 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem dual_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) (harea : area Λ = |(starRingEnd ℂ w1 * w2).im|)
    (x : ℂ) (hx : ∀ w ∈ Λ, ∃ b : ℤ, (x * starRingEnd ℂ w / (area Λ : ℂ)).im = b) : x ∈ Λ := by
  obtain ⟨b1, hb1⟩ := hx w1 h1
  obtain ⟨b2, hb2⟩ := hx w2 h2
  rw [Complex.div_ofReal_im, harea] at hb1 hb2
  set D := (starRingEnd ℂ w1 * w2).im with hDdef
  have hA : |D| ≠ 0 := abs_ne_zero.mpr hD
  have e1 : (x * starRingEnd ℂ w1).im = b1 * |D| := (div_eq_iff hA).mp hb1
  have e2 : (x * starRingEnd ℂ w2).im = b2 * |D| := (div_eq_iff hA).mp hb2
  have hc := cramer x w1 w2
  rw [← hDdef, e1, e2] at hc
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have m1 : (b1 : ℂ) * w2 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h2 b1
  have m2 : (b2 : ℂ) * w1 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h1 b2
  rcases abs_cases D with ⟨hDa, -⟩ | ⟨hDa, -⟩
  · have : x = (b1 : ℂ) * w2 - (b2 : ℂ) * w1 := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.sub_mem m1 m2
  · have : x = -((b1 : ℂ) * w2 - (b2 : ℂ) * w1) := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.neg_mem (Λ.sub_mem m1 m2)

variable (D : D7)

theorem s_sq : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem d_pos : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

theorem K_repr (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ p q : ℚ, x = (p : D.host.E) + (q : D.host.E) * D.host.sqd := by
  first | exact UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr .. | (apply UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr <;> assumption) | (apply @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr <;> assumption) | (apply @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr D x hx | exact @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr D x | exact @UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr D

theorem embedding_sqrt_neg_d : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  D.host.φ₀_mem

theorem finrank_K : Module.finrank ℚ D.host.K = 2 := by
  set s := D.host.sqd
  have hs := s_sq D
  have hd := d_pos D
  have hmon : (X ^ 2 + C (D.host.d : ℚ)).Monic := monic_X_pow_add_C _ two_ne_zero
  have hev : aeval s (X ^ 2 + C (D.host.d : ℚ)) = 0 := by
    rw [map_add, map_pow, aeval_X, aeval_C, hs]
    simp
  have hirr : Irreducible (X ^ 2 + C (D.host.d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_add_C]; simp
    · intro r hr
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hr
      nlinarith [sq_nonneg r]
  have hint : IsIntegral ℚ s := ⟨_, hmon, by rw [← aeval_def]; exact hev⟩
  have hmin : minpoly ℚ s = X ^ 2 + C (D.host.d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank hint
  rw [hmin, natDegree_X_pow_add_C] at this
  exact this

theorem cc_basis (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ c1 ∈ cc, ∃ c2 ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = (m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2) ∧
      ∀ p q : ℚ, (p : D.host.E) * ((c1 : D.host.K) : D.host.E) +
        (q : D.host.E) * ((c2 : D.host.K) : D.host.E) = 0 → p = 0 ∧ q = 0 := by
  have hr : Module.finrank ℤ (𝓞 D.host.K) = 2 := by rw [RingOfIntegers.rank, finrank_K]
  let b := Module.finBasisOfFinrankEq ℤ (𝓞 D.host.K) hr
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨bI 0, (bI 0).2, bI 1, (bI 1).2, ?_, ?_⟩
  · intro c hc
    have h := bI.sum_repr ⟨c, hc⟩
    rw [Fin.sum_univ_two] at h
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h2 := congrArg (fun t : cc => (t : 𝓞 D.host.K)) h
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul] at h2
    exact h2.symm
  · intro p q hpq
    have hli : LinearIndependent ℤ ![bI 0, bI 1] := by
      have : ![bI 0, bI 1] = ⇑bI := by ext i; fin_cases i <;> rfl
      rw [this]; exact bI.linearIndependent
    have key := LinearIndependent.pair_iff.mp hli (p.num * q.den) (q.num * p.den) (by
      apply Subtype.ext
      apply RingOfIntegers.ext
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, Submodule.coe_zero]
      have hc : ∀ n : ℤ, ((((n : 𝓞 D.host.K) : D.host.K)) : D.host.E) = (n : D.host.E) := by
        intro n
        have h1 : ((n : 𝓞 D.host.K) : D.host.K) = (n : D.host.K) :=
          map_intCast (algebraMap (𝓞 D.host.K) D.host.K) n
        rw [h1]; exact map_intCast D.host.K.val n
      push_cast [Int.cast_natCast, hc]
      have hp : (p : D.host.E) = (p.num : D.host.E) / (p.den : D.host.E) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      have hq : (q : D.host.E) = (q.num : D.host.E) / (q.den : D.host.E) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      rw [hp, hq] at hpq
      have hpd : (p.den : D.host.E) ≠ 0 := by exact_mod_cast p.den_nz
      have hqd : (q.den : D.host.E) ≠ 0 := by exact_mod_cast q.den_nz
      field_simp at hpq
      linear_combination hpq)
    constructor
    · have : p.num = 0 := by
        rcases mul_eq_zero.mp key.1 with h | h
        · exact h
        · exact absurd h (by exact_mod_cast q.den_nz)
      exact Rat.num_eq_zero.mp this
    · have : q.num = 0 := by
        rcases mul_eq_zero.mp key.2 with h | h
        · exact h
        · exact absurd h (by exact_mod_cast p.den_nz)
      exact Rat.num_eq_zero.mp this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CS

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

theorem CS.coe_intO (D : D7) (n : ℤ) :
    ((((n : 𝓞 D.host.K) : D.host.K)) : D.host.E) = (n : D.host.E) := by
  have h1 : ((n : 𝓞 D.host.K) : D.host.K) = (n : D.host.K) :=
    map_intCast (algebraMap (𝓞 D.host.K) D.host.K) n
  rw [h1]; exact map_intCast D.host.K.val n

theorem CS.im_conj_mul (δ a b : ℂ) :
    (starRingEnd ℂ (δ * a) * (δ * b)).im = Complex.normSq δ * (starRingEnd ℂ a * b).im := by
  have : starRingEnd ℂ (δ * a) * (δ * b) = (starRingEnd ℂ δ * δ) * (starRingEnd ℂ a * b) := by
    rw [map_mul]; ring
  rw [this, ← Complex.normSq_eq_conj_mul_self, Complex.im_ofReal_mul]

theorem curve_lattice_self_dual : CurveSelfDualRec := by
  intro D cc hcc δ hδ x hx
  obtain ⟨c1, hc1, c2, hc2, hspan, hind⟩ := CS.cc_basis D cc hcc.1
  set w1 := δ * D.host.φ₀ (((c1 : D.host.K) : D.host.E)) with hw1
  set w2 := δ * D.host.φ₀ (((c2 : D.host.K) : D.host.E)) with hw2
  have h1 : w1 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c1, hc1, rfl⟩
  have h2 : w2 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c2, hc2, rfl⟩
  have hb : ∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2 := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
    obtain ⟨m, n, rfl⟩ := hspan c hc
    refine ⟨m, n, ?_⟩
    have e : ((((m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2 : 𝓞 D.host.K) : D.host.K) : D.host.E) =
        (m : D.host.E) * ((c1 : D.host.K) : D.host.E) + (n : D.host.E) * ((c2 : D.host.K) : D.host.E) := by
      rw [← CS.coe_intO D m, ← CS.coe_intO D n]
      rfl
    rw [e, hw1, hw2, map_add, map_mul, map_mul, map_intCast, map_intCast]
    ring
  have hD : (starRingEnd ℂ w1 * w2).im ≠ 0 := by
    obtain ⟨p1, q1, e1⟩ := CS.K_repr D _ (c1 : D.host.K).2
    obtain ⟨p2, q2, e2⟩ := CS.K_repr D _ (c2 : D.host.K).2
    have hφ1 : D.host.φ₀ ((c1 : D.host.K) : D.host.E) =
        (p1 : ℂ) + (q1 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e1, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have hφ2 : D.host.φ₀ ((c2 : D.host.K) : D.host.E) =
        (p2 : ℂ) + (q2 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e2, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have him : (starRingEnd ℂ w1 * w2).im =
        Complex.normSq δ * (((p1 * q2 - q1 * p2 : ℚ) : ℝ) * Real.sqrt D.host.d) := by
      rw [hw1, hw2, CS.im_conj_mul, hφ1, hφ2]
      congr 1
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
        Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im, map_ratCast]
      push_cast
      ring
    rw [him]
    have hsd : 0 < Real.sqrt D.host.d := IO.sqrt_d_pos D
    have hnδ : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
    intro h0
    have hpqR : ((p1 * q2 - q1 * p2 : ℚ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hnδ.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hsd.ne'
    have hpq : p1 * q2 - q1 * p2 = 0 := by exact_mod_cast hpqR
    have hpqE : (p1 : D.host.E) * q2 - q1 * p2 = 0 := by
      have := congrArg (fun t : ℚ => (t : D.host.E)) hpq
      push_cast at this
      exact this
    by_cases hq : q1 = 0 ∧ q2 = 0
    · have r := hind p2 (-p1) (by rw [e1, e2, hq.1, hq.2]; push_cast; ring)
      have hp1 : p1 = 0 := by linarith [r.2]
      have r2 := hind 1 0 (by rw [e1, hp1, hq.1]; push_cast; ring)
      exact one_ne_zero r2.1
    · have r := hind q2 (-q1) (by rw [e1, e2]; push_cast; linear_combination hpqE)
      exact hq ⟨by linarith [r.2], r.1⟩
  exact CS.dual_of_basis _ h1 h2 hD (CS.area_of_basis _ h1 h2 hb hD) x hx

theorem self_dual_lattice : SelfDualRec := SelfDualRec_of_curve curve_lattice_self_dual

theorem LinkThIndep_of_arith' (hA : HfArithRec) : LinkThIndep :=
  LinkThIndep_of_arith hA self_dual_lattice

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
