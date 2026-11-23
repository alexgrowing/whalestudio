import Formalism.SatakeDualWeyl.Statement

open Matrix NumberField ComplexConjugate

namespace Formalism.UG.P

section Den
variable {E : Type} [Field E] [NumberField E]

theorem sf_den {ι : Type} [Finite ι] (f : ι → E) :
    ∃ d : E, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ i, IsIntegral ℤ (d * f i) := by
  classical
  have hZ : ∀ x : ℤ, IsIntegral ℤ (x : E) := fun x => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := x))
  have hQ : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using hQ
  have _ := Fintype.ofFinite ι
  refine ⟨((∏ i, m i : ℤ) : E), ?_, hZ _, ?_⟩
  · exact_mod_cast Finset.prod_ne_zero_iff.2 (fun i _ => hm0 i)
  · intro i
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast
    rw [mul_comm ((m i : ℤ) : E), mul_assoc]
    refine IsIntegral.mul ?_ (hmi i)
    exact_mod_cast hZ (∏ j ∈ Finset.univ.erase i, m j)

end Den

section CS
variable {n : Type} [Fintype n] [DecidableEq n]

theorem sf_expand (A : Matrix n n ℂ) (a b : ℂ) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (a • v + b • u) (a • v + b • u) =
      conj a * a * hform (starRingEnd ℂ) A v v + conj a * b * hform (starRingEnd ℂ) A v u +
      conj b * a * hform (starRingEnd ℂ) A u v + conj b * b * hform (starRingEnd ℂ) A u u := by
  unfold hform
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_mul]
  ring

theorem sf_conj (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    conj (hform (starRingEnd ℂ) A u v) = hform (starRingEnd ℂ) A v u := by
  unfold hform
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_conj, hA]
  ring

theorem sf_cs (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u)
      (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u) =
    hform (starRingEnd ℂ) A u u * (hform (starRingEnd ℂ) A u u * hform (starRingEnd ℂ) A v v
      - conj (hform (starRingEnd ℂ) A u v) * hform (starRingEnd ℂ) A u v) := by
  rw [sf_expand]
  have h1 : conj (hform (starRingEnd ℂ) A u u) = hform (starRingEnd ℂ) A u u := sf_conj A hA u u
  have h2 : hform (starRingEnd ℂ) A v u = conj (hform (starRingEnd ℂ) A u v) := (sf_conj A hA u v).symm
  rw [h2, map_neg, h1]
  ring

theorem sf_map {E : Type} [CommRing E] (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : τ.comp σ = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x y : n → E) :
    τ (hform σ J x y) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (x k)) (fun k => τ (y k)) := by
  unfold hform
  simp only [map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := RingHom.congr_fun hτ (x i)
  simp only [RingHom.comp_apply] at h1
  rw [h1]

theorem sf_gram {A : Type} [CommRing A] (σ : A →+* A) (J M : Matrix n n A) (a b : n) :
    (cT σ M * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  unfold hform cT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sf_single {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix n n A) (i : n) (y : n → A) :
    hform σ J (Pi.single i 1) y = (J *ᵥ y) i := by
  unfold hform
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CS

section B
variable {n : Type} [Fintype n] [DecidableEq n]

theorem sf_sign {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) :
    ∃ s : ℝ, 0 < s * s ∧ ∀ x : n → E, ∃ t : ℝ, τ (hform (σ : E →+* E) J x x) = t ∧
      (x ≠ 0 → 0 < s * t) ∧ 0 ≤ s * t := by
  classical
  have hreal : ∀ a : F, conj (τ (algebraMap F E a)) = τ (algebraMap F E a) := by
    intro a
    have h1 : τ ((σ : E →+* E) (algebraMap F E a)) = conj (τ (algebraMap F E a)) :=
      RingHom.congr_fun hτ _
    have h2 : (σ : E →+* E) (algebraMap F E a) = algebraMap F E a := σ.commutes a
    rw [h2] at h1
    exact h1.symm
  have him : ∀ a : F, (τ (algebraMap F E a)).im = 0 := fun a => Complex.conj_eq_iff_im.1 (hreal a)
  let ι : F →+* ℝ :=
    { toFun := fun a => (τ (algebraMap F E a)).re
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, Complex.mul_re, him a, him b]
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hval : ∀ a : F, τ (algebraMap F E a) = ((ι a : ℝ) : ℂ) := fun a =>
    (Complex.conj_eq_iff_re.1 (hreal a)).symm
  have h00 : τ (hform (σ : E →+* E) J 0 0) = ((0 : ℝ) : ℂ) := by
    unfold hform
    simp
  rcases hdef ι with hpos | hneg
  · refine ⟨1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hpos x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a
  · refine ⟨-1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hneg x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a

theorem sf_bound {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) (g : Matrix n n E)
    (hg : cT (σ : E →+* E) g * J * g = J) (i j : n) :
    ‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖ := by
  classical
  obtain ⟨s, hs, hsign⟩ := sf_sign σ J τ hτ hdef
  have hA : ∀ a b, conj ((J.map τ) b a) = (J.map τ) a b := by
    intro a b
    have h3 : τ ((σ : E →+* E) (J b a)) = conj (τ (J b a)) := RingHom.congr_fun hτ _
    have h4 : (σ : E →+* E) (J b a) = J a b := by
      have h1 : (cT (σ : E →+* E) J) a b = J a b := by rw [hH]
      exact h1
    simp only [Matrix.map_apply]
    rw [← h3, h4]
  have hc : (J * g) i j = hform (σ : E →+* E) J (Pi.single i 1) (fun k => g k j) := by
    rw [sf_single]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hb : hform (σ : E →+* E) J (fun k => g k j) (fun k => g k j) = J j j := by
    rw [← sf_gram, hg]
  have ha : hform (σ : E →+* E) J (Pi.single i 1) (Pi.single i 1) = J i i := by
    rw [sf_single]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hau : τ (J i i) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    rw [← sf_map _ τ hτ, ha]
  have hcu : τ ((J * g) i j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hc]
  have hbv : τ (J j j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (g k j)) (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hb]
  obtain ⟨tw, htw, -, htw0⟩ := hsign ((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E))
  obtain ⟨ta, hta, hta1, -⟩ := hsign (Pi.single i 1 : n → E)
  obtain ⟨tb, htb, -, htb0⟩ := hsign (fun k => g k j)
  have hei : (Pi.single i 1 : n → E) ≠ 0 := by
    intro h
    have h5 := congr_fun h i
    simp at h5
  have hta' := hta1 hei
  rw [ha] at hta
  rw [hb] at htb
  rw [sf_map _ τ hτ] at htw
  have hw : (fun k => τ (((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E)) k)) =
      τ (J i i) • (fun k => τ (g k j)) + (-τ ((J * g) i j)) • (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    funext k
    simp [map_add, map_mul, map_neg]
  rw [hw, hau, hcu, sf_cs _ hA, ← hau, ← hcu, ← hbv, hta, htb] at htw
  rw [← Complex.normSq_eq_conj_mul_self] at htw
  have key : ta * (ta * tb - Complex.normSq (τ ((J * g) i j))) = tw := by exact_mod_cast htw
  have hN : Complex.normSq (τ ((J * g) i j)) = ‖τ ((J * g) i j)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [hN] at key
  have h1 : ‖τ ((J * g) i j)‖ ^ 2 ≤ ta * tb := by
    by_contra hneg
    push_neg at hneg
    have h6 : s * tw < 0 := by
      rw [← key]
      nlinarith
    linarith
  have h3 : ta * tb ≤ |ta| * |tb| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [hta, htb]
  have hn1 : ‖((ta : ℝ) : ℂ)‖ = |ta| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖((tb : ℝ) : ℂ)‖ = |tb| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn1, hn2]
  nlinarith [abs_nonneg ta, abs_nonneg tb, norm_nonneg (τ ((J * g) i j))]

end B

theorem UG_stabilizer_finite : Formalism.UG.StabFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan
  classical
  obtain ⟨dJ, hdJ0, -, hdJ⟩ := sf_den (fun p : n × n => J p.1 p.2)
  obtain ⟨S, hS⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨dL, hdL0, -, hdL⟩ := sf_den (fun p : S × n => (p.1 : n → E) p.2)
  have hΛint : ∀ v ∈ Λ, ∀ k, IsIntegral ℤ (dL * v k) := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem x hx => intro k; exact hdL (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (r • x) k = (algebraMap (𝓞 E) E r) * x k := by
        rw [Pi.smul_apply, Algebra.smul_def]
      rw [this, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hcol : ∀ j : n, ∃ c : E, c ≠ 0 ∧ c • (Pi.single j 1 : n → E) ∈ Λ := by
    intro j
    have hm : (Pi.single j 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; trivial
    obtain ⟨m, f, gg, hsum⟩ := Submodule.mem_span_set'.mp hm
    obtain ⟨d, hd0, -, hd⟩ := sf_den f
    refine ⟨d, hd0, ?_⟩
    rw [← hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun l _ => ?_)
    obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hd l)
    have : d • (f l • (gg l : n → E)) = r • (gg l : n → E) := by
      rw [smul_smul, ← hr, algebraMap_smul]
    rw [this]
    exact Λ.smul_mem r (gg l).2
  choose c hc0 hcΛ using hcol
  let β : (E →+* ℂ) × n × n → ℝ := fun z =>
    ‖z.1 (dJ * dL * c z.2.2)‖ * (‖z.1 (J z.2.1 z.2.1)‖ + ‖z.1 (J z.2.2 z.2.2)‖)
  obtain ⟨B, hB⟩ := (Set.finite_range β).bddAbove
  set T : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  have hmem : ∀ g ∈ level (σ : E →+* E) J Λ, ∀ i j,
      dJ * dL * c j * ((J * (g : Matrix n n E)) i j) ∈ T := by
    intro g hg i j
    have hU : cT (σ : E →+* E) (g : Matrix n n E) * J * (g : Matrix n n E) = J := hg.1
    have hstab : ∀ x : n → E, x ∈ Λ ↔ (g : Matrix n n E) *ᵥ x ∈ Λ := hg.2
    have hgc : (g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E)) ∈ Λ := (hstab _).mp (hcΛ j)
    have hcoord : ∀ k, ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k =
        c j * (g : Matrix n n E) k j := by
      intro k; simp [Matrix.mulVec_smul]
    refine ⟨?_, fun φ => ?_⟩
    · have : dJ * dL * c j * ((J * (g : Matrix n n E)) i j) =
          ∑ k, (dJ * J i k) * (dL * ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k) := by
        simp only [hcoord, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
      rw [this]
      exact IsIntegral.sum _ (fun k _ => (hdJ (i, k)).mul (hΛint _ hgc k))
    · rw [map_mul, norm_mul]
      calc ‖φ (dJ * dL * c j)‖ * ‖φ ((J * (g : Matrix n n E)) i j)‖
          ≤ ‖φ (dJ * dL * c j)‖ * (‖φ (J i i)‖ + ‖φ (J j j)‖) :=
            mul_le_mul_of_nonneg_left (sf_bound σ J φ (hτ φ) hH hdef.2 _ hU i j) (norm_nonneg _)
        _ = β (φ, i, j) := rfl
        _ ≤ B := hB ⟨(φ, i, j), rfl⟩
  have : Finite T := hTfin.to_subtype
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr hdet
  refine Finite.of_injective
    (fun g : level (σ : E →+* E) J Λ => fun i j => (⟨_, hmem g.1 g.2 i j⟩ : T)) ?_
  intro g g' hgg
  have h1 : J * (g.1 : Matrix n n E) = J * (g'.1 : Matrix n n E) := by
    ext i j
    have := congr_arg Subtype.val (congr_fun (congr_fun hgg i) j)
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hdJ0 hdL0) (hc0 j)) this
  exact Subtype.ext (Units.ext (hJu.mul_left_cancel h1))

end Formalism.UG.P
