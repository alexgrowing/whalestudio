import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmpGen

variable {K : Type} [CommRing K] {D : ℕ}

def twist (x : Fin (D + 1) → K) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial K)) (fun l => Polynomial.C (x l) * Polynomial.X)

theorem twist_homog (x : Fin (D + 1) → K) (n : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous n) :
    twist x T = Polynomial.C (aeval x T) * Polynomial.X ^ n := by
  unfold twist
  rw [coe_eval₂Hom, eval₂_eq', aeval_def, eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hT (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  simp
  ring

def Good (c : ℕ) (A : ℕ → AddSubgroup K) (p : Polynomial K) : Prop :=
  (∀ b < c, p.coeff b = 0) ∧ ∀ q, p.coeff (q + c) ∈ A q

theorem good_zero (c : ℕ) (A : ℕ → AddSubgroup K) : Good c A 0 :=
  ⟨fun _ _ => by simp, fun q => by simpa using (A q).zero_mem⟩

theorem good_add {c : ℕ} {A : ℕ → AddSubgroup K} {p r : Polynomial K} (hp : Good c A p) (hr : Good c A r) :
    Good c A (p + r) :=
  ⟨fun b hb => by simp [hp.1 b hb, hr.1 b hb], fun q => by simpa using (A q).add_mem (hp.2 q) (hr.2 q)⟩

theorem good_int_mul {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : ℤ) :
    Good c A ((a : Polynomial K) * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hp.1 b hb, mul_zero]
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, ← zsmul_eq_mul]
    exact zsmul_mem (hp.2 q) a

theorem good_mul_X {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : K)
    (hA : ∀ q, ∀ f ∈ A q, a * f ∈ A (q + 1)) :
    Good c A (Polynomial.C a * Polynomial.X * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases b with _ | b
    · simp
    · rw [Polynomial.coeff_X_mul, hp.1 b (by omega), mul_zero]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases q with _ | q
    · rcases c with _ | c
      · simp
      · rw [zero_add, Polynomial.coeff_X_mul, hp.1 c (by omega), mul_zero]; exact (A 0).zero_mem
    · rw [show q + 1 + c = (q + c) + 1 by omega, Polynomial.coeff_X_mul]
      exact hA q _ (hp.2 q)

theorem good_twist_mul (x : Fin (D + 1) → K) {c : ℕ} {A : ℕ → AddSubgroup K}
    (hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1)) (r : MvPolynomial (Fin (D + 1)) ℤ) :
    ∀ p : Polynomial K, Good c A p → Good c A (twist x r * p) := by
  induction r using MvPolynomial.induction_on with
  | C a => intro p hp; simpa [twist] using good_int_mul hp a
  | add r s hr hs => intro p hp; rw [map_add, add_mul]; exact good_add (hr p hp) (hs p hp)
  | mul_X r l hr =>
    intro p hp
    have h1 : twist x (r * X l) * p = twist x r * (Polynomial.C (x l) * Polynomial.X * p) := by
      simp [twist]; ring
    rw [h1]
    exact hr _ (good_mul_X hp (x l) (hA · l))

theorem exists_finite_homogeneous_generators : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  intro K _ D c x ι _ w Λ hx hw
  classical
  letI : Module (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) := (twist x).toModule
  have hsmul : ∀ (r : MvPolynomial (Fin (D + 1)) ℤ) (p : Polynomial K), r • p = twist x r * p := fun _ _ => rfl
  let S : Set (ℕ × K) := {g | g.2 ∈ Λ g.1}
  let v : ℕ × K → Polynomial K := fun g => Polynomial.C g.2 * Polynomial.X ^ (g.1 + c)
  let M : Submodule (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) :=
    Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' S)
  let ψ : (ι → MvPolynomial (Fin (D + 1)) ℤ) →ₗ[MvPolynomial (Fin (D + 1)) ℤ] Polynomial K :=
    Fintype.linearCombination (MvPolynomial (Fin (D + 1)) ℤ) (fun i => Polynomial.C (w i))
  have hle : M ≤ LinearMap.range ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨q, f⟩, hf, rfl⟩
    obtain ⟨T, hT, rfl⟩ := hw q f hf
    refine ⟨T, ?_⟩
    simp only [ψ, v, Fintype.linearCombination_apply, hsmul, twist_homog x _ _ (hT _), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul]; ring
  have hfg : M.FG := by
    have h1 : (M.comap ψ).FG := IsNoetherian.noetherian _
    have h2 := h1.map ψ
    rwa [Submodule.map_comap_eq_of_le hle] at h2
  obtain ⟨S0, hS0⟩ := hfg
  have hT : ∀ s ∈ S0, ∃ T : Finset (Polynomial K), ↑T ⊆ v '' S ∧
      s ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (T : Set (Polynomial K)) := fun s hs =>
    Submodule.mem_span_finite_of_mem_span (by
      have h := Submodule.subset_span (R := MvPolynomial (Fin (D + 1)) ℤ) (s := (S0 : Set (Polynomial K))) hs
      rw [hS0] at h; exact h)
  choose! Tf hTf hsT using hT
  obtain ⟨G, hGS, hGT⟩ := (Finset.subset_set_image_iff (s := S) (t := S0.biUnion Tf) (f := v)).mp (by
    intro p hp
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hp
    obtain ⟨s, hs, hp⟩ := hp
    exact hTf s hs hp)
  refine ⟨G, fun g hg => hGS hg, ?_⟩
  set A : ℕ → AddSubgroup K := fun q => AddSubgroup.closure
    {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} with hAdef
  have hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1) := by
    intro q l f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨g, hg, α, hα, rfl⟩ := hf
      refine AddSubgroup.subset_closure ⟨g, hg, α + Pi.single l 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
        simp; omega
      · have : ∏ i, x i ^ (Pi.single l 1 : Fin (D + 1) → ℕ) i = x l := by
          rw [Finset.prod_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
          simp
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, this]; ring
    | zero => simpa using (A (q + 1)).zero_mem
    | add a b _ _ ha hb => rw [mul_add]; exact (A (q + 1)).add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact (A (q + 1)).neg_mem ha
  have hgood : ∀ p ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))), Good c A p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨g, hg, rfl⟩ := hp
      refine ⟨fun b hb => ?_, fun q => ?_⟩
      · simp only [v, Polynomial.coeff_C_mul_X_pow]; rw [if_neg (by omega)]
      · simp only [v, Polynomial.coeff_C_mul_X_pow]
        by_cases hq : q = g.1
        · subst hq; rw [if_pos rfl]
          exact AddSubgroup.subset_closure ⟨g, hg, 0, by simp, by simp⟩
        · rw [if_neg (by omega)]; exact (A q).zero_mem
    | zero => exact good_zero c A
    | add a b _ _ ha hb => exact good_add ha hb
    | smul r a _ ha => rw [hsmul]; exact good_twist_mul x hA r a ha
  intro q f hf
  have hmem : v (q, f) ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))) := by
    rw [← Finset.coe_image, hGT]
    have : v (q, f) ∈ M := Submodule.subset_span ⟨(q, f), hf, rfl⟩
    rw [← hS0] at this
    refine Submodule.span_le.mpr ?_ this
    intro s hs
    exact Submodule.span_mono (by
      intro p hp; simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]; exact ⟨s, hs, hp⟩) (hsT s hs)
  have h := (hgood _ hmem).2 q
  simp only [v, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h
  exact h

end GlobalTheory.HSAmpGen
