import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntSum_of :
    CntSum := by
  classical
  intro Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP
  have hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c) := by
    intro c hc u hu
    have e := hP _ (hconj c hc u hu) c hc
    rw [← e]
    congr 1
    group
  let φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K' := fun z =>
    QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, x⟩ ⟨a', x'⟩ he
      simp only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he
      push_cast at he
      have hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K := by
        have e := K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))
        convert e using 1
        group
      have ha : a = a' := by
        rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        push_cast
        exact hK
      subst ha
      have hx1 : r x' * (r x')⁻¹ ∈ M := by simpa using M.one_mem
      have hx2 : r x' * (r x)⁻¹ ∈ M := by
        have e := hnorm (r x) (hKK' (hrK x)) _ he
        convert e using 1
        group
      obtain ⟨x0, _, hu⟩ := hr (r x') (hrK x')
      rw [hu x hx2, hu x' hx1]
    · intro b
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c
      have hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K := by
        rw [hk]
        push_cast
        have e := K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
        convert e using 1
        group
      obtain ⟨x, hx, -⟩ := hr _ hκ
      refine ⟨(QuotientGroup.mk c, x), ?_⟩
      simp only [φ]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      have e := hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx
      convert e using 1
      group
  haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2
  letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _
  have hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2)
      = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z))) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K')
      (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
    simp only [φ]
    rw [hu]
    push_cast
    have hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K' :=
      K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))
    have e := hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)
    rw [mul_assoc h, ← e]
    congr 1
    group
  let g : K' ⧸ M.subgroupOf K' → Γ ⧸ K := fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹
  have hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y)
      = ((Finset.univ.filter (fun b => g b = y)).card : ℂ) := by
    intro y
    have hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' =>
        h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y := by
      refine Finset.filter_congr fun b _ => ?_
      simp only [g]
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rw [QuotientGroup.eq, inv_inv]
    unfold cntFn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  have hsupp : (Function.support fun y : Γ ⧸ K =>
      cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g) := by
    intro y hy
    rw [Function.mem_support, hcnt] at hy
    by_contra hyn
    apply hy
    have e : Finset.univ.filter (fun b => g b = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))
    simp [e]
  have hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹
      = ∑ b, P (Quotient.out (g b))⁻¹ := by
    rw [Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hcnt, Nat.cast_smul_eq_nsmul]
  have hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹
    simp only [g]
    rw [hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]
    exact hP _ (K.inv_mem k.2) _ (Quotient.out b).2
  rw [hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z))))
    (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]
