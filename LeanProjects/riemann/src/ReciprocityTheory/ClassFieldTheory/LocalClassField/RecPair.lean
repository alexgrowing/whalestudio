import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_lift_char (χ : charGrp (GK p K)) : ∃ t : GK p K → ℚ, IsLocallyConstant t ∧
    ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ.1 (Additive.ofMul g) :=
  ⟨fun g => (χ.1 (Additive.ofMul g)).out,
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp Quotient.out,
    fun _ => QuotientAddGroup.out_eq' _⟩

theorem exists_isPairClass_of_inv {a : (kbarT p K).V} (ha : ∀ g, (kbarT p K).rho g a = a) (χ : charGrp (GK p K)) :
    ∃ c, IsPairClass p K a χ c := by
  obtain ⟨t, ht, htχ⟩ := exists_lift_char χ
  obtain ⟨m, hm⟩ := exists_defect χ.1 t htχ
  obtain ⟨z, hz, hzv⟩ := exists_defect_cocycle (kbarT p K) ha ht hm
  exact ⟨_, t, m, z, hz, ht, htχ, hm, hzv, rfl⟩

theorem IsPairClass.unique_of_inv {a : (kbarT p K).V} (ha : ∀ g, (kbarT p K).rho g a = a) {χ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K a χ c') : c = c' := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨t', m', z', hz', ht', htχ', hm', hzv', rfl⟩ := h'
  exact defect_cls_eq (kbarT p K) ha ht ht' (fun g => (htχ g).trans (htχ' g).symm) hm hm' hz hz' hzv hzv'

theorem IsPairClass.add_left {a b : (kbarT p K).V} (hb : ∀ g, (kbarT p K).rho g b = b) {χ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K b χ c') :
    IsPairClass p K (a + b) χ (c + c') := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨z', hz', hzv'⟩ := exists_defect_cocycle (kbarT p K) hb ht hm
  have e : c' = (kbarT p K).coch.cls 2 z' hz' :=
    IsPairClass.unique_of_inv hb h' ⟨t, m, z', hz', ht, htχ, hm, hzv', rfl⟩
  subst e
  refine ⟨t, m, z + z', Cx.d_add_eq_zero hz hz', ht, htχ, hm, fun g => ?_, rfl⟩
  show z.1 g + z'.1 g = _
  rw [hzv, hzv', smul_add]

theorem IsPairClass.add_right {a : (kbarT p K).V} {χ ψ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K a ψ c') :
    IsPairClass p K a (χ + ψ) (c + c') := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨t', m', z', hz', ht', htχ', hm', hzv', rfl⟩ := h'
  refine ⟨t + t', m + m', z + z', Cx.d_add_eq_zero hz hz', ht.add ht', fun g => ?_, fun g => ?_, fun g => ?_, rfl⟩
  · show (QuotientAddGroup.mk (t g + t' g) : QZ) = χ.1 (Additive.ofMul g) + ψ.1 (Additive.ofMul g)
    rw [QuotientAddGroup.mk_add, htχ, htχ']
  · show ((m g + m' g : ℤ) : ℚ) = (t (g 0) + t' (g 0)) + (t (g 1) + t' (g 1)) - (t (g 0 * g 1) + t' (g 0 * g 1))
    rw [Int.cast_add, hm, hm']; ring
  · show z.1 g + z'.1 g = (m g + m' g) • a
    rw [hzv, hzv', add_smul]

theorem exists_isPairClass (a : Kˣ) (χ : charGrp (GK p K)) :
    ∃ c, IsPairClass p K (ofK p K (Additive.ofMul a)) χ c :=
  exists_isPairClass_of_inv (fun g => kbarT_rho_ofK g _) χ

theorem IsPairClass.unique {a : Kˣ} {χ : charGrp (GK p K)} {c c' : Br p K}
    (h : IsPairClass p K (ofK p K (Additive.ofMul a)) χ c)
    (h' : IsPairClass p K (ofK p K (Additive.ofMul a)) χ c') : c = c' :=
  IsPairClass.unique_of_inv (fun g => kbarT_rho_ofK g _) h h'

theorem isPairClass_pairBr (a : Kˣ) (χ : charGrp (GK p K)) :
    IsPairClass p K (ofK p K (Additive.ofMul a)) χ (pairBr p K a χ) := by
  unfold pairBr
  rw [dif_pos (exists_isPairClass a χ)]
  exact (exists_isPairClass a χ).choose_spec

theorem pairBr_mul (a b : Kˣ) (χ : charGrp (GK p K)) :
    pairBr p K (a * b) χ = pairBr p K a χ + pairBr p K b χ := by
  refine IsPairClass.unique (isPairClass_pairBr (a * b) χ) ?_
  rw [ofMul_mul, map_add]
  exact (isPairClass_pairBr a χ).add_left (fun g => kbarT_rho_ofK g _) (isPairClass_pairBr b χ)

theorem pairBr_add (a : Kˣ) (χ ψ : charGrp (GK p K)) :
    pairBr p K a (χ + ψ) = pairBr p K a χ + pairBr p K a ψ :=
  IsPairClass.unique (isPairClass_pairBr a (χ + ψ)) ((isPairClass_pairBr a χ).add_right (isPairClass_pairBr a ψ))

theorem pairK_mul (a b : Kˣ) (χ : charGrp (GK p K)) : pairK p K (a * b) χ = pairK p K a χ + pairK p K b χ := by
  unfold pairK
  rw [pairBr_mul, map_add]

theorem pairK_add (a : Kˣ) (χ ψ : charGrp (GK p K)) : pairK p K a (χ + ψ) = pairK p K a χ + pairK p K a ψ := by
  unfold pairK
  rw [pairBr_add, map_add]

theorem pairK_one (χ : charGrp (GK p K)) : pairK p K 1 χ = 0 := by
  have h := pairK_mul 1 1 χ
  rw [mul_one] at h
  simpa using h

theorem pairK_zero (a : Kˣ) : pairK p K a 0 = 0 := by
  have h := pairK_add a 0 0
  rw [add_zero] at h
  simpa using h

theorem pairK_inv (a : Kˣ) (χ : charGrp (GK p K)) : pairK p K a⁻¹ χ = - pairK p K a χ := by
  apply eq_neg_of_add_eq_zero_left
  rw [← pairK_mul, inv_mul_cancel, pairK_one]

theorem pairK_pow (a : Kˣ) (n : ℕ) (χ : charGrp (GK p K)) : pairK p K (a ^ n) χ = n • pairK p K a χ := by
  induction n with
  | zero => rw [pow_zero, pairK_one, zero_smul]
  | succ n ih => rw [pow_succ, pairK_mul, ih, succ_nsmul]

theorem pairK_nsmul (a : Kˣ) (n : ℕ) (χ : charGrp (GK p K)) : pairK p K a (n • χ) = n • pairK p K a χ := by
  induction n with
  | zero => rw [zero_smul, pairK_zero, zero_smul]
  | succ n ih => rw [succ_nsmul, pairK_add, ih, succ_nsmul]

end ReciprocityTheory.DiscreteGroups.LocalClassField
