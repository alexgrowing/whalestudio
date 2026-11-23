import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSumFrobeniusGcdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsBoundedRootsUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusAutomorphismGcdStatement

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

theorem mem_intR_iff (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (x : Kn p K n) : x ∈ GlobalTheory.LKLoc.intR p K n ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap (Kn p K n) (PadicAlgCl p) x) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem comp_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {f : ℕ}
    (hq : qK p K = p ^ f) (r i : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) :
    comp p K hq r i x ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r) := by
  have h : intKQ p K r ≤ (GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)).comap (comp p K hq r i).toRingHom := by
    apply Subring.closure_le.2
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show comp p K hq r i (inclK p K r (a : K)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclK]
      exact mem_Obar_iff.1 a.2
    · show comp p K hq r i (inclQ p K r (b : Qr p r)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclQ, norm_GK]
      exact mem_Obar_iff.1 b.2
  exact h hx

theorem kq_split : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (f r : ℕ), qK p K = p ^ f → 0 < r →
    ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)))
      (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)),
      (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r),
        e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)),
        i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧
      (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  intro p _ K hK f r hq hr
  have hp := (Fact.out : p.Prime)
  have h1r : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hN : ¬ p ∣ p ^ r - 1 := by
    intro h
    have h2 : p ∣ 1 := (Nat.dvd_add_right h).1 (by rw [Nat.sub_add_cancel h1r]; exact dvd_pow_self p hr.ne')
    exact hp.not_dvd_one h2
  have hN0 : p ^ r - 1 ≠ 0 := fun h => hN (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hN0
  have hζmem : ζ ∈ Qr p r := UnramifiedExtensions.mem_Kn_of_pow (Q0 p) (by rw [residue_cardinality_base_field]; exact hζ.pow_eq_one)
  set ζ' : Qr p r := ⟨ζ, hζmem⟩ with hζ'
  have hfr : ∀ i : ℕ, (frobK p (Q0 p) ^ i) ζ = ζ ^ p ^ i := fun i => frobenius_pow_root_of_unity p hN hζ.pow_eq_one i

  have val : ∀ (c : Fin r → K) (i : ℕ),
      ((comp p K hq r i (∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ' ^ (j : ℕ)) : Kn p K (r / Nat.gcd f r)) :
        PadicAlgCl p) = ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) := by
    intro c i
    rw [map_sum, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, comp_inclK, comp_inclQ]
    rw [show ((ζ' : Qr p r) : PadicAlgCl p) = ζ from rfl, hfr]

  have key : ∀ c : Fin r → K, (∀ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ ≤ 1) →
      ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := by
    intro c hc j
    refine GlobalTheory.T.coefficients_bounded_roots_unity p (p ^ r - 1) r hN (fun s => ζ ^ p ^ (s : ℕ)) ?_ ?_ (fun j => (c j : PadicAlgCl p)) ?_ j
    · intro s
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro s t hst
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · apply Fin.ext
        have := s.2; have := t.2
        omega
      · have hlt : ∀ u : Fin r, p ^ (u : ℕ) < p ^ r - 1 := by
          intro u
          have h1 : p ^ (u : ℕ) ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega)
          have h2 : p ^ r = p * p ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
          have h3 : 2 ≤ p ^ (r - 1) := le_trans hp.two_le (by
            calc p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega))
          have h4 : 2 * p ^ (r - 1) ≤ p * p ^ (r - 1) := Nat.mul_le_mul_right _ hp.two_le
          omega
        have h5 := hζ.pow_inj (hlt s) (hlt t) hst
        exact Fin.ext (Nat.pow_right_injective hp.two_le h5)
    · intro s
      obtain ⟨i, hi, heq⟩ := GlobalTheory.T.norm_sum_frobenius_gcd p K hK f r hq hr ζ hζ.pow_eq_one c s
      rw [heq]
      exact hc i hi

  have inj : Function.Injective (eMap p K hq r) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
    have hz : ∀ i < Nat.gcd f r, ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) = 0 := by
      intro i hi
      rw [← val c i]
      have h1 := congrFun hx ⟨i, hi⟩
      rw [eMap_apply] at h1
      rw [h1]
      rfl
    have hc0 : ∀ j, c j = 0 := by
      intro j
      by_contra hcj
      have h1 := key (fun k => ((p : K)⁻¹ * (c j)⁻¹) * c k) (by
        intro i hi
        have h2 : ∑ k : Fin r, (((((p : K)⁻¹ * (c j)⁻¹) * c k : K)) : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) =
            (((p : K)⁻¹ * (c j)⁻¹ : K) : PadicAlgCl p) *
              ∑ k : Fin r, (c k : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [MulMemClass.coe_mul, mul_assoc]
        rw [h2, hz i hi, mul_zero, norm_zero]
        exact zero_le_one) j
      have h3 : ((p : K)⁻¹ * (c j)⁻¹) * c j = (p : K)⁻¹ := by
        rw [mul_assoc, inv_mul_cancel₀ hcj, mul_one]
      simp only [h3] at h1
      have h5 : (((p : K)⁻¹ : K) : PadicAlgCl p) = (p : PadicAlgCl p)⁻¹ := by simp
      rw [h5, norm_inv, norm_p] at h1
      rw [inv_inv] at h1
      have h4 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    simp [hc0]

  haveI hQf : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI hKQf : FiniteDimensional ℚ_[p] (KQ p K r) := inferInstanceAs (FiniteDimensional ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI hLf : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
  have dim : Module.finrank ℚ_[p] (KQ p K r) =
      Module.finrank ℚ_[p] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) := by
    have h1 : Module.finrank ℚ_[p] (KQ p K r) = Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Qr p r) :=
      Module.finrank_tensorProduct (R := ℚ_[p]) (S := ℚ_[p]) (M := K) (M' := Qr p r)
    rw [h1, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr)),
      finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot]
    have h2 : Nat.gcd f r * (r / Nat.gcd f r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)
    calc _ = Module.finrank ℚ_[p] K * (Nat.gcd f r * (r / Nat.gcd f r)) := by rw [h2, mul_one]
      _ = _ := by ring
  have bij : Function.Bijective (eMap p K hq r) := by
    refine ⟨inj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim (f := (eMap p K hq r).toLinearMap)).1 inj
  obtain ⟨τ, hτK, hτm, hτQ⟩ := GlobalTheory.T.exists_frobenius_automorphism_gcd p K hK f r hq hr
  let e0 := AlgEquiv.ofBijective (eMap p K hq r) bij
  have he : ∀ x i, e0 x i = comp p K hq r i x := fun x i => rfl
  have hlast : ∀ x : KQ p K r, comp p K hq r (Nat.gcd f r) x = τ (comp p K hq r 0 x) := by
    have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, comp p K hq r (Nat.gcd f r) y = τ (comp p K hq r 0 y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero =>
        have z1 : comp p K hq r (Nat.gcd f r) (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        have z2 : comp p K hq r 0 (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        rw [z1, z2, map_zero]
      | tmul a b =>
        have h1 : comp p K hq r (Nat.gcd f r) (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) =
            incK p K _ a * incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) :=
          Algebra.TensorProduct.productMap_apply_tmul _ _ a b
        have h2 : comp p K hq r 0 (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) = incK p K _ a * incQ p K hq r b :=
          (Algebra.TensorProduct.productMap_apply_tmul _ _ a b).trans
            (by rw [AlgHom.comp_apply, pow_zero, AlgHom.one_apply])
        rw [h1, h2, map_mul, hτQ, (hτK _).2 (by rw [coe_incK]; exact a.2)]
      | add y z hy hz =>
        have e1 : comp p K hq r (Nat.gcd f r) (y + z) =
            comp p K hq r (Nat.gcd f r) y + comp p K hq r (Nat.gcd f r) z := map_add _ _ _
        have e2 : comp p K hq r 0 (y + z) = comp p K hq r 0 y + comp p K hq r 0 z := map_add _ _ _
        rw [e1, e2, map_add, hy, hz]
    exact h
  refine ⟨e0.toRingEquiv, τ, hτK, hτm, ?_, ?_, ?_, ?_⟩
  · intro a i
    show ((e0 (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a
    rw [he, comp_inclK]
  · intro x i h
    show e0 (sigKQ p K r x) i = e0 x ⟨i.val + 1, h⟩
    rw [he, he, comp_sigKQ]
  · intro x i hi i0 hi0
    show e0 (sigKQ p K r x) i = τ (e0 x i0)
    rw [he, he, comp_sigKQ, hi, hi0, hlast]
  · intro x
    show x ∈ intKQ p K r ↔ ∀ i, e0 x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
    constructor
    · intro hx i
      rw [he]
      exact comp_mem_intR p K hq r i x hx
    · intro h
      obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
      have hc : ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := key c (fun i hi => by
        rw [← val c i, ← mem_intR_iff p K (r / Nat.gcd f r)]
        have h1 := h ⟨i, hi⟩
        rwa [he] at h1)
      have hζi : ζ' ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
        rw [mem_intR_iff p (Q0 p) r]
        exact (UnramifiedExtensions.norm_eq_one_of_pow hN0 hζ.pow_eq_one).le
      apply Subring.sum_mem
      intro j _
      apply Subring.mul_mem
      · apply Subring.subset_closure
        left
        exact ⟨⟨c j, mem_Obar_iff.2 (hc j)⟩, rfl⟩
      · apply Subring.pow_mem
        apply Subring.subset_closure
        right
        exact ⟨⟨ζ', hζi⟩, rfl⟩

end GlobalTheory.LKRes.ResSplit
