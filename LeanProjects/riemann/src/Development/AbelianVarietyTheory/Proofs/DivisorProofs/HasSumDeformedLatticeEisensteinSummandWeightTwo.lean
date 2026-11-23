import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring

variable [IsCMField E]

theorem defCoord_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (a b : maximalRealSubfield E) (i : I) :
    defCoord φ z ((a : E) + (b : E) * θ) i =
      (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I) * latPt (modPt φ e θ z) (a, b) (e i) := by
  have h1 := one_add_ne_zero hz i
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [defCoord, latPt, modPt, Equiv.symm_apply_apply, map_add, map_mul, he, Complex.conj_ofReal]
  field_simp
  ring

theorem defTerm_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (σ : ℂ) (a b : maximalRealSubfield E) :
    defTerm φ 2 z σ ((a : E) + (b : E) * θ) =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisTerm 2 σ (modPt φ e θ z) (a, b) := by
  set w := latPt (modPt φ e θ z) (a, b)
  set c : I → ℂ := fun i => (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I)
  have hc : homFac z = ∏ i, c i := rfl
  have hw : ∏ τ, w τ = ∏ i, w (e i) := (Equiv.prod_comp e w).symm
  unfold defTerm eisTerm logFac
  simp only [defCoord_eq φ e he θ hz a b]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ i, (c i * w (e i))⁻¹ ^ 2 = (homFac z)⁻¹ ^ 2 * (∏ τ, w τ)⁻¹ ^ 2 := by
    rw [hc, hw, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, mul_pow]
  have h2 : ∏ i, ((‖c i * w (e i)‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖homFac z‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖∏ τ, w τ‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [prodCpow _ _ (fun i => norm_nonneg _), hc, hw, norm_prod, norm_prod,
      ← Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _), ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    simp only [norm_mul]
  rw [h1, h2, norm_cpow_eq_exp (homFac_ne_zero hz)]
  ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_of_add_mul {θ : E} (hθ : θ ∉ maximalRealSubfield E) {a b a' b' : maximalRealSubfield E}
    (h : (a : E) + (b : E) * θ = (a' : E) + (b' : E) * θ) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    refine ⟨Subtype.ext ?_, rfl⟩
    simpa using h
  · exfalso
    apply hθ
    have hb' : ((b : E) - (b' : E)) ≠ 0 := by
      intro h0; apply hb; exact Subtype.ext (sub_eq_zero.1 h0)
    have : θ = ((a' : E) - (a : E)) / ((b : E) - (b' : E)) := by
      field_simp
      linear_combination h
    rw [this]
    exact div_mem (sub_mem a'.2 a.2) (sub_mem b.2 b'.2)

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem algebraMap_unit (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl

noncomputable def classMap (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ)
    (c : Quotient (latRel 𝔞 𝔟)) : modUnits L :=
  ⟨Quotient.mk _ ((c.out.1.1 : E) + (c.out.1.2 : E) * θ),
    (c.out.1.1 : E) + (c.out.1.2 : E) * θ, (hL _).2 ⟨_, c.out.2.1, _, c.out.2.2.1, rfl⟩, fun h0 => c.out.2.2.2 (by
      have h := eq_of_add_mul hθ (a := c.out.1.1) (b := c.out.1.2) (a' := 0) (b' := 0) (by simpa using h0)
      exact Prod.ext h.1 h.2), rfl⟩

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by
  constructor
  · intro c c' h
    have h1 := Quotient.exact (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := h1
    rw [algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul] at hu
    obtain ⟨ha, hb⟩ := eq_of_add_mul hθ hu
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨u, ha, hb⟩
  · rintro ⟨q, x, hxL, hx0, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (hL x).1 hxL
    have hp : ((a, b) : maximalRealSubfield E × maximalRealSubfield E) ≠ 0 := by
      intro h0
      apply hx0
      have h1 : a = 0 := congrArg Prod.fst h0
      have h2 : b = 0 := congrArg Prod.snd h0
      simp [h1, h2]
    let p : LatPair 𝔞 𝔟 := ⟨(a, b), ha, hb, hp⟩
    refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
    obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
    show Quotient.mk _ _ = Quotient.mk _ _
    refine Quotient.sound ⟨ε, ?_⟩
    rw [algebraMap_unit]
    have e1 : a = p.1.1 := rfl
    have e2 : b = p.1.2 := rfl
    rw [e1, e2, h1, h2, Subfield.coe_mul, Subfield.coe_mul]
    ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

theorem hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _

end GlobalTheory.WeightTwoCompare
