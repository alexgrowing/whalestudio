import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.ThetaTranslSpan

theorem mem_of_eigen {V : Type} [AddCommGroup V] (Λ Λ₁ : AddSubgroup V) (hle : Λ₁ ≤ Λ)
    [Finite (Λ ⧸ Λ₁.addSubgroupOf Λ)] (j : V → V → ℂ) (hj0 : ∀ a ∈ Λ, ∀ z, j a z ≠ 0)
    (hj : ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ z, j (a + b) z = j a (z + b) * j b z)
    (D S : Submodule ℂ (V → ℂ)) (F : V → ℂ)
    (hD : ∀ a ∈ Λ, (fun z => (j a z)⁻¹ * F (z + a)) ∈ D)
    (hF : ∀ a ∈ Λ₁, ∀ z, F (z + a) = j a z * F z)
    (hS : ∀ ψ : AddChar Λ ℂ, (∀ a, ‖ψ a‖ = 1) → (∀ a : Λ, (a : V) ∈ Λ₁ → ψ a = 1) → ∀ G ∈ D,
      (∀ (a : Λ) z, G (z + a) = ψ a * j a z * G z) → G ∈ S) : F ∈ S := by
  classical
  set Q := Λ ⧸ Λ₁.addSubgroupOf Λ
  haveI : Fintype Q := Fintype.ofFinite Q
  let T₀ : Λ → V → ℂ := fun a z => (j a z)⁻¹ * F (z + a)
  have hT₀ : ∀ a b : Λ, (QuotientAddGroup.leftRel (Λ₁.addSubgroupOf Λ)) a b → T₀ a = T₀ b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hab
    obtain ⟨c, rfl⟩ : ∃ c : Λ, b = c + a := ⟨-a + b, by abel⟩
    have hc : (c : V) ∈ Λ₁ := by simpa using hab
    ext z
    simp only [T₀, AddSubgroup.coe_add]
    rw [hj c c.2 a a.2, show z + (c + a) = (z + a) + c by abel, hF c hc]
    have := hj0 c c.2 (z + a)
    have := hj0 a a.2 z
    field_simp
  let T : Q → V → ℂ := Quotient.lift T₀ hT₀
  have hTD : ∀ q, T q ∈ D := fun q => QuotientAddGroup.induction_on q fun a => hD a a.2
  have hT : ∀ (q : Q) (a : Λ) z, T q (z + a) = j a z * T (q + (a : Q)) z := by
    intro q a z
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      change T₀ b (z + a) = j a z * T₀ (b + a) z
      simp only [T₀, AddSubgroup.coe_add]
      rw [hj b b.2 a a.2, show z + (b + a) = (z + a) + b by abel]
      have := hj0 b b.2 (z + a)
      have := hj0 a a.2 z
      field_simp
  have hT0 : T 0 = F := by
    change T₀ 0 = F
    ext z
    have h := hj 0 Λ.zero_mem 0 Λ.zero_mem z
    rw [add_zero, add_zero] at h
    have h1 : j 0 z = 1 := by
      have := hj0 0 Λ.zero_mem z
      exact (mul_eq_left₀ this).1 h.symm
    simp [T₀, h1]
  have hmem : ∀ ψ : AddChar Q ℂ, ∑ q, ψ (-q) • T q ∈ S := by
    intro ψ
    refine hS (ψ.compAddMonoidHom (QuotientAddGroup.mk' _)) (fun a => ?_) (fun a ha => ?_) _
      (D.sum_mem fun q _ => D.smul_mem _ (hTD q)) (fun a z => ?_)
    · simp [AddChar.norm_apply]
    · have : (a : Q) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ha
      change ψ (a : Q) = 1
      rw [this, AddChar.map_zero_eq_one]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (a : Q)) _ _ fun q => ?_
      have : ψ (-q) = ψ (a : Q) * ψ (-(q + (a : Q))) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; abel
      change _ = ψ (a : Q) * j a z * (ψ (-(q + (a : Q))) * T (q + (a : Q)) z)
      rw [this]
      ring
  have hsum : ∑ ψ : AddChar Q ℂ, ∑ q, ψ (-q) • T q = (Fintype.card Q : ℂ) • F := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
    rw [Finset.sum_eq_single 0 (fun q _ hq => by simp [hq]) (by simp)]
    simp [hT0]
  have h := S.sum_mem (t := Finset.univ) fun ψ _ => hmem ψ
  rw [hsum] at h
  exact (S.smul_mem_iff (by simp)).1 h

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem exists_im_eq (hH : Hm.PosDef) (f : (Fin g → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y, ∀ a, (star y ⬝ᵥ Hm.mulVec a).im = f a := by
  let B : LinearMap.BilinForm ℝ (Fin g → ℂ) := LinearMap.mk₂ ℝ
    (fun v a => (star v ⬝ᵥ Hm.mulVec a).im)
    (fun a b m => by rw [star_add, add_dotProduct, Complex.add_im])
    (fun t a m => by rw [star_smul, smul_dotProduct, Complex.smul_im, star_trivial])
    (fun m a b => by rw [mulVec_add, dotProduct_add, Complex.add_im])
    (fun t m a => by rw [mulVec_smul, dotProduct_smul, Complex.smul_im])
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => ?_
    by_contra hne
    have h1 := hH.dotProduct_mulVec_pos hne
    have h2 : (star u ⬝ᵥ Hm.mulVec (Complex.I • u)).im = 0 := LinearMap.congr_fun hu _
    rw [mulVec_smul, dotProduct_smul] at h2
    simp at h2
    have := (Complex.pos_iff.1 h1).1
    linarith
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 hinj
  obtain ⟨y, hy⟩ := hsurj f
  exact ⟨y, fun a => LinearMap.congr_fun hy a⟩

theorem span_eq_top (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) → v ∈ Λ) :
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨y, hy⟩ := exists_im_eq hH f
  have hmem : ∀ t : ℝ, t • y ∈ Λ := fun t => hΛ _ fun a ha => ⟨0, by
    rw [star_smul, smul_dotProduct, Complex.smul_im, hy,
      LinearMap.mem_ker.1 (hf (Submodule.subset_span ha))]
    simp⟩
  have hc : Continuous fun t : ℝ => (⟨t • y, hmem t⟩ : Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := ((IsLocallyConstant.iff_continuous _).2 hc).apply_eq_of_preconnectedSpace 1 0
  have hy0 : y = 0 := by simpa using h
  apply hf0
  ext a
  all_goals simp [← hy, hy0]

theorem exists_im_eq_lattice (hH : Hm.PosDef) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (φ : Λ →ₗ[ℤ] ℝ) :
    ∃ y, ∀ a : Λ, (star y ⬝ᵥ Hm.mulVec a).im = φ a := by
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f := (b.ofZLatticeBasis ℝ Λ).constr ℝ (fun i => φ (b i))
  obtain ⟨y, hy⟩ := exists_im_eq hH f
  have : (f.restrictScalars ℤ) ∘ₗ Λ.subtype = φ := b.ext fun i => by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply]
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact ⟨y, fun a => by rw [hy, ← this]; rfl⟩

theorem exists_log_addChar {A : Type} [AddCommGroup A] [Module.Free ℤ A] (ψ : AddChar A ℂ)
    (hψ : ∀ a, ‖ψ a‖ = 1) :
    ∃ φ : A →ₗ[ℤ] ℝ, ∀ a, ψ a = Complex.exp (2 * Real.pi * Complex.I * (φ a : ℝ)) := by
  let b := Module.Free.chooseBasis ℤ A
  let φ : A →ₗ[ℤ] ℝ := b.constr ℤ fun i => (ψ (b i)).arg / (2 * Real.pi)
  refine ⟨φ, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Module.Basis.constr_basis]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (ψ (b i)), hψ]
    push_cast
    rw [one_mul]; congr 1; field_simp
  | zero => simp
  | add x y _ _ hx hy =>
    rw [AddChar.map_add_eq_mul, hx, hy, map_add, ← Complex.exp_add]; congr 1; push_cast; ring
  | smul t x _ hx =>
    rw [AddChar.map_zsmul_eq_zpow, hx, map_zsmul, ← Complex.exp_int_mul]; congr 1
    simp; ring

theorem herm_swap (hH : Hm.PosDef) (z u : Fin g → ℂ) :
    star u ⬝ᵥ Hm.mulVec z = star (star z ⬝ᵥ Hm.mulVec u) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hH.isHermitian.eq, ← dotProduct_mulVec]

theorem exists_eq_smul (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ)
    (χ θ G : (Fin g → ℂ) → ℂ) (hχ : ∀ a ∈ Λ, ‖χ a‖ = 1) (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (hθt : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) (hG : Differentiable ℂ G)
    (hGt : ∀ a ∈ Λ, ∀ z, G (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * G z) : ∃ c : ℂ, G = c • θ := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ := span_eq_top hH Λ fun v => (hΛ v).1
  have htr : ∀ z u : Fin g → ℂ, z ⬝ᵥ Hmᵀ.mulVec (star u) = star u ⬝ᵥ Hm.mulVec z := fun z u => by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  have hsk : ∀ z u : Fin g → ℂ, (star u ⬝ᵥ Hm.mulVec z).im = -(star z ⬝ᵥ Hm.mulVec u).im :=
    fun z u => by rw [herm_swap hH z u]; simp
  have hint : ∀ l m : L, ∃ k : ℤ,
      (k : ℝ) = (star (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (l : Fin g → ℂ)).im := fun l m => by
    obtain ⟨k, hk⟩ := (hΛ m).2 m.2 l l.2
    exact ⟨k, hk.symm⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ L := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, mulVec_add, dotProduct_add,
        Complex.add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, mulVec_smul, dotProduct_smul]
      simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, add_dotProduct,
        Complex.add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, smul_dotProduct]
      simp))
  have hE : ∀ l m : L, (Ef l m : ℝ) =
      (star (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (l : Fin g → ℂ)).im := hk
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 fun l hl => ?_, fun φ => ?_⟩
    · by_contra hne
      have h1 := hH.dotProduct_mulVec_pos (x := (l : Fin g → ℂ)) fun h => hne (Subtype.ext h)
      have h : ∀ m, (star (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec m).im = 0 := by
        intro m
        have hm : m ∈ Submodule.span ℝ (L : Set (Fin g → ℂ)) := hsp ▸ Submodule.mem_top
        induction hm using Submodule.span_induction with
        | mem m hm => rw [hsk, ← hE l ⟨m, hm⟩, hl]; simp
        | zero => simp
        | add a b _ _ ha hb => rw [mulVec_add, dotProduct_add, Complex.add_im, ha, hb, add_zero]
        | smul t a _ ha => rw [mulVec_smul, dotProduct_smul, Complex.smul_im, ha, smul_zero]
      have h2 := h (Complex.I • (l : Fin g → ℂ))
      rw [mulVec_smul, dotProduct_smul] at h2
      simp at h2
      have := (Complex.pos_iff.1 h1).1
      linarith
    · obtain ⟨y, hy⟩ := exists_im_eq_lattice hH L hsp (-(Algebra.linearMap ℤ ℝ ∘ₗ φ))
      have hyΛ : y ∈ Λ := (hΛ y).1 fun a ha => ⟨-φ ⟨a, ha⟩, by rw [hy ⟨a, ha⟩]; simp⟩
      refine ⟨⟨y, hyΛ⟩, LinearMap.ext fun a => Int.cast_injective (α := ℝ) ?_⟩
      rw [hE, hsk, hy]; simp
  have hli : ¬ LinearIndependent ℂ ![θ, G] := fun hli => by
    have := GlobalTheory.card_le_pow_of_linearIndependent_theta_principal
      GlobalTheory.SiegelNormalForm.exists_normal_form
      (GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent
        GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
        (GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero
          GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic))
      g L hL hsp Hmᵀ (fun l => χ l) Ef hH.isHermitian.transpose
      (fun z hz => by rw [htr]; exact (Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hz)).1)
      (fun l => hχ l l.2) (fun l m => by rw [htr, hE]) hbij 1 le_rfl 2 ![θ, G]
      (fun k => by
        fin_cases k
        · exact ⟨hθ, fun l z => by rw [pow_one, htr, htr]; exact hθt l l.2 z⟩
        · exact ⟨hG, fun l z => by rw [pow_one, htr, htr]; exact hGt l l.2 z⟩) hli
    simp at this
  rw [LinearIndependent.pair_iff' h0] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, ha.symm⟩

theorem mem_span_translates : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), 0 < M → Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ a ∈ Λ₁, ∀ z, F (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * F z) → F ∈ Submodule.span ℂ {G : (Fin g → ℂ) → ℂ | ∃ y : Fin g → ℂ, (M : ℂ) • y ∈ Λ₁ ∧ G = fun z => Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec z))) * θ (z + y)} := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ hM hle hΛ₁ F hF hFt
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ := span_eq_top hH Λ fun v => (hΛ v).1
  haveI : Module.Finite ℤ Λ := (inferInstance : Module.Finite ℤ L)
  haveI : Module.Free ℤ Λ := (inferInstance : Module.Free ℤ L)
  have hMs : ∀ y a : Fin g → ℂ, (star ((M : ℂ) • y) ⬝ᵥ Hm.mulVec a).im =
      M * (star y ⬝ᵥ Hm.mulVec a).im := fun y a => by
    rw [star_smul, smul_dotProduct]; simp
  haveI : Finite (Λ ⧸ Λ₁.addSubgroupOf Λ) := by
    haveI : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨M, hM, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      refine (hΛ₁ _).1 fun b hb => ?_
      obtain ⟨k, hk⟩ := (hΛ a).2 a.2 b (hle hb)
      exact ⟨k, by rw [hMs, hk]⟩
  let j : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun a z => χ a * Complex.exp
    (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a))
  have hj0 : ∀ a ∈ Λ, ∀ z, j a z ≠ 0 := fun a ha z =>
    mul_ne_zero (fun h => by simpa [h] using hχ a ha) (Complex.exp_ne_zero _)
  have hjs : ∀ a z w, j a (z + w) = j a z * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec w)) :=
    fun a z w => by
      simp only [j, mulVec_add, dotProduct_add]
      rw [mul_assoc (χ a), ← Complex.exp_add]; congr 2; ring
  have hlin : ∀ a : Fin g → ℂ, Differentiable ℂ fun z : Fin g → ℂ => star a ⬝ᵥ Hm.mulVec z :=
    fun a => by
      simp only [dotProduct, mulVec]
      fun_prop
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  refine mem_of_eigen Λ Λ₁ hle j hj0 (fun a ha b hb z => ?_)
    { carrier := {G | Differentiable ℂ G}
      add_mem' := fun h1 h2 => h1.add h2
      zero_mem' := differentiable_const 0
      smul_mem' := fun c _ h => h.const_smul c } _ F (fun a ha => ?_) hFt
    (fun ψ hψ hψ₁ G hG hGt => ?_)
  · have h1 : j (a + b) z₀ = j a (z₀ + b) * j b z₀ := by
      refine mul_right_cancel₀ hz₀ ?_
      have e1 : θ (z₀ + (a + b)) = j (a + b) z₀ * θ z₀ := hθt _ (Λ.add_mem ha hb) _
      have e2 : θ (z₀ + b + a) = j a (z₀ + b) * θ (z₀ + b) := hθt _ ha _
      have e3 : θ (z₀ + b) = j b z₀ * θ z₀ := hθt _ hb _
      rw [← e1, mul_assoc, ← e3, ← e2]; congr 1; abel
    obtain ⟨w, rfl⟩ : ∃ w, z = z₀ + w := ⟨z - z₀, by abel⟩
    rw [show z₀ + w + b = z₀ + b + w by abel, hjs (a + b), hjs a (z₀ + b), hjs b, h1, star_add,
      add_dotProduct, mul_add, Complex.exp_add]
    ring
  · refine Differentiable.mul (Differentiable.inv ?_ (hj0 a ha)) (hF.comp (differentiable_id.add_const a))
    exact (differentiable_const _).mul (((hlin a).const_mul _).add_const _).cexp
  · have hG' : Differentiable ℂ G := hG
    obtain ⟨φ, hφ⟩ := exists_log_addChar ψ hψ
    obtain ⟨y, hy⟩ := exists_im_eq_lattice hH L hsp (-φ)
    have hy' : ∀ a : Λ, (star y ⬝ᵥ Hm.mulVec a).im = -φ a := hy
    have hyM : (M : ℂ) • y ∈ Λ₁ := (hΛ₁ _).1 fun a ha => by
      have h := hψ₁ ⟨a, hle ha⟩ ha
      rw [hφ, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have h2 : ((φ ⟨a, hle ha⟩ : ℝ) : ℂ) = n :=
        mul_left_cancel₀ Complex.two_pi_I_ne_zero (hn.trans (mul_comm _ _))
      have h3 : φ ⟨a, hle ha⟩ = n := by exact_mod_cast h2
      exact ⟨-n, by rw [hMs, hy' ⟨a, hle ha⟩, h3]; simp⟩
    obtain ⟨c, hc⟩ := exists_eq_smul hH Λ hΛ χ θ
      (fun w => Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec w)) * G (w + -y)) hχ hθ h0 hθt
      (((hlin y).const_mul _).cexp.mul (hG'.comp (differentiable_id.add_const _)))
      (fun a ha z => by
        have e := hGt ⟨a, ha⟩ (z + -y)
        have e2 : star y ⬝ᵥ Hm.mulVec a - star a ⬝ᵥ Hm.mulVec y =
            -(2 * Complex.I * (φ ⟨a, ha⟩ : ℝ)) := by
          rw [herm_swap hH y a, Complex.star_def, Complex.sub_conj, hy' ⟨a, ha⟩]; push_cast; ring
        change _ = j a z * _
        rw [show z + a + -y = z + -y + a by abel, e, hjs, hφ, mulVec_add, dotProduct_add, mul_add,
          Complex.exp_add, mulVec_neg, dotProduct_neg]
        have e3 : Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec a)) *
            Complex.exp (2 * Real.pi * Complex.I * (φ ⟨a, ha⟩ : ℝ)) *
            Complex.exp (Real.pi * -(star a ⬝ᵥ Hm.mulVec y)) = 1 := by
          rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]; congr 1
          linear_combination (Real.pi : ℂ) * e2
        linear_combination (Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec z)) * j a z *
          G (z + -y)) * e3)
    have hGe : G = (c * Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec y)))) •
        fun z => Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec z))) * θ (z + y) := by
      ext z
      have h := congrFun hc (z + y)
      simp only [Pi.smul_apply, smul_eq_mul, add_neg_cancel_right, mulVec_add, dotProduct_add,
        mul_add, Complex.exp_add] at h
      simp only [Pi.smul_apply, smul_eq_mul, Complex.exp_neg]
      have := Complex.exp_ne_zero (Real.pi * (star y ⬝ᵥ Hm.mulVec y))
      have := Complex.exp_ne_zero (Real.pi * (star y ⬝ᵥ Hm.mulVec z))
      field_simp
      linear_combination h
    rw [hGe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hyM, rfl⟩)

end GlobalTheory.ThetaTranslSpan
