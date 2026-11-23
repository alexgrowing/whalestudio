import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenBasisSameVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModelBaseTrivModels
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix ComplexConjugate

section Linear

variable {E : Type} [Field E] [NumberField E]

open Classical in

theorem char_part {g : ℕ} (ty : Fin g → E →+* ℂ) (t : Fin g → ℂ) (s : E)
    (h : ∀ α : 𝓞 E, (∑ j, ty j α * t j).im = ((Algebra.trace ℚ E (α * s) : ℚ) : ℝ)) (ρ : E →+* ℂ) :
    ∑ j, (if ty j = ρ then t j else 0) - ∑ j, (if conjEmb (ty j) = ρ then conj (t j) else 0) =
      2 * Complex.I * ρ s := by
  have li : LinearIndependent ℂ fun ρ : E →+* ℂ => (fun α : 𝓞 E => ρ α) :=
    (linearIndependent_monoidHom (𝓞 E) ℂ).comp
      (fun ρ : E →+* ℂ => (ρ.comp (algebraMap (𝓞 E) E)).toMonoidHom) fun ρ ρ' e =>
        IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => DFunLike.congr_fun e a)
  refine sub_eq_zero.1 (Fintype.linearIndependent_iff.1 li (fun ρ => ∑ j, (if ty j = ρ then t j else 0) -
    ∑ j, (if conjEmb (ty j) = ρ then conj (t j) else 0) - 2 * Complex.I * ρ s) (funext fun α => ?_) ρ)
  have h1 : ((Algebra.trace ℚ E (α * s) : ℚ) : ℂ) = ∑ ρ : E →+* ℂ, ρ α * ρ s := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (K := ℚ) (E := ℂ)]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) _ _ fun σ => (map_mul σ _ _).symm).symm
  have h2 := Complex.sub_conj (∑ j, ty j α * t j)
  rw [h, Complex.ofReal_mul, Complex.ofReal_ratCast, h1] at h2
  have h3 : ∀ (ty : Fin g → E →+* ℂ) (t : Fin g → ℂ),
      ∑ ρ : E →+* ℂ, (∑ j, if ty j = ρ then t j else 0) * ρ α = ∑ j, ty j α * t j := fun ty t => by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [mul_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
  rw [h3, h3 (fun j => conjEmb (ty j))]
  have h4 : ∑ j, conjEmb (ty j) α * conj (t j) = conj (∑ j, ty j α * t j) := by
    simp [conjEmb]
  rw [h4, h2]
  simp only [Complex.ofReal_ofNat, Finset.mul_sum, Finset.sum_mul]
  exact sub_eq_zero.2 (Finset.sum_congr rfl fun _ _ => by ring)

omit [NumberField E] in

theorem eq_zero_of_span {r : ℕ} (τ : E →+* ℂ) (Λ : Set (Fin r → E)) (hΛ : Submodule.span E Λ = ⊤)
    (f : (Fin r → ℂ) → ℂ) (ha : ∀ u v, f (u + v) = f u + f v) (hs : ∀ (s : ℂ) u, f (s • u) = conj s * f u)
    (h : ∀ v ∈ Λ, f (fun n => τ (v n)) = 0) (u : Fin r → ℂ) : f u = 0 := by
  have h0 : f 0 = 0 := by simpa using hs 0 0
  have h1 : ∀ v : Fin r → E, f (fun n => τ (v n)) = 0 := fun v => by
    have hv : v ∈ Submodule.span E Λ := hΛ ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv => exact h v hv
    | zero => simp only [Pi.zero_apply, map_zero]; exact h0
    | add v w _ _ hv hw =>
      have := ha (fun n => τ (v n)) (fun n => τ (w n))
      rw [hv, hw, add_zero] at this
      simp only [Pi.add_apply, map_add]; exact this
    | smul a v _ hv =>
      have := hs (τ a) (fun n => τ (v n))
      rw [hv, mul_zero] at this
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact this
  let K : Submodule ℂ (Fin r → ℂ) :=
    { carrier := {u | f u = 0}
      add_mem' := fun {u v} hu hv => by simp only [Set.mem_setOf_eq] at *; rw [ha, hu, hv, add_zero]
      zero_mem' := h0
      smul_mem' := fun s u hu => by simp only [Set.mem_setOf_eq] at *; rw [hs, hu, mul_zero] }
  have : u ∈ K := by
    rw [pi_eq_sum_univ' u]
    refine K.sum_mem fun n _ => K.smul_mem _ ?_
    have := h1 (Pi.single n 1)
    show f _ = 0
    convert this using 2
    funext m
    by_cases e : m = n <;> simp [e, Pi.single_apply]
  exact this

theorem det_sum_elim {p q r : ℕ} (ε : Fin q ⊕ Fin p ≃ Fin r) (Γ : Matrix (Fin r) (Fin r) ℂ)
    (hΓ : (Γ.submatrix (ε ∘ Sum.inl) (ε ∘ Sum.inl)).det ≠ 0) (y : Fin q ⊕ Fin p → Fin r → ℂ)
    (A : Fin q ⊕ Fin p → Fin q → ℂ) (κ : ℂ)
    (h : ∀ k j, ∑ b, Γ (ε (.inl b)) (ε (.inl j)) * A k b = κ * ∑ m, y k m * Γ m (ε (.inl j))) :
    (Matrix.of fun k => Sum.elim (A k) fun b => y k (ε (.inr b))).det =
      κ ^ q * (Matrix.of fun k m => y k (ε m)).det := by
  have key : (Matrix.of fun k => Sum.elim (A k) fun b => y k (ε (.inr b))) *
      Matrix.fromBlocks (Γ.submatrix (ε ∘ Sum.inl) (ε ∘ Sum.inl)) 0 0 1 =
      (Matrix.of fun k m => y k (ε m)) * Matrix.fromBlocks (κ • Γ.submatrix (ε ∘ Sum.inl) (ε ∘ Sum.inl)) 0
        (κ • Γ.submatrix (ε ∘ Sum.inr) (ε ∘ Sum.inl)) 1 := by
    ext k (j | j)
    · have := h k j
      rw [← ε.sum_comp, Fintype.sum_sum_type] at this
      simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply, Function.comp_apply,
        Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, Matrix.smul_apply, smul_eq_mul]
      simp only [mul_comm (A k _), this, mul_add, Finset.mul_sum, mul_left_comm κ]
    · simp [Matrix.mul_apply, Matrix.one_apply]
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_one, Fintype.card_fin] at this
  refine mul_right_cancel₀ hΓ ?_
  linear_combination this

variable [IsCMField E]

open Classical in

theorem flatCoord_eq {p q r g : ℕ} (ε : Fin q ⊕ Fin p ≃ Fin r) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (X : Matrix (Fin r) (Fin r) ℂ) (hX : X.det ≠ 0)
    (hΓ : ((gram τ G X).submatrix (ε ∘ Sum.inl) (ε ∘ Sum.inl)).det ≠ 0)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (φ : La →ₗ[𝓞 E] (Fin r → E))
    (hφ : Submodule.span E (Set.range φ) = ⊤) (ty : Fin g → E →+* ℂ) (P : La →+ (Fin g → ℂ))
    (hP : ∀ (α : 𝓞 E) a j, P (α • a) j = ty j α * P a j) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ a b, (hermForm Hm (P a) (P b)).im = ((Algebra.trace ℚ E (ξ * herm G (φ a) (φ b)) : ℚ) : ℝ))
    (jw : Fin q → Fin g) (jv : Fin p → Fin g)
    (hw : ∀ F : Fin g → ℂ, ∑ j, (if ty j = conjEmb τ then F j else 0) = ∑ b, F (jw b))
    (hv : ∀ F : Fin g → ℂ, ∑ j, (if ty j = τ then F j else 0) = ∑ b, F (jv b))
    (hPw : ∀ a b, P a (jw b) = hermC τ G (col X (ε (.inl b))) (Data.emb τ (φ a)))
    (hPv : ∀ a b, P a (jv b) = (X⁻¹ *ᵥ Data.emb τ (φ a)) (ε (.inr b))) (x : Fin q ⊕ Fin p → La) :
    GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.flatCoord Hm (fun k => P (x k)) (fun b => Pi.single (jw b) 1) (fun k b => P (x k) (jv b)) =
      (-(Real.pi : ℂ) * (2 * Complex.I * conj (τ ξ))) ^ q *
        (Matrix.of fun k m => τ (φ (x k) (ε m))).det * X.det⁻¹ := by
  have hXu : IsUnit X.det := hX.isUnit
  have hcol : ∀ a, col X a = X *ᵥ Pi.single a 1 := fun a => by
    ext k; simp [col]
  have hinv : ∀ u : Fin r → ℂ, X *ᵥ (X⁻¹ *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hXu, Matrix.one_mulVec]
  have hcj : ∀ ρ : E →+* ℂ, conjEmb ρ = conjEmb τ ↔ ρ = τ := fun ρ =>
    ⟨fun e => RingHom.ext fun a => (starRingEnd ℂ).injective (DFunLike.congr_fun e a), fun e => e ▸ rfl⟩
  have main : ∀ (b₀ : La) (u : Fin r → ℂ),
      ∑ b, hermC τ G (col X (ε (.inl b))) u * (Hm *ᵥ star (P b₀)) (jw b) -
        ∑ b, conj ((X⁻¹ *ᵥ u) (ε (.inr b)) * (Hm *ᵥ star (P b₀)) (jv b)) -
        2 * Complex.I * conj (τ ξ) * hermC τ G (Data.emb τ (φ b₀)) u = 0 := fun b₀ u => by
    refine eq_zero_of_span τ _ hφ (fun u => ∑ b, hermC τ G (col X (ε (.inl b))) u * (Hm *ᵥ star (P b₀)) (jw b) -
        ∑ b, conj ((X⁻¹ *ᵥ u) (ε (.inr b)) * (Hm *ᵥ star (P b₀)) (jv b)) -
        2 * Complex.I * conj (τ ξ) * hermC τ G (Data.emb τ (φ b₀)) u) (fun u v => ?_) (fun s u => ?_) ?_ u
    · simp only [UnitFrame.hermC_eq, star_add, Matrix.mulVec_add, dotProduct_add, add_mul, Pi.add_apply, map_add,
        Finset.sum_add_distrib]
      ring
    · simp only [UnitFrame.hermC_eq, star_smul, Matrix.mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
        mul_assoc, map_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
    · rintro _ ⟨a, rfl⟩
      have h1 := char_part ty (fun j => P a j * (Hm *ᵥ star (P b₀)) j) (ξ * herm G (φ a) (φ b₀)) (fun α => by
        have := hH (α • a) b₀
        rw [hermForm, dotProduct] at this
        have e : ξ * herm G (φ (α • a)) (φ b₀) = α * (ξ * herm G (φ a) (φ b₀)) := by
          rw [map_smul]
          simp only [herm, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
            rw [RingOfIntegers.coe_eq_algebraMap]; ring
        rw [e] at this
        simpa only [hP, mul_assoc] using this) (conjEmb τ)
      simp only [hcj] at h1
      rw [hw, hv] at h1
      simp only [hPw, hPv] at h1
      have h2 : conjEmb τ (herm G (φ a) (φ b₀)) = hermC τ G (Data.emb τ (φ b₀)) (Data.emb τ (φ a)) := by
        have h3 : ∀ a b, conj (τ (G a b)) = τ (G b a) := fun a b => by
          rw [← hG a b, cc, IsCMField.complexEmbedding_complexConj]
        simp only [conjEmb, RingHom.comp_apply, herm, hermC, Data.emb, cc, map_sum, map_mul, h3,
          IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [map_mul, h2] at h1
      exact sub_eq_zero.2 (h1.trans (mul_assoc _ _ _).symm)
  have hd := det_sum_elim ε (gram τ G X) hΓ (fun k => X⁻¹ *ᵥ Data.emb τ (φ (x k)))
    (fun k b => -(Real.pi : ℂ) * hermForm Hm (Pi.single (jw b) 1) (P (x k)))
    (-(Real.pi : ℂ) * (2 * Complex.I * conj (τ ξ))) fun k j => by
      have h1 := main (x k) (col X (ε (.inl j)))
      have h2 : ∀ b, (X⁻¹ *ᵥ col X (ε (.inl j))) (ε (.inr b)) = 0 := fun b => by
        rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hXu, Matrix.one_mulVec]
        simp
      have h3 : hermC τ G (Data.emb τ (φ (x k))) (col X (ε (.inl j))) =
          ∑ m, (X⁻¹ *ᵥ Data.emb τ (φ (x k))) m * gram τ G X m (ε (.inl j)) := by
        conv_lhs => rw [← hinv (Data.emb τ (φ (x k))), hcol, UnitFrame.hermC_mulVec]
        simp [dotProduct]
      simp only [h2, zero_mul, map_zero, Finset.sum_const_zero, sub_zero, h3] at h1
      simp only [hermForm, single_dotProduct, one_mul, mul_left_comm _ (-(Real.pi : ℂ)), ← Finset.mul_sum]
      rw [mul_assoc, ← sub_eq_zero.1 h1]
      rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.flatCoord, hPv]
  rw [hd, mul_assoc (_ ^ q), ← Ring.inverse_eq_inv', ← Matrix.det_nonsing_inv, ← Matrix.det_transpose X⁻¹, ← Matrix.det_submatrix_equiv_self ε X⁻¹ᵀ,
    ← Matrix.det_mul]
  congr 2
  ext k m
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    Matrix.transpose_apply, Data.emb]
  rw [← ε.sum_comp]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Linear

open AlgebraicGeometry CategoryTheory Limits IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt
  GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

open Classical in

theorem sum_letters (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) {n : ℕ}
    (hn : n = Dw.mult τ) (F : Fin g → ℂ) :
    ∑ j, (if relab c σ (e j).1 = relab c σ τ then F j else 0) = ∑ b : Fin n, F (e.symm ⟨τ, Fin.cast hn b⟩) := by
  subst hn
  rw [← e.symm.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single τ]
  · simp
  · intro ρ _ hρ
    simp [(relab_injective σ).eq_iff, hρ]
  · simp

theorem rdU_eq_mul_horizGen {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H)
    {Y : Model Xo c (RingHom.id c.F)} {V : (Xo.XF c).Opens} {sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1} {f : Rul Xo c}
    (hn : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig) (hh : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig) (hr : Reads Y V τ sig f)
    (k : U.Comp) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) :
    ∃ a : ℂ, ∀ y : (U.X k).dom, (∀ s, ptF (U.un k y) s ∈ (V : Set (Xo.XF c))) →
      rdU U f k y ≠ 0 ∧ rdU U f k y = a * horizGen ⟨_, hτ⟩ y.1 := by
  classical
  obtain ⟨hrk, hsh, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := hU
  obtain ⟨hp0, hΨ⟩ := hsh k
  obtain ⟨x₀, hx₀⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := (F.Di (ik k)).La) (n := Dw.q + Dw.p)
    (by rw [(F.Di (ik k)).rank, (F.sig _).1, (F.sig _).2, add_comm])
  obtain ⟨κ, -, hκ⟩ := hh σ hσ g _ (PeriodRowsCompare.isTypeFn_letters c σ hσ e) F (ik k)
    (x₀ ∘ finSumFinEquiv) (hx₀.comp _ finSumFinEquiv.injective)
  have hp : Dw.p = Dw.mult τ.1 := (if_pos τ.2).symm
  have hq : Dw.q = Dw.mult (conjEmb τ.1) := (if_neg (conj_not_mem τ)).symm
  let ε : Fin Dw.q ⊕ Fin Dw.p ≃ Fin r :=
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv).trans (finCongr (by omega))
  have hε₁ : ∀ b, (ε (.inl b) : ℕ) = Dw.q - 1 - b := fun b => by simp [ε]; omega
  have hε₂ : ∀ b, (ε (.inr b) : ℕ) = Dw.q + b := fun b => by simp [ε]
  let ψ : (F.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype.comp (φ k).toLinearMap
  have hψ : Submodule.span E (Set.range ψ) = ⊤ := by
    rw [← (U.X k).Λ_span]
    congr 1
    ext v
    exact ⟨fun ⟨a, ha⟩ => ha ▸ (φ k a).2, fun hv => ⟨(φ k).symm ⟨v, hv⟩, by simp [ψ]⟩⟩
  refine ⟨κ * ((-(Real.pi : ℂ) * (2 * Complex.I * conj (relab c σ τ.1 (-(U.X k).ξ0)))) ^ Dw.q *
    (Matrix.of fun i m => relab c σ τ.1 (ψ ((x₀ ∘ finSumFinEquiv) i) (ε m))).det), fun y hy => ?_⟩
  obtain ⟨P, hP, hPer, hx, hder, -⟩ := hper k y
  obtain ⟨a, ha⟩ := exists_matches Y V τ (U.un k y) hy
  have hval : rdU U f k y = sig (CAt σ) (algebraMap c.F (CAt σ)) a := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, y.2, dif_pos]
    haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    exact hr (CAt σ) _ (FlagTan.fromTest_of_isLocalRing (S := CAt σ) _) a ha
  refine ⟨hval ▸ (show IsUnit (M := ℂ) _ from hn _ _ a).ne_zero, ?_⟩
  obtain ⟨Hm, hH, -, hHE⟩ := hPer.2.2.2.2
  have hdir : ∀ (ρ : E →+* ℂ) (j : Fin (Dw.mult ρ)) v, SameVec (S := CAt σ) Y (U.un k y) ((U.un k y).u ρ j) v →
      GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsDirection Y (ptF (S := CAt σ) (U.un k y)) (fun z => (F.ex (ik k) P z).left)
        (Pi.single (e.symm ⟨ρ, j⟩) 1) v := by
    rintro ρ j v ⟨w, hw, h1, h2⟩
    exact ⟨Over.homMk w hw.1, h2, (congrArg _ h1).mpr (hder ρ j)⟩
  have h1 := hκ P Hm hPer hH hHE (ptF (S := CAt σ) (U.un k y)) a ((pullback.lift_fst _ _ _).trans hx) ha.1
    (fun b => Pi.single (e.symm ⟨τ.1, Fin.cast hp b⟩) 1) (fun b => Pi.single (e.symm ⟨conjEmb τ.1, Fin.cast hq b⟩) 1)
    (fun i b => P ((x₀ ∘ finSumFinEquiv) i) (e.symm ⟨τ.1, Fin.cast hp b⟩))
    (fun b => by
      obtain ⟨j, hj, hs⟩ := ha.2.1 b
      obtain rfl : j = Fin.cast hp b := Fin.ext hj
      exact hdir _ _ _ hs)
    (fun b => by
      obtain ⟨j, hj, hs⟩ := ha.2.2 b
      obtain rfl : j = Fin.cast hq b := Fin.ext hj
      exact hdir _ _ _ hs)
    (fun i n => by
      have := sum_letters σ e τ.1 hp fun j => P ((x₀ ∘ finSumFinEquiv) i) j * (Pi.single j 1 : Fin g → ℂ) n
      rw [← this, Finset.sum_eq_single n (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [Pi.single_eq_same, mul_one]
      rfl)
  have hnot : conjEmb (relab c σ τ.1) ∉ (U.X k).Ψ := ((U.X k).cmType _).1 hτ
  have hcc : conjEmb (conjEmb (relab c σ τ.1)) = relab c σ τ.1 := RingHom.ext fun a => by simp [conjEmb]
  have h2 := flatCoord_eq ε (relab c σ τ.1) (U.X k).Gm (U.X k).Gm_herm (-(U.X k).ξ0) (mat y.1 ⟨_, hτ⟩)
    (y.2 ⟨_, hτ⟩).1
    (by
      have h3 := (y.2 ⟨_, hτ⟩).2 ⟨Dw.q, by omega⟩
      intro h0
      have h4 : dmin (U.X k).Gm y.1 ⟨_, hτ⟩ ⟨Dw.q, by omega⟩ = 0 := by
        rw [← h0, dmin, lminor, ← Matrix.det_submatrix_equiv_self (Fin.revPerm : Fin Dw.q ≃ Fin Dw.q)]
        rfl
      rw [h4] at h3
      simp at h3)
    ψ hψ (fun j => relab c σ (e j).1) P hPer.1 Hm
    (fun a b => by rw [hHE]; exact_mod_cast congrArg (fun z : ℚ => (z : ℝ)) (hEF k a b))
    (fun b => e.symm ⟨conjEmb τ.1, Fin.cast hq b⟩) (fun b => e.symm ⟨τ.1, Fin.cast hp b⟩)
    (fun F => by rw [← relab_conj]; exact sum_letters σ e _ hq F) (sum_letters σ e _ hp)
    (fun a b => by
      rw [hP, Equiv.apply_symm_apply, relab_conj]
      have hb : (U.X k).p0 - 1 - b < r := by have := b.2; omega
      have key : ∀ (ρ : E →+* ℂ) (hρ : ρ = relab c σ τ.1) (h' : ρ ∈ (U.X k).Ψ),
          hermC ρ (U.X k).Gm (col (mat y.1 ⟨ρ, h'⟩) ⟨_, hb⟩) (Data.emb ρ (φ k a : Fin r → E)) =
          hermC (relab c σ τ.1) (U.X k).Gm (col (mat y.1 ⟨_, hτ⟩) (ε (.inl b))) (Data.emb (relab c σ τ.1) (ψ a)) := by
        rintro _ rfl _
        rw [show (⟨_, hb⟩ : Fin r) = ε (.inl b) from Fin.ext (by rw [hε₁]; simp only [hp0])]
        rfl
      unfold perFr
      rw [dif_neg hnot, dif_pos (hcc.symm ▸ hτ)]
      exact (dif_pos hb).trans (key _ hcc _))
    (fun a b => by
      rw [hP, Equiv.apply_symm_apply]
      have hb : (U.X k).p0 + b < r := by have := b.2; omega
      unfold perFr
      rw [dif_pos hτ]
      refine (dif_pos hb).trans ?_
      rw [show ε (.inr b) = (⟨_, hb⟩ : Fin r) from Fin.ext (by rw [hε₂]; simp only [hp0])]
      rfl)
    (x₀ ∘ finSumFinEquiv)
  rw [h2] at h1
  rw [hval, horizGen, mul_assoc]
  exact h1

theorem const_length_of_reads : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig → f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) → Reads Y V τ sig f → ∀ σ, GoodEmb c σ → ∃ b : ℝ, 0 < b ∧ homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn (U σ) Z = {b} := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ Y V sig f hV _ hn hh _ hr σ hσ
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hτ : relab c σ τ.1 ∈ ((U σ).X k).Ψ := by
    refine (((hL.unf σ hσ).2.1 k).2 _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0
  obtain ⟨a, ha⟩ := rdU_eq_mul_horizGen (U σ) hσ (hL.unf σ hσ) τ hn hh hr k hτ
  obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
  have hy' : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by rw [hk]; exact ⟨rfl, hy⟩
  have ha0 : a ≠ 0 := by
    obtain ⟨h1, h2⟩ := ha ⟨y, hy⟩ (hV ▸ hy'.2)
    exact left_ne_zero_of_mul (h2 ▸ h1)
  refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖),
    mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha0) (Real.sqrt_pos.2 (norm_pos_iff.2
      ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨_, hy'⟩, ?_⟩⟩
  rintro ⟨k', y'⟩ hz
  have hz' := hz
  rw [hk] at hz'
  obtain ⟨rfl, hy₁⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom := hz'
  have h1 := (ha ⟨y', hy₁⟩ (hV ▸ hz.2)).2
  rw [← pnorm_horizGen ((U σ).X k') ⟨_, hτ⟩ hy₁, homN, ptN, modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' hτ]
  simp only at h1
  simp only [Data.pnorm, h1, norm_mul, mul_assoc]

end GlobalTheory.BdryUnit
