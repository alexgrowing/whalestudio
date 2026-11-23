import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBoxIndicatorRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearFullRankVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContrBilinear
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel Matrix

variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

theorem toRows₁_mul_right (Y : Matrix (R ⊕ T) D k) (h : Matrix D D k) : (Y * h).toRows₁ = Y.toRows₁ * h := by
  ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem toRows₂_mul_right (Y : Matrix (R ⊕ T) D k) (h : Matrix D D k) : (Y * h).toRows₂ = Y.toRows₂ * h := by
  ext i j; simp [Matrix.toRows₂, Matrix.mul_apply]

theorem shear_mul_right (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) (h : Matrix D D k) :
    shear c (Y * h) = shear c Y * h := by
  simp [shear, toRows₁_mul_right, toRows₂_mul_right, Matrix.fromRows_mul, Matrix.add_mul, Matrix.mul_assoc]

theorem rank_shear_le (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).rank ≤ Y.rank := by
  rw [← shearGL_transpose_mul]; exact rank_mul_le_right _ _

theorem eq_of_mul_eq_of_minor (τ : R → D) (Y₁ : Matrix R D k) (hY : (Y₁.submatrix id τ).det ≠ 0)
    {C C' : Matrix T R k} (h : C * Y₁ = C' * Y₁) : C = C' := by
  have e : ∀ C : Matrix T R k, (C * Y₁).submatrix id τ = C * Y₁.submatrix id τ := fun C => by
    ext i j; simp [Matrix.mul_apply]
  have h2 : C * Y₁.submatrix id τ = C' * Y₁.submatrix id τ := by rw [← e, ← e, h]
  have hu : IsUnit (Y₁.submatrix id τ).det := isUnit_iff_ne_zero.2 hY
  calc C = C * Y₁.submatrix id τ * (Y₁.submatrix id τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = C' := by rw [h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem rank_eq_of_minor (τ : R → D) (Y₁ : Matrix R D k) (hY : (Y₁.submatrix id τ).det ≠ 0) :
    Y₁.rank = Fintype.card R := by
  refine le_antisymm (rank_le_card_height Y₁) ?_
  have := rank_submatrix_le Y₁ id τ
  rwa [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY))] at this

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_stack (C : Matrix T R k) : Continuous (fun Y₁ : Matrix R D k => stack Y₁ C) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i
  · simp only [stack, fromRows_apply_inl]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [stack, fromRows_apply_inr, Matrix.mul_apply]
    exact continuous_finset_sum _ fun r _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply r))

theorem continuous_toRows₁_fun : Continuous (fun Y : Matrix (R ⊕ T) D k => Y.toRows₁) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply (Sum.inl i))

end GlobalTheory.RankChart

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel Matrix

theorem chart_form_eq_zero : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n ρ d : ℕ) (T : Type) [Fintype T] [DecidableEq T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), n < d → ρ < n → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Bf : fullRk k n d →ₗ[ℂ] SB (Matrix (Fin ρ ⊕ T) (Fin d) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ : SB (Matrix (Fin ρ ⊕ T) (Fin d) k)), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ Ψ₂' : SB (Matrix (Fin ρ ⊕ T) (Fin d) k)),
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin ρ ⊕ T) (Fin d) k)),
        (∀ Y : Matrix (Fin ρ ⊕ T) (Fin d) k, Y.rank ≤ ρ → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
      ∀ (τ : Fin ρ → Fin d) (Ψ₁ : fullRk k n d) (f : SB (Matrix (Fin ρ ⊕ T) (Fin d) k)),
        (∀ Y : Matrix (Fin ρ ⊕ T) (Fin d) k, f.1 Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → Bf Ψ₁ f = 0 := by
  intro hKP k _ _ _ _ n ρ d T _ _ ν ϖ hnd hρn hsm hun hν Bf hlact hquasi hkill τ Ψ₀ f hsupp
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.T.rank_chart_bounded_coefficients k (Fin ρ) T (Fin d) τ f.1 f.2 hsupp
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.rank_chart_shear_invariance k (Fin ρ) T (Fin d) f.1 f.2
  obtain ⟨b, hba, hbb⟩ : ∃ b : kˣ, box T (Fin ρ) b ≤ box T (Fin ρ) a ∧ box T (Fin ρ) b ≤ box T (Fin ρ) b₀ := by
    rcases le_total (valuation k (a : k)) (valuation k (b₀ : k)) with h | h
    · exact ⟨a, le_rfl, fun C hC r q => (hC r q).trans h⟩
    · exact ⟨b₀, fun C hC r q => (hC r q).trans h, le_rfl⟩

  have key : ∀ (Ψ : fullRk k n d) (X X' : SB (Matrix (Fin ρ ⊕ T) (Fin d) k)),
      (∀ Y : Matrix (Fin ρ ⊕ T) (Fin d) k, Y.rank ≤ ρ → X.1 Y = X'.1 Y) → Bf Ψ X = Bf Ψ X' := by
    intro Ψ X X' h
    have := hkill Ψ (X - X') (fun Y hY => by simp [h Y hY])
    rwa [map_sub, sub_eq_zero] at this

  have hext := fun θ : fullRk k ρ d => GlobalTheory.T.full_rank_box_indicator_representation k ρ d T b θ.1 θ.2
  let E : fullRk k ρ d → Matrix (Fin ρ ⊕ T) (Fin d) k → ℂ := fun θ => Classical.choose (hext θ)
  have hEmem : ∀ θ, E θ ∈ SB (Matrix (Fin ρ ⊕ T) (Fin d) k) := fun θ => (Classical.choose_spec (hext θ)).1
  have hEval : ∀ θ (Y : Matrix (Fin ρ ⊕ T) (Fin d) k), Y.rank ≤ ρ → E θ Y =
      Set.indicator {Z : Matrix (Fin ρ ⊕ T) (Fin d) k | ∃ C ∈ box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁}
        (fun Z => θ.1 Z.toRows₁) Y := fun θ => (Classical.choose_spec (hext θ)).2
  let e : Matrix T (Fin ρ) k → fullRk k ρ d → SB (Matrix (Fin ρ ⊕ T) (Fin d) k) := fun C θ =>
    ⟨omB ν ν (shearGL (-C)) 1 (E θ), omB_mem_SB ν ν _ _ (hEmem θ)⟩
  have hev : ∀ C θ (Y : Matrix (Fin ρ ⊕ T) (Fin d) k), Y.rank ≤ ρ → (e C θ).1 Y =
      Set.indicator {Z : Matrix (Fin ρ ⊕ T) (Fin d) k | ∃ C ∈ box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁}
        (fun Z => θ.1 Z.toRows₁) (shear (-C) Y) := by
    intro C θ Y hY
    show omB ν ν (shearGL (-C)) 1 (E θ) Y = _
    rw [omB_shearGL]
    exact hEval θ _ ((rank_shear_le _ _).trans hY)

  have hD : ∀ (C : Matrix T (Fin ρ) k) (Ψ : fullRk k n d) (θ : fullRk k ρ d), Bf Ψ (e C θ) = 0 := by
    intro C
    let Dq : fullRk k n d →ₗ[ℂ] fullRk k ρ d →ₗ⋆[ℂ] ℂ :=
      LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Ψ θ => Bf Ψ (e C θ))
        (fun Ψ Ψ' θ => by simp [map_add])
        (fun c Ψ θ => by simp)
        (fun Ψ θ θ' => by
          rw [← map_add]
          refine key Ψ _ _ fun Y hY => ?_
          simp only [Submodule.coe_add, Pi.add_apply]
          rw [hev C _ Y hY, hev C _ Y hY, hev C _ Y hY]
          simp only [Set.indicator_apply, Submodule.coe_add, Pi.add_apply]
          split_ifs <;> simp)
        (fun c Ψ θ => by
          rw [← LinearMap.map_smulₛₗ]
          refine key Ψ _ _ fun Y hY => ?_
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [hev C _ Y hY, hev C _ Y hY]
          simp only [Set.indicator_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> simp)
    have H := GlobalTheory.T.invariant_bilinear_full_rank_vanishes hKP k n ρ d ν ϖ hnd hρn hsm hun hν Dq ?_ ?_
    · intro Ψ θ; exact H Ψ θ
    · intro g Ψ₁ Ψ₁' Ψ₂ h
      exact hlact g Ψ₁ Ψ₁' _ h
    · intro h
      obtain ⟨m, hm, hm'⟩ := hquasi h
      refine ⟨m, hm, fun Ψ₁ Ψ₁' θ θ' h1 h2 => ?_⟩
      let X' : SB (Matrix (Fin ρ ⊕ T) (Fin d) k) := ⟨fun Y => (e C θ).1 (Y * h.1), by
        have := comp_mul_mem_SB 1 h (e C θ).2
        simp only [Units.val_one, Matrix.one_mul] at this
        exact this⟩
      show (m : ℂ) * Bf Ψ₁' (e C θ') = Bf Ψ₁ (e C θ)
      rw [key Ψ₁' (e C θ') X' ?_]
      · exact hm' Ψ₁ Ψ₁' (e C θ) X' h1 rfl
      intro Y hY
      show (e C θ').1 Y = (e C θ).1 (Y * h.1)
      rw [hev C θ' Y hY, hev C θ (Y * h.1) ((rank_mul_le_left _ _).trans hY), shear_mul_right]
      have hc : ∀ C' : Matrix T (Fin ρ) k, ((shear (-C) Y).toRows₂ * h.1 = C' * ((shear (-C) Y).toRows₁ * h.1) ↔
          (shear (-C) Y).toRows₂ = C' * (shear (-C) Y).toRows₁) := fun C' => by
        rw [← Matrix.mul_assoc]
        refine ⟨fun e' => ?_, fun e' => by rw [e']⟩
        have := congrArg (· * (h⁻¹ : GL (Fin d) k).1) e'
        simpa [Matrix.mul_assoc] using this
      simp only [Set.indicator_apply, Set.mem_setOf_eq, toRows₁_mul_right, toRows₂_mul_right, hc, h2]

  haveI : Finite (box T (Fin ρ) a ⧸ (box T (Fin ρ) b).addSubgroupOf (box T (Fin ρ) a)) := finite_box a b
  letI : Fintype (box T (Fin ρ) a ⧸ (box T (Fin ρ) b).addSubgroupOf (box T (Fin ρ) a)) := Fintype.ofFinite _
  have hθmem : ∀ C : Matrix T (Fin ρ) k, (fun Y₁ : Matrix (Fin ρ) (Fin d) k => f.1 (stack Y₁ C)) ∈ fullRk k ρ d := by
    intro C
    refine ⟨GlobalTheory.LocFlat.ContrBil.comp_mem_SB f.2 (continuous_stack C) continuous_toRows₁_fun
      (fun Y₁ => toRows₁_stack Y₁ C), fun Y₁ hY₁ => ?_⟩
    by_contra hne
    apply hY₁
    have := hsupp _ hne
    rw [submatrix_inl_eq, toRows₁_stack] at this
    simpa using rank_eq_of_minor τ Y₁ this
  let θq : (box T (Fin ρ) a ⧸ (box T (Fin ρ) b).addSubgroupOf (box T (Fin ρ) a)) → fullRk k ρ d := fun q =>
    ⟨_, hθmem ((q.out : box T (Fin ρ) a) : Matrix T (Fin ρ) k)⟩
  let Φ : SB (Matrix (Fin ρ ⊕ T) (Fin d) k) := ∑ q, e ((q.out : box T (Fin ρ) a) : Matrix T (Fin ρ) k) (θq q)
  rw [key Ψ₀ f Φ ?_, map_sum]
  · exact Finset.sum_eq_zero fun q _ => hD _ _ _
  intro Y hY
  simp only [Φ, Submodule.coe_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun q _ => hev _ _ Y hY]
  by_cases hd : (Y.submatrix Sum.inl τ).det = 0
  · have hf0 : f.1 Y = 0 := by by_contra h; exact hsupp Y h hd
    rw [hf0]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    simp only [Set.indicator_apply]
    split_ifs
    · show f.1 (stack (shear _ Y).toRows₁ _) = 0
      by_contra h
      exact hsupp _ h (by rwa [submatrix_inl_eq, toRows₁_stack, toRows₁_shear, ← submatrix_inl_eq])
    · rfl
  · obtain ⟨C, hC⟩ := GlobalTheory.T.rank_chart_stack_decomposition k (Fin ρ) T (Fin d) τ Y (by simpa using hY) hd
    generalize hY₁ : Y.toRows₁ = Y₁ at hC
    subst hC
    have hd' : (Y₁.submatrix id τ).det ≠ 0 := by rwa [submatrix_inl_eq, toRows₁_stack] at hd
    have hterm : ∀ q : box T (Fin ρ) a ⧸ (box T (Fin ρ) b).addSubgroupOf (box T (Fin ρ) a),
        Set.indicator {Z : Matrix (Fin ρ ⊕ T) (Fin d) k | ∃ C ∈ box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁}
          (fun Z => (θq q).1 Z.toRows₁) (shear (-((q.out : box T (Fin ρ) a) : Matrix T (Fin ρ) k)) (stack Y₁ C)) =
        if -C + ((q.out : box T (Fin ρ) a) : Matrix T (Fin ρ) k) ∈ box T (Fin ρ) b then f.1 (stack Y₁ C) else 0 := by
      intro q
      set Cq : Matrix T (Fin ρ) k := ((q.out : box T (Fin ρ) a) : Matrix T (Fin ρ) k)
      rw [shear_stack]
      have hiff : (∃ C' ∈ box T (Fin ρ) b, (stack Y₁ (C + -Cq)).toRows₂ = C' * (stack Y₁ (C + -Cq)).toRows₁) ↔
          -C + Cq ∈ box T (Fin ρ) b := by
        simp only [stack, toRows₁_fromRows, toRows₂_fromRows]
        constructor
        · rintro ⟨C', hC', he⟩
          rw [← eq_of_mul_eq_of_minor τ Y₁ hd' he] at hC'
          have := (box T (Fin ρ) b).neg_mem hC'
          rwa [neg_add, neg_neg] at this
        · intro h
          refine ⟨C + -Cq, ?_, rfl⟩
          have := (box T (Fin ρ) b).neg_mem h
          rwa [neg_add, neg_neg] at this
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hiff]
      split_ifs with h
      · show f.1 (stack (stack Y₁ (C + -Cq)).toRows₁ Cq) = f.1 (stack Y₁ C)
        rw [toRows₁_stack]
        have := hb₀ (stack Y₁ C) (-C + Cq) (hbb h)
        rwa [shear_stack, add_neg_cancel_left] at this
      · rfl
    rw [Finset.sum_congr rfl fun q _ => hterm q, sum_ite_out _ _ hba]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h ((box T (Fin ρ) a).neg_mem (ha Y₁ C hne))

end GlobalTheory.RankChart
