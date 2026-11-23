import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeSumXMulCLe

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3.RK

def linT (n : ℕ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)
  | Sum.inl x => ∑ l, X (Sum.inr (l, x.1)) * C (X (Sum.inl (l, x.2)))
  | Sum.inr x => ∑ l, X (Sum.inl (l, x.1)) * C (X (Sum.inr (l, x.2)))

def TT (n : ℕ) : Poly n →ₐ[ℂ] MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n) := aeval (linT n)

theorem TT_deg {n : ℕ} (P : Poly n) : (TT n P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.TotalDegreeBounds.main
  | exact _root_.GlobalTheory.TotalDegreeBounds.main
  | (apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TotalDegreeBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TotalDegreeBounds.main ..)

theorem ev_conjT_mul {n : ℕ} (A M : Mat n) (P : Poly n) :
    ev (A.conjTranspose * M) P =
      eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2))) (map (ev M) (TT n P)) := by
  have h : (ev (A.conjTranspose * M) : Poly n →+* ℂ) =
      (eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2)))).comp
        ((map (ev M)).comp (TT n).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [ev, TT, MvPolynomial.algebraMap_eq]
    · rcases v with x | x
      · simp [ev, TT, linT, Matrix.mul_apply]
      · simp [ev, TT, linT, Matrix.mul_apply]
  exact congrArg (fun f : Poly n →+* ℂ => f P) h

theorem eval_map_eq {n : ℕ} (x : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) (f : Poly n →+* ℂ)
    (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)) :
    eval x (map f p) = ∑ s ∈ p.support, f (coeff s p) * eval x (monomial s 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, map_monomial, eval_monomial, one_mul]

end GlobalTheory.PsCo.Pc3.RK

namespace GlobalTheory.PsCo.Pc3

open RK

theorem rangeK : RangeK := by
  classical
  intro n ε U _ _ _ π hπ P
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hφc : Continuous fun k : KG ε => toMK k := hemb.continuous
  have hevc : ∀ Q : Poly n, Continuous fun k : KG ε => ev (toMK k) Q := by
    intro Q
    have hent : Continuous fun k : KG ε =>
        (Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2)) :
          (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
      refine continuous_pi fun i => ?_
      rcases i with x | x
      · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
      · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
    exact (MvPolynomial.continuous_eval Q).comp hent
  have horb : ∀ v : U, Continuous fun k : KG ε => π k v :=
    fun v => (hπ.continuous_apply v).comp continuous_subtype_val
  have hint : ∀ (Q : Poly n) (v : U), Integrable (fun k : KG ε => ev (toMK k) Q • π k v) (muK ε) :=
    fun Q v => ((hevc Q).smul (horb v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨M, hM⟩ := (isCompact_univ.image (hevc P)).isBounded.exists_norm_le
  have hMb : ∀ k : KG ε, ‖ev (toMK k) P‖ ≤ M := fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩
  let Bl : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, ev (toMK k) P • π k v ∂(muK ε)
      map_add' := fun v w => by
        simp only [map_add, smul_add]
        exact integral_add (hint P v) (hint P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => smul_comm _ _ _) }
  let B : U →L[ℂ] U := Bl.mkContinuous (M * ((muK ε) Set.univ).toReal) fun v => by
    change ‖∫ k, ev (toMK k) P • π k v ∂(muK ε)‖ ≤ _
    have := norm_integral_le_of_norm_le_const (μ := muK ε) (C := M * ‖v‖)
      (f := fun k : KG ε => ev (toMK k) P • π k v) (Filter.Eventually.of_forall fun k => by
        rw [norm_smul, hπ.norm_apply]
        exact mul_le_mul_of_nonneg_right (hMb k) (norm_nonneg v))
    calc _ ≤ M * ‖v‖ * ((muK ε) Set.univ).toReal := this
      _ = M * ((muK ε) Set.univ).toReal * ‖v‖ := by ring
  refine ⟨B, fun v => ⟨hint P v, rfl⟩, fun u l => ?_⟩
  set p := TT n P with hp
  let f : KG ε → ℂ := fun k => ⟪l, π k u⟫_ℂ
  have hfc : Continuous f := continuous_const.inner (horb u)
  let c : _ → ℂ := fun s => ∫ k, ev (toMK k) (coeff s p) * f k ∂(muK ε)
  refine ⟨∑ s ∈ p.support, C (c s) * monomial s 1, ?_, fun k₀ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    rw [C_mul_monomial, mul_one]
    exact (totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans (TT_deg P))
  · have hginv : toMK k₀⁻¹ = star (toMK k₀) := by
      have h1 : toMK k₀ * star (toMK k₀) = 1 := Unitary.mul_star_self_of_mem k₀.2.1
      calc toMK k₀⁻¹ = toMK k₀⁻¹ * (toMK k₀ * star (toMK k₀)) := by rw [h1, Matrix.mul_one]
        _ = star (toMK k₀) := by
          rw [← Matrix.mul_assoc]
          change toMK (k₀⁻¹ * k₀) * _ = _
          rw [inv_mul_cancel]
          exact Matrix.one_mul _
    have e1 : π k₀ (B u) = ∫ k, ev (toMK (k₀⁻¹ * k)) P • π k u ∂(muK ε) := by
      change π k₀ (∫ k, ev (toMK k) P • π k u ∂(muK ε)) = _
      rw [← (π k₀).integral_comp_comm (hint P u)]
      have e2 : ∫ k, π k₀ (ev (toMK k) P • π k u) ∂(muK ε) =
          ∫ k, (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) (k₀ * k) ∂(muK ε) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [map_smul, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
      rw [e2, integral_mul_left_eq_self (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) k₀]
    have hexp : ∀ k : KG ε, ev (toMK (k₀⁻¹ * k)) P =
        ∑ s ∈ p.support, ev (toMK k) (coeff s p) * ev (toMK k₀) (monomial s 1) := by
      intro k
      change ev (toMK k₀⁻¹ * toMK k) P = _
      rw [hginv, show star (toMK k₀) = (toMK k₀).conjTranspose from rfl, ev_conjT_mul, eval_map_eq]
      rfl
    have hint2 : ∀ s, Integrable (fun k : KG ε => ev (toMK k) (coeff s p) * f k) (muK ε) :=
      fun s => hintC _ ((hevc _).mul hfc)
    have hint3 : Integrable (fun k : KG ε => ev (toMK (k₀⁻¹ * k)) P • π k u) (muK ε) :=
      (((hevc P).comp (continuous_const.mul continuous_id)).smul (horb u)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc ⟪l, π k₀ (B u)⟫_ℂ = ∫ k, ⟪l, ev (toMK (k₀⁻¹ * k)) P • π k u⟫_ℂ ∂(muK ε) := by
          rw [e1, integral_inner hint3]
      _ = ∫ k, ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * (ev (toMK k) (coeff s p) * f k) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [inner_smul_right, hexp k, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * c s := by
          rw [integral_finsetSum _ fun s _ => (hint2 s).const_mul _]
          exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
      _ = ev (toMK k₀) (∑ s ∈ p.support, C (c s) * monomial s 1) := by
          simp only [map_sum, map_mul, ev, eval_C]
          exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory.PsCo.Pc3
