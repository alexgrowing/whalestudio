import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

section LineStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {R : Type} [Zero R] {n : ℕ}

theorem continuous_mat_UAtSub (X : Spc F E n) (ev : AF F → R) :
    Continuous fun g : UAtSub σ X ev => mat g.1 :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

theorem isClosed_stabAt_vec (X : Spc F E n) (ev : AF F → R) (x : Fin n → E) :
    IsClosed (stabAt σ X ev x : Set (UAtSub σ X ev)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  exact isClosed_eq ((continuous_mat_UAtSub X ev).matrix_mulVec continuous_const) continuous_const

theorem isClosed_stabAt_mul_levi (X : Spc F E n) (ev : AF F → R) (x : Fin n → E)
    (m₀ : idelesAt E ev →* UAtSub σ X ev) (hm : ∀ t, mat (m₀ t).1 *ᵥ incV F x = (t.1 : AE F E) • incV F x) :
    IsClosed {g : UAtSub σ X ev | ∃ q ∈ stabAt σ X ev x, ∃ t, g = q * m₀ t} := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  set y : Fin n → AE F E := incV F x with hy
  by_cases h0 : y = 0
  · have : {g : UAtSub σ X ev | ∃ q ∈ stabAt σ X ev x, ∃ t, g = q * m₀ t} = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ⟨g, ?_, 1, by rw [map_one, mul_one]⟩
      show mat g.1 *ᵥ incV F x = incV F x
      rw [← hy, h0, Matrix.mulVec_zero]
    rw [this]; exact isClosed_univ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
  have hxi : x i ≠ 0 := fun h => hi (by simp [hy, incV, h])
  have hyi : IsUnit (y i) := (IsUnit.mk0 (x i) hxi).map (inclR (F := F) (AF F))
  obtain ⟨u, hu⟩ := hyi
  have key : {g : UAtSub σ X ev | ∃ q ∈ stabAt σ X ev x, ∃ t, g = q * m₀ t} =
      {g : UAtSub σ X ev | ∀ j, (mat g.1 *ᵥ y) j * y i = (mat g.1 *ᵥ y) i * y j} := by
    ext g
    constructor
    · rintro ⟨q, hq, t, rfl⟩ j
      have hq' : mat q.1 *ᵥ y = y := hq
      have e : mat (q * m₀ t).1 *ᵥ y = (t.1 : AE F E) • y := by
        show mat (q.1 * (m₀ t).1) *ᵥ y = _
        rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hm t, Matrix.mulVec_smul, hq']
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · intro hg
      set s : AE F E := (mat g.1 *ᵥ y) i * (u⁻¹ : (AE F E)ˣ) with hs
      have hgy : mat g.1 *ᵥ y = s • y := by
        funext j
        have h1 := hg j
        rw [← hu] at h1
        simp only [Pi.smul_apply, smul_eq_mul, hs]
        calc (mat g.1 *ᵥ y) j = (mat g.1 *ᵥ y) j * (u : AE F E) * (u⁻¹ : (AE F E)ˣ) := by
              rw [Units.mul_inv_cancel_right]
          _ = (mat g.1 *ᵥ y) i * y j * (u⁻¹ : (AE F E)ˣ) := by rw [h1]
          _ = _ := by ring
      have hinv : mat g.1⁻¹ * mat g.1 = 1 := Units.inv_mul g.1.1
      have hback : y = s • (mat g.1⁻¹ *ᵥ y) := by
        rw [← Matrix.mulVec_smul, ← hgy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      have hsu : IsUnit s := by
        have h2 : y i = s * (mat g.1⁻¹ *ᵥ y) i := by
          conv_lhs => rw [hback]
          rfl
        rw [← hu] at h2
        exact isUnit_of_mul_isUnit_left (h2 ▸ u.isUnit)
      have hsAt : hsu.unit ∈ idelesAt E ev := by
        intro a ha
        have h3 : a • (mat g.1 - 1) = 0 := g.2 a ha
        have h4 : (a • (mat g.1 - 1)) *ᵥ y = 0 := by rw [h3, Matrix.zero_mulVec]
        rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hgy] at h4
        have h5 := congrFun h4 i
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h5
        show a • ((hsu.unit : AE F E) - 1) = 0
        rw [IsUnit.unit_spec]
        have h6 : (a • (s - 1)) * y i = 0 := by
          rw [smul_mul_assoc, sub_mul, one_mul]; exact h5
        rw [← hu] at h6
        exact (Units.mul_left_eq_zero u).mp h6
      let t : idelesAt E ev := ⟨hsu.unit, hsAt⟩
      refine ⟨g * (m₀ t)⁻¹, ?_, t, by rw [inv_mul_cancel_right]⟩
      show mat (g.1 * (m₀ t)⁻¹.1) *ᵥ y = y
      rw [← map_inv, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hm t⁻¹, Matrix.mulVec_smul, hgy, smul_smul]
      have : ((t⁻¹ : idelesAt E ev).1 : AE F E) * s = 1 := by
        exact hsu.val_inv_mul
      rw [this, one_smul]
  rw [key]
  simp only [Set.setOf_forall]
  have hc : Continuous fun g : UAtSub σ X ev => mat g.1 *ᵥ y :=
    (continuous_mat_UAtSub X ev).matrix_mulVec continuous_const
  exact isClosed_iInter fun j => isClosed_eq (((continuous_apply j).comp hc).mul continuous_const)
    (((continuous_apply i).comp hc).mul continuous_const)

end LineStab

theorem isClosed_stab_and_lineStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ m₀ : idelesAt E (evFin F v) →* UAtSub σ G.V (evFin F v), (∀ t, IsLevi H t.1 (1 : UA σ G₁.V.J) (m₀ t).1) →
      IsClosed (stabAt σ G.V (evFin F v) H.x : Set (UAtSub σ G.V (evFin F v))) ∧
      IsClosed {x : UAtSub σ G.V (evFin F v) | ∃ q ∈ stabAt σ G.V (evFin F v) H.x, ∃ t, x = q * m₀ t} := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' om₁ om₁' _ _ v m₀ hL
  exact ⟨isClosed_stabAt_vec G.V (evFin F v) H.x,
    isClosed_stabAt_mul_levi G.V (evFin F v) H.x m₀ fun t => (hL t).1⟩

end GlobalTheory.ThK.LemF.QuotInv
