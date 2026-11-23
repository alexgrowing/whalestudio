import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
