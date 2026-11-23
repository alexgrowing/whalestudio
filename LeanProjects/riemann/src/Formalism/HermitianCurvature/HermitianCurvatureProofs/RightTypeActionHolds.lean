import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RightTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_right (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg (Qx8.uw_one z) (Qx8.nlev_one _) hh (Qx8.nlev_one _)
  simpa using this

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) h hh
  rw [Matrix.one_mul, Matrix.mul_one, hπ'.1] at e1
  rw [Matrix.one_mul] at e2
  have e3 : (J g).comp (1 : Wq →L[ℂ] Wq) = J g := ContinuousLinearMap.comp_id _
  rw [e3] at e1
  rw [e2, ← ContinuousLinearMap.comp_assoc, ← e1]

theorem rd_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : QrD.InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : RdV X F g = (J g).comp ((QrD.dOp π' X).comp B) := by
  have h := QrD.dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (J g)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_right hD hg (QrD.exp_uw hX t)), J_right hπ' hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold RdV
  rw [h3]
  exact h2.deriv

theorem rz_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : QrD.InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((QrD.ecOp π' Z).comp B) := by
  unfold RZ QrD.ecOp
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp

theorem fold_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r i ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨1, fun g _ => (ContinuousLinearMap.comp_id _).symm, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B, hB1, hB2⟩ := ih fun q hq => hL q (by simp [hq])
    have hp := hL p (by simp)
    refine ⟨p.1 • B + (QrD.ecOp π' p.2).comp B, fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 hp.1 hp.2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [← hB2 v, QrD.ecRep_eq hπ' hc hp.1 hp.2]
      rfl

end RightTypeActionHermitianCurvature

theorem right_type_action_holds : RightTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  obtain ⟨B, hB1, hB2⟩ := RightTypeActionHermitianCurvature.fold_right hD hπ' hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  have e1 := hB1 g hg
  have e2 := hB2 v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1 e2
  simp only [id]
  rw [e1, ← e2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
