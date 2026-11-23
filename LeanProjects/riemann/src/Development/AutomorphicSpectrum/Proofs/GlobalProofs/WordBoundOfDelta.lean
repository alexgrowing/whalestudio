import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutatorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBoundStatement

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

theorem dRep_real_smul {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) :
    dRep π (r • X) v = (r : ℂ) • dRep π X v := by
  have hrX : r • X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 r X hX
  have h1 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hX).1
  have h2 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hrX).1
  have h3 : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h4 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v) (r • dRep π X v) 0 := by
    have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by
      simpa using h1
    exact HasDerivAt.scomp (0 : ℝ) h1' h3
  have h5 : (fun t : ℝ => π (NormedSpace.exp (t • (r • X))) v) = fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v := by
    funext t
    rw [smul_smul, mul_comm]
  rw [h5] at h2
  rw [h2.unique h4]
  exact (Complex.coe_smul r _).symm

theorem dRep_sum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (r : Fin d → ℝ) {w : H} (hw : IsSmoothVec G π w) :
    dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w := by
  have hl := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  have key : ∀ s : Finset (Fin d), (∑ i ∈ s, r i • b i ∈ HCSS.lieOf G) ∧
      dRep π (∑ i ∈ s, r i • b i) w = ∑ i ∈ s, (r i : ℂ) • dRep π (b i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · intro t
        simpa using hG.one_mem
      · simp [dRep]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hri := hl.2.1 (r i) _ (hb i)
      refine ⟨hl.1 _ _ hri ih.1, ?_⟩
      rw [(GlobalTheory.T.derived_action_additive hG hrep hw hw hri ih.1).1, ih.2, dRep_real_smul hG hrep hw (hb i)]
  exact (key Finset.univ).2

theorem word_bound_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v := by
  intro n G H _ _ _ π hG hrep _ hQ d b hb hli hsp Y _ hYs hYd v hv
  obtain ⟨Q, m, Mb, a, hm, hMb, ha, hadd, hsmul, hconj, hpos, hbd, hgrow⟩ := hQ
  obtain ⟨hsadd, hssmul, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  have hvs := hYs v hv
  let S : Submodule ℂ H :=
    { carrier := {x | IsSmoothVec G π x}
      add_mem' := fun {x y} hx hy => hsadd x y hx hy
      zero_mem' := by simpa using hssmul 0 v hvs
      smul_mem' := fun c x hx => hssmul c x hx }
  let Xf : Fin d → Module.End ℂ S := fun i =>
    { toFun := fun x => ⟨dRep π (b i) x, (GlobalTheory.T.derived_action_of_smooth_vector hG hrep x.2 (hb i)).2⟩
      map_add' := fun x y => Subtype.ext (GlobalTheory.T.derived_action_additive hG hrep x.2 y.2 (hb i) (hb i)).2.1
      map_smul' := fun c x => Subtype.ext ((GlobalTheory.T.derived_action_additive hG hrep x.2 x.2 (hb i) (hb i)).2.2 c) }
  have hXc : ∀ i (x : S), ((Xf i x : S) : H) = dRep π (b i) x := fun _ _ => rfl
  have hlie := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  choose r hr using fun (p : Fin d × Fin d) => hsp _ (hlie.2.2.1 (b p.1) (b p.2) (hb p.1) (hb p.2))
  have hcomm : ∀ i j, Xf i * Xf j - Xf j * Xf i = ∑ l, ((r (i, j) l : ℝ) : ℂ) • Xf l := by
    intro i j
    ext u
    have h1 := GlobalTheory.T.derived_action_commutator hG hrep u.2 (hb i) (hb j)
    rw [show b i * b j - b j * b i = _ from hr (i, j), dRep_sum hG hrep b hb _ u.2] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, hXc]
    exact h1.symm
  have hQnn : ∀ x : H, 0 ≤ (Q x x).re := fun x =>
    le_trans (by positivity) (hpos x)
  let A : ℝ := a * ∑ i, mnorm (b i)
  have hmn : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ mnorm X := fun X =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha (Finset.sum_nonneg fun i _ => hmn _)
  have hs : ∀ i (x : S), |2 * (Q (Xf i x) x).re| ≤ A * (Q x x).re := by
    intro i x
    refine (GlobalTheory.T.smooth_vector_hermitian_form_growth hG hrep Q Mb a hadd hsmul hconj hbd hgrow (hb i) x.2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hQnn x)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => mnorm (b i)) (fun i _ => hmn _) (Finset.mem_univ i)) ha
  let V : Submodule ℂ S := Y.comap S.subtype
  have hinj : Function.Injective (fun u : V => (⟨(u : S), u.2⟩ : Y)) := by
    intro u w h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) h))
  let f : V →ₗ[ℂ] Y :=
    { toFun := fun u => ⟨(u : S), u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_injective f hinj
  have hV : ∀ u ∈ V, (∑ i, Xf i * Xf i) u ∈ V := by
    intro u hu
    have h1 := hYd (u : H) hu
    change (((∑ i, Xf i * Xf i) u : S) : H) ∈ Y
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, hXc] using h1
  obtain ⟨C, hC, hN⟩ := GlobalTheory.T.hermitian_form_lie_word_growth (fun x y : S => Q x y)
    (fun x y z => hadd x y z) (fun c x y => hsmul c x y) (fun x y => hconj x y)
    (fun x hx => lt_of_lt_of_le (by
      have : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
      positivity) (hpos x))
    Xf (fun i j l => ((r (i, j) l : ℝ) : ℂ)) hcomm A hA hs V hV
  have hword : ∀ (l : List (Fin d)) (u : S),
      (((l.map Xf).prod u : S) : H) = l.foldr (fun i w => dRep π (b i) w) (u : H) := by
    intro l u
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hXc, List.foldr_cons, ih]
  let vS : S := ⟨v, hvs⟩
  have hvV : vS ∈ V := hv
  let K : ℝ := Real.sqrt (Q v v).re / Real.sqrt m
  have hK : 0 ≤ K := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine GlobalTheory.T.lie_basis_coordinate_growth_bound hG hrep b hb hsp _ (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.1 (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.2
    (fun r w hw => dRep_sum hG hrep b hb r hw) hvs (C * (K + 1)) (by positivity) ?_
  intro l
  have h1 := hN l vS hvV
  rw [show ((l.map Xf).prod vS : S) = ((l.map Xf).prod vS : S) from rfl] at h1
  set w : S := (l.map Xf).prod vS with hw
  have hwv : (w : H) = l.foldr (fun i w => dRep π (b i) w) v := hword l vS
  rw [← hwv]
  have h2 : Real.sqrt m * ‖(w : H)‖ ≤ Real.sqrt (Q w w).re := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact hpos w
  have h3 : ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * K := by
    have h4 : Real.sqrt m * ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re := h2.trans h1
    have h5 : C ^ (l.length + 1) * l.length.factorial * K = (C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re) / Real.sqrt m := by
      simp only [K]; ring
    rw [h5, le_div_iff₀ hsm]
    linarith
  refine h3.trans ?_
  have h6 : K ≤ (K + 1) ^ (l.length + 1) := by
    have h7 : (K + 1) ^ 1 ≤ (K + 1) ^ (l.length + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [mul_pow]
  have h8 : 0 ≤ C ^ (l.length + 1) * (l.length.factorial : ℝ) := by positivity
  calc C ^ (l.length + 1) * l.length.factorial * K ≤ C ^ (l.length + 1) * l.length.factorial * (K + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left h6 h8
    _ = C ^ (l.length + 1) * (K + 1) ^ (l.length + 1) * l.length.factorial := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

end
