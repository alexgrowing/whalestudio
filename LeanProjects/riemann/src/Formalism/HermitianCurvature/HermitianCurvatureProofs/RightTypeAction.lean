import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Geometry

variable {k r : ℕ}

def InLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  inLieLev k r (Fin.last r) X ∧ X *ᵥ z = 0

theorem exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z := by
  have h := Qx8.exp_lev hX.1 t
  exact ⟨h.1, fun a => h.2 a (by simp), Qx8.exp_fix hX.2 t⟩

theorem unitB_conj_mulVec {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m)
    (v : Fin n → ℂ) (h : herm H v (Bs a) = 0) : (unitB H Bs a b)ᴴ *ᵥ (H *ᵥ v) = 0 := by
  ext q
  have h' : ∑ p, star (Bs a p) * (H *ᵥ v) p = 0 := h
  show ∑ p, star (Bs a p * (star (Bs b) ⬝ᵥ H *ᵥ bvec q)) * (H *ᵥ v) p = 0
  simp_rw [star_mul']
  rw [show ∑ p, star (Bs a p) * star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * (H *ᵥ v) p
      = star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * ∑ p, star (Bs a p) * (H *ᵥ v) p from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring, h', mul_zero]

theorem frame_lie {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) :
    InLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      InLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hl := Qx8.unitB_lie Bs hB.1 (Fin.last r) a b
  have h0 : ∀ c, herm (Hpk k r) z (Bs c) = 0 := by
    intro c
    rw [← Qx2.herm_star, hB.2.2 c z (by simp), star_zero]
  have z1 : unitB (Hpk k r) Bs a b *ᵥ z = 0 := by
    rw [Qx8.unitB_mulVec, h0, zero_smul]
  have z2 : ((Hpk k r)⁻¹ * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ z = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, unitB_conj_mulVec _ _ _ _ _ (h0 a), Matrix.mulVec_zero]
  refine ⟨⟨hl.1, ?_⟩, ⟨hl.2, ?_⟩⟩
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, z1, z2]; simp
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, z1, z2]; simp

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def dOp (π : Mx k r → (W →L[ℂ] W)) (X : Mx k r) : W →L[ℂ] W :=
  deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0

def ecOp (π : Mx k r → (W →L[ℂ] W)) (Z : Mx k r) : W →L[ℂ] W :=
  dOp π (hpart1 (Hpk k r) Z) + Complex.I • dOp π (hpart2 (Hpk k r) Z)

variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem dOp_hasDeriv (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) (dOp π X) 0 := by
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hc.comp_continuous h1 (exp_uw hX)
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)))
    (by simp [NormedSpace.exp_zero, hπ.1])
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.2 _ (exp_uw hX s) _ (exp_uw hX t)]) hcont
  exact (hA 0).differentiableAt.hasDerivAt

theorem dRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) (v : W) : dRep π X v = dOp π X v := by
  have h := dOp_hasDeriv hπ hc hX
  have h2 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dOp π X v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa [Function.comp_def] using this
  unfold dRep
  exact h2.deriv

theorem ecRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z)) (v : W) :
    EcRep (Hpk k r) π Z v = ecOp π Z v := by
  unfold EcRep ecOp
  rw [dRep_eq hπ hc h1, dRep_eq hπ hc h2]
  rfl

end Rep

section Right

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_right (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hgG.1, hh.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hh.2.1 a).1, (hh.2.1 a).2]
      exact hgG.2 a ha
  · have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ 1 ⟨1, h1z, 1, h1N, by simp⟩ h ⟨h, hh, 1, h1N, by simp⟩
    simpa using hS

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg 1 h1z h hh
  rw [one_mul, mul_one, hπ'.1] at e1
  have e1' : π 1 ∘SL J g = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [one_mul] at e2
  rw [e2, ← ContinuousLinearMap.comp_assoc, e1']

theorem rd_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : RdV X F g = (J g).comp ((dOp π' X).comp B) := by
  have hfun : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_right hD hg hu), J_right hπ' hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold RdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp) (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B))
      ((J g).comp ((dOp π' X).comp B)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem rz_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((ecOp π' Z).comp B) := by
  unfold RZ
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨ContinuousLinearMap.id ℂ Wq, fun g _ => by simp, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B', hB1, hB2⟩ := ih (fun q hq => hL q (by simp [hq]))
    obtain ⟨h1, h2⟩ := hL p (by simp)
    refine ⟨p.1 • B' + (ecOp π' p.2).comp B', fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 h1 h2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      rw [hB2 v, ecRep_eq hπ' hc h1 h2]

end Right

end QrD

theorem right_type_action : Formalism.FourierDecayAlt.Q.RightTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∃ Bσ : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
            (J g).comp Bσ) ∧
      ∀ v, Bσ v = ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v :=
    fun σ => QrD.fold_right hD hπ' hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at key
  choose Bf hBf1 hBf2 using key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_zsmul, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hBf1 σ g hg, ContinuousLinearMap.comp_apply, hBf2 σ v]

end Formalism.FourierDecayAlt.P
