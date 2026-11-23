import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFamilyConjConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemisimpleRingOfPosFormAdjointClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRePosDefAdjointPeriodStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU.Retype

section Hol

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dOn_prod {J : Type} (u : Finset J) (f : J → E → ℂ) {s : Set E}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem dOn_det {n : Type} [Fintype n] [DecidableEq n] (f : E → Matrix n n ℂ) {s : Set E}
    (hf : ∀ i j, DifferentiableOn ℂ (fun b => f b i j) s) : DifferentiableOn ℂ (fun b => (f b).det) s := by
  simp only [Matrix.det_apply']
  exact DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul
    (dOn_prod Finset.univ (fun i b => f b (σ i) i) fun i _ => hf (σ i) i) _

theorem dOn_inv {n : Type} [Fintype n] [DecidableEq n] (f : E → Matrix n n ℂ) {s : Set E}
    (hf : ∀ i j, DifferentiableOn ℂ (fun b => f b i j) s) (hu : ∀ b ∈ s, (f b).det ≠ 0) (i j : n) :
    DifferentiableOn ℂ (fun b => (f b)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine DifferentiableOn.mul ((dOn_det f hf).inv hu) ?_
  refine dOn_det (fun b => (f b).updateRow j (Pi.single i 1)) fun k l => ?_
  by_cases h : k = j
  · subst h; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne h]; exact hf k l

theorem dOn_mul {l n p : Type} [Fintype n] (f : E → Matrix l n ℂ) (g : E → Matrix n p ℂ) {s : Set E}
    (hf : ∀ i j, DifferentiableOn ℂ (fun b => f b i j) s) (hg : ∀ i j, DifferentiableOn ℂ (fun b => g b i j) s)
    (i : l) (j : p) : DifferentiableOn ℂ (fun b => (f b * g b) i j) s := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hf i k).mul (hg k j)

end Hol

section Alg

variable {g r : ℕ}

theorem restr_key (V : Matrix (Fin g) (Fin r) ℂ) (R : Matrix (Fin r) (Fin g) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ))
    (hVR : V * R = 1) (hS : ∀ s ∈ S, ∃ M : Matrix (Fin g) (Fin g) ℂ, V * s = M * V) (s : S) :
    V * (s : Matrix (Fin r) (Fin r) ℂ) * R * V = V * (s : Matrix (Fin r) (Fin r) ℂ) := by
  obtain ⟨M, hM⟩ := hS s s.2
  rw [hM, Matrix.mul_assoc M V R, hVR, Matrix.mul_one]

def restr (V : Matrix (Fin g) (Fin r) ℂ) (R : Matrix (Fin r) (Fin g) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ))
    (hVR : V * R = 1) (hS : ∀ s ∈ S, ∃ M : Matrix (Fin g) (Fin g) ℂ, V * s = M * V) :
    S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ where
  toFun s := V * (s : Matrix (Fin r) (Fin r) ℂ) * R
  map_one' := by simp [hVR]
  map_mul' s t := by
    simp only [Subalgebra.coe_mul, ← Matrix.mul_assoc, restr_key V R S hVR hS s]
  map_zero' := by simp
  map_add' s t := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    show V * (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ) c) * R = algebraMap ℂ (Matrix (Fin g) (Fin g) ℂ) c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hVR]

theorem restr_mul (V : Matrix (Fin g) (Fin r) ℂ) (R : Matrix (Fin r) (Fin g) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ))
    (hVR : V * R = 1) (hS : ∀ s ∈ S, ∃ M : Matrix (Fin g) (Fin g) ℂ, V * s = M * V) (s : S) :
    restr V R S hVR hS s * V = V * (s : Matrix (Fin r) (Fin r) ℂ) :=
  restr_key V R S hVR hS s

end Alg

section Lat

variable {O : Type} [Ring O] {bar : O → O} {g r : ℕ}

def actAlg (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ) :=
  Algebra.adjoin ℂ (Set.range (actM D e ℂ))

def perM (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) (P : D.La →+ (Fin g → ℂ)) : Matrix (Fin g) (Fin r) ℂ :=
  Matrix.of fun i j => P (e j) i

theorem apply_eq_mulVec (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) (P : D.La →+ (Fin g → ℂ)) (x : D.La) :
    P x = perM D e P *ᵥ (fun j => ((e.repr x j : ℤ) : ℂ)) := by
  conv_lhs => rw [← e.sum_repr x, map_sum]
  ext i
  simp only [map_zsmul, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, perM, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem perM_mul_actM (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) (P : D.La →+ (Fin g → ℂ)) (a : O) :
    perM D e P * actM D e ℂ a = Matrix.of fun i j => P (a • e j) i := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  rw [apply_eq_mulVec D e P (a • e j)]
  simp [Matrix.mul_apply, actM, Matrix.mulVec, dotProduct]

theorem apply_smul_eq (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) (P : D.La →+ (Fin g → ℂ)) (a : O) (x : D.La) :
    P (a • x) = (perM D e P * actM D e ℂ a) *ᵥ (fun j => ((e.repr x j : ℤ) : ℂ)) := by
  rw [perM_mul_actM]
  conv_lhs => rw [← e.sum_repr x]
  rw [Finset.smul_sum]
  simp_rw [smul_comm a]
  ext i
  simp [map_sum, map_zsmul, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem perM_surj (D : PLat O bar) (e : Module.Basis (Fin r) ℤ D.La) (P : D.La →+ (Fin g → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) : Function.Surjective (perM D e P).mulVec := by
  intro w
  have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
  have hle : Submodule.span ℝ (Set.range P) ≤
      (LinearMap.range (Matrix.mulVecLin (perM D e P))).restrictScalars ℝ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (apply_eq_mulVec D e P x).symm⟩
  obtain ⟨v, hv⟩ := hle hw
  exact ⟨v, hv⟩

theorem exists_rinv (V : Matrix (Fin g) (Fin r) ℂ) (h : Function.Surjective V.mulVec) :
    ∃ R : Matrix (Fin r) (Fin g) ℂ, V * R = 1 := by
  choose v hv using fun k : Fin g => h (Pi.single k 1)
  refine ⟨Matrix.of fun l k => v k l, ?_⟩
  ext i k
  have := congrFun (hv k) i
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

end Lat

theorem retype : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → b₀ ∈ B → (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → IsPeriod D ρ (P b₀) → (∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ ∀ a : O, ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ x, P b (a • x) = M *ᵥ P b x) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ (a : O) x, h b *ᵥ P b (a • x) = ρ a *ᵥ (h b *ᵥ P b x) := by
  intro O _ bar g ρ D m B b₀ P hB hb₀ hPd hper hBP
  classical
  let e : Module.Basis (Fin (Module.finrank ℤ D.La)) ℤ D.La := Module.finBasis ℤ D.La
  let S := actAlg D e
  let V : (Fin m → ℂ) → Matrix (Fin g) (Fin (Module.finrank ℤ D.La)) ℂ := fun b => perM D e (P b)
  have hVd : ∀ i j, DifferentiableOn ℂ (fun b => V b i j) B := fun i j =>
    (differentiableOn_pi.1 (hPd (e j))) i
  have hSV : ∀ b ∈ B, ∀ s ∈ S, ∃ M : Matrix (Fin g) (Fin g) ℂ, V b * s = M * V b := by
    intro b hb s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨M, hM⟩ := (hBP b hb).2 a
      refine ⟨M, ?_⟩
      show perM D e (P b) * actM D e ℂ a = M * perM D e (P b)
      rw [perM_mul_actM]
      ext i j
      simp [perM, hM, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    | algebraMap c =>
      refine ⟨algebraMap ℂ _ c, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨M, hM⟩ := hx
      obtain ⟨N, hN⟩ := hy
      exact ⟨M + N, by rw [Matrix.mul_add, hM, hN, Matrix.add_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨M, hM⟩ := hx
      obtain ⟨N, hN⟩ := hy
      exact ⟨M * N, by rw [← Matrix.mul_assoc, hM, Matrix.mul_assoc, hN, Matrix.mul_assoc]⟩
  obtain ⟨R₀, hR₀⟩ := exists_rinv (V b₀) (perM_surj D e (P b₀) hper.2.2.2.1)
  let W : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => V b * R₀
  have hWd : ∀ i j, DifferentiableOn ℂ (fun b => W b i j) B :=
    dOn_mul V (fun _ => R₀) hVd (fun _ _ => differentiableOn_const _)
  let B' := B ∩ (fun b => (W b).det) ⁻¹' {0}ᶜ
  have hB'o : IsOpen B' := (dOn_det W hWd).continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton
  have hdet : ∀ b ∈ B', (W b).det ≠ 0 := fun b hb => hb.2
  have hb₀' : b₀ ∈ B' := by
    refine ⟨hb₀, ?_⟩
    show (V b₀ * R₀).det ≠ 0
    rw [hR₀, Matrix.det_one]
    exact one_ne_zero
  let R : (Fin m → ℂ) → Matrix (Fin (Module.finrank ℤ D.La)) (Fin g) ℂ := fun b => R₀ * (W b)⁻¹
  have hVR : ∀ b ∈ B', V b * R b = 1 := fun b hb => by
    show V b * (R₀ * (W b)⁻¹) = 1
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet b hb))
  let F : (Fin m → ℂ) → (S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) := fun b =>
    if hb : b ∈ B' then restr (V b) (R b) S (hVR b hb) (hSV b hb.1)
    else restr (V b₀) (R b₀) S (hVR b₀ hb₀') (hSV b₀ hb₀)
  have hF : ∀ b (hb : b ∈ B'), F b = restr (V b) (R b) S (hVR b hb) (hSV b hb.1) := fun b hb => dif_pos hb
  have hFd : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B' := by
    intro a i j
    refine DifferentiableOn.congr (f := fun b => (V b * a.1 * R b) i j) ?_ ?_
    · refine dOn_mul (fun b => V b * a.1) R ?_ ?_ i j
      · exact dOn_mul V (fun _ => a.1) (fun i j => (hVd i j).mono Set.inter_subset_left)
          (fun _ _ => differentiableOn_const _)
      · exact dOn_mul (fun _ => R₀) (fun b => (W b)⁻¹) (fun _ _ => differentiableOn_const _)
          (dOn_inv W (fun i j => (hWd i j).mono Set.inter_subset_left) hdet)
    · intro b hb
      rw [hF b hb]
      rfl
  obtain ⟨Q, hQh, hQp, hQa⟩ := GlobalTheory.T.gram_re_posDef_adjoint_period O bar g ρ D (P b₀) _ e hper
  have hcl : ∀ x ∈ S, ∃ y ∈ S, Q * y = xᴴ * Q := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨actM D e ℂ (bar a), Algebra.subset_adjoin ⟨bar a, rfl⟩, hQa a⟩
    | algebraMap c =>
      refine ⟨algebraMap ℂ _ (star c), Subalgebra.algebraMap_mem _ _, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, hu'⟩ := hx
      obtain ⟨v, hv, hv'⟩ := hy
      exact ⟨u + v, S.add_mem hu hv, by rw [Matrix.mul_add, hu', hv', Matrix.conjTranspose_add, Matrix.add_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, hu'⟩ := hx
      obtain ⟨v, hv, hv'⟩ := hy
      exact ⟨v * u, S.mul_mem hv hu, by
        rw [← Matrix.mul_assoc, hv', Matrix.mul_assoc, hu', Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩
  haveI : IsSemisimpleRing S := GlobalTheory.T.isSemisimpleRing_of_posDef_adjoint_closed _ Q S hQh hQp hcl
  obtain ⟨B'', h, hB''o, hb₀'', hB''sub, hh1, hhd, hhu⟩ := GlobalTheory.T.holomorphic_family_conj_constant S g m B' b₀ F hB'o hb₀' hFd
  refine ⟨B'', fun b => (h b)⁻¹, hB''o, hb₀'', hB''sub.trans Set.inter_subset_left, by simp [hh1], ?_, ?_⟩
  · exact dOn_inv h hhd (fun b hb => ((Matrix.isUnit_iff_isUnit_det _).1 (hhu b hb).1).ne_zero)
  · intro b hb
    obtain ⟨hu, hconj⟩ := hhu b hb
    have hbB' := hB''sub hb
    have hud : IsUnit (h b).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    refine ⟨Matrix.isUnit_nonsing_inv_iff.2 hu, fun a x => ?_⟩
    let s : S := ⟨actM D e ℂ a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
    have h1 : F b s * V b = V b * actM D e ℂ a := by
      rw [hF b hbB']
      exact restr_mul _ _ _ _ _ s
    have h2 : F b₀ s = ρ a := by
      have e1 : F b₀ s * V b₀ = ρ a * V b₀ := by
        rw [hF b₀ hb₀', restr_mul]
        show perM D e (P b₀) * actM D e ℂ a = ρ a * perM D e (P b₀)
        rw [perM_mul_actM]
        ext i j
        simp [perM, hper.1 a, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      calc F b₀ s = F b₀ s * V b₀ * R₀ := by rw [Matrix.mul_assoc, hR₀, Matrix.mul_one]
        _ = ρ a * V b₀ * R₀ := by rw [e1]
        _ = ρ a := by rw [Matrix.mul_assoc, hR₀, Matrix.mul_one]
    have h3 : (h b)⁻¹ * F b s = ρ a * (h b)⁻¹ := by
      have hc := hconj s
      rw [h2] at hc
      have hi : h b * (h b)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hud
      have hi' : (h b)⁻¹ * h b = 1 := Matrix.nonsing_inv_mul _ hud
      calc (h b)⁻¹ * F b s = (h b)⁻¹ * (F b s * h b) * (h b)⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
        _ = (h b)⁻¹ * (h b * ρ a) * (h b)⁻¹ := by rw [hc]
        _ = ρ a * (h b)⁻¹ := by rw [← Matrix.mul_assoc (h b)⁻¹, hi', Matrix.one_mul]
    rw [apply_smul_eq D e (P b) a x, apply_eq_mulVec D e (P b) x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    congr 1
    change (h b)⁻¹ * (V b * actM D e ℂ a) = ρ a * (h b)⁻¹ * V b
    rw [← h1, ← Matrix.mul_assoc, h3]

end GlobalTheory.PELU.Retype
