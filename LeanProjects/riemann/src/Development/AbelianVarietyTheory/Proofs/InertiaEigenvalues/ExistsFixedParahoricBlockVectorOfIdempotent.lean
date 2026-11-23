import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem conv_sum {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (T : G → W →ₗ[ℂ] W) (f : G → W)
    (hT : ∀ g h, T g (f h) = f (g * h)) (a b : MonoidAlgebra ℂ G) :
    (a.coeff.sum fun g c => c • T g (b.coeff.sum fun h d => d • f h)) = (a * b).coeff.sum fun k c => c • f k := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index', ha, ha']
      <;> intros <;> simp [add_smul]
  | single g c =>
    rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index',
        map_add, smul_add, hb, hb'] <;> intros <;> simp [add_smul]
    | single h d =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, Finsupp.sum_single_index, map_smul, hT, smul_smul] <;> simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}

def ee (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

theorem ee_inl (i : Fin r) : ee r t (Sum.inl i) = Fin.castAdd t i := by ext; simp [ee]

theorem ee_inr (j : Fin t) : ee r t (Sum.inr j) = Fin.natAdd r j := by ext; simp [ee]

variable (F) in

def dg (r t : ℕ) : GL (Fin r) F →* GL (Fin (r + t)) F := (emb₂ F (ee r t)).comp (MonoidHom.inl _ _)

variable (F) in

def bl (r t : ℕ) : GL (Fin (r + t)) F →* GL (Fin r ⊕ Fin t) F := reix F (ee r t).symm

theorem bl_apply (g : GL (Fin (r + t)) F) (a b : Fin r ⊕ Fin t) : (bl F r t g).val a b = g.val (ee r t a) (ee r t b) := by
  rw [bl, val_reix, Equiv.symm_symm]

theorem eq_of_bl {g g' : GL (Fin (r + t)) F} (H : (bl F r t g).val = (bl F r t g').val) : g = g' := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun H a) b
  rwa [bl_apply, bl_apply] at this

theorem dg_bl (A : GL (Fin r) F) : (bl F r t (dg F r t A)).val = fromBlocks A.val 0 0 1 := by
  ext a b
  rw [bl_apply]
  have := val_emb₂ F (ee r t) (A, 1)
  simp only [dg, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [this, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem bl_21 (g : GL (Fin (r + t)) F) (i : Fin t) (j : Fin r) :
    (bl F r t g).val.toBlocks₂₁ i j = g.val (Fin.natAdd r i) (Fin.castAdd t j) := by
  simp only [toBlocks₂₁, of_apply, bl_apply, ee_inr, ee_inl]

theorem bl_11 (g : GL (Fin (r + t)) F) (i j : Fin r) :
    (bl F r t g).val.toBlocks₁₁ i j = g.val (Fin.castAdd t i) (Fin.castAdd t j) := by
  simp only [toBlocks₁₁, of_apply, bl_apply, ee_inl]

theorem bl_22 (g : GL (Fin (r + t)) F) :
    (bl F r t g).val.toBlocks₂₂ = g.val.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  simp only [toBlocks₂₂, of_apply, bl_apply, ee_inr, submatrix_apply]

theorem intM_dg {A : GL (Fin r) F} (hA : IntM A.val) : IntM (dg F r t A).val := by
  intro a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun (dg_bl (t := t) A) a) b
  rw [bl_apply] at this
  rw [this]
  exact intM_fromBlocks.2 ⟨hA, intM_zero, intM_zero, intM_one⟩ a b

theorem dg_mem_KO {A : GL (Fin r) F} (hA : A ∈ KO F (Fin r)) : dg F r t A ∈ KO F (Fin (r + t)) :=
  GlobalTheory.StepData.mem_KO.2 ⟨intM_dg (GlobalTheory.StepData.mem_KO.1 hA).1,
    by rw [← map_inv]; exact intM_dg (GlobalTheory.StepData.mem_KO.1 hA).2⟩

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}
  {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin (r + t)) F) W}

theorem isBlockVec_add {v w : W} (hv : IsBlockVec χ π v) (hw : IsBlockVec χ π w) : IsBlockVec χ π (v + w) :=
  fun h hh h1 h2 u hu => by rw [map_add, hv h hh h1 h2 u hu, hw h hh h1 h2 u hu, smul_add]

theorem isBlockVec_smul (c : ℂ) {v : W} (hv : IsBlockVec χ π v) : IsBlockVec χ π (c • v) :=
  fun h hh h1 h2 u hu => by rw [map_smul, hv h hh h1 h2 u hu, smul_comm]

theorem isBlockVec_zero : IsBlockVec χ π (0 : W) := fun _ _ _ _ _ _ => by simp

theorem dg_fix {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KOne F (Fin r)) :
    π (dg F r t κ) v = v := by
  have key := hv _ (dg_mem_KO (GlobalTheory.StepData.KOne_le_KO hκ))
    (fun i j => by rw [← bl_21, dg_bl, toBlocks_fromBlocks₂₁]; simp)
    (fun i j => by
      rw [← bl_11, dg_bl, toBlocks_fromBlocks₁₁]
      have := (GlobalTheory.StepData.mem_KOne.1 hκ) i j
      rwa [Matrix.sub_apply, Matrix.one_apply] at this)
    1 (by rw [← bl_22, dg_bl, toBlocks_fromBlocks₂₂, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

theorem dg_isBlockVec {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KO F (Fin r)) :
    IsBlockVec χ π (π (dg F r t κ) v) := by
  intro h hh h1 h2 u hu
  have hd := dg_mem_KO (t := t) hκ
  have hK : (dg F r t κ)⁻¹ * h * dg F r t κ ∈ KO F (Fin (r + t)) := mul_mem (mul_mem (inv_mem hd) hh) hd
  obtain ⟨A, B, C, D, hE⟩ : ∃ A B C D, (bl F r t h).val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hΦ : (bl F r t ((dg F r t κ)⁻¹ * h * dg F r t κ)).val =
      fromBlocks ((κ⁻¹).val * A * κ.val) ((κ⁻¹).val * B) (C * κ.val) D := by
    rw [← map_inv (dg F r t) κ, map_mul, map_mul, Units.val_mul, Units.val_mul, dg_bl, dg_bl, hE,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hC : MaxM C := fun i j => by
    rw [show C i j = h.val (Fin.natAdd r i) (Fin.castAdd t j) by rw [← bl_21, hE, toBlocks_fromBlocks₂₁]]
    exact h1 i j
  have hA : MaxM (A - 1) := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    rw [show A i j = h.val (Fin.castAdd t i) (Fin.castAdd t j) by rw [← bl_11, hE, toBlocks_fromBlocks₁₁]]
    exact h2 i j
  have key := hv _ hK
    (fun i j => by rw [← bl_21, hΦ, toBlocks_fromBlocks₂₁]; exact hC.mul_intM (intM_of_mem_KO hκ) i j)
    (fun i j => by
      rw [← bl_11, hΦ, toBlocks_fromBlocks₁₁]
      have e : (κ⁻¹).val * A * κ.val - 1 = (κ⁻¹).val * (A - 1) * κ.val := by
        rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
      have := ((((GlobalTheory.StepData.mem_KO.1 hκ).2).mul_maxM hA).mul_intM (intM_of_mem_KO hκ)) i j
      rw [← e, Matrix.sub_apply, Matrix.one_apply] at this
      exact this)
    u (by
      rw [← bl_22, hΦ, toBlocks_fromBlocks₂₂]
      rw [← bl_22, hE, toBlocks_fromBlocks₂₂] at hu
      exact hu)
  have hh' : h * dg F r t κ = dg F r t κ * ((dg F r t κ)⁻¹ * h * dg F r t κ) := by group
  calc π h (π (dg F r t κ) v) = π (dg F r t κ) (π ((dg F r t κ)⁻¹ * h * dg F r t κ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, hh', map_mul, Module.End.mul_apply]
    _ = (χ u : ℂ) • π (dg F r t κ) v := by rw [key, map_smul]

theorem exists_of_isLiftN {p : ℕ} {g : GL (Fin r) (ZMod p)} {h : GL (Fin (r + t)) F} (H : IsLiftN g h) :
    ∃ A : GL (Fin r) F, dg F r t A = h ∧ IsLift g A := by
  set M : Matrix (Fin r) (Fin r) F := fun i j => h.val (Fin.castAdd t i) (Fin.castAdd t j) with hM
  have hΦ : (bl F r t h).val = fromBlocks M 0 0 1 := by
    ext (a | a) (b | b)
    · rw [bl_apply, ee_inl, ee_inl, fromBlocks_apply₁₁]
    · have := H (Fin.castAdd t a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.castAdd t a ≠ Fin.natAdd r b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.castAdd t b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.natAdd r a ≠ Fin.castAdd t b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.natAdd r b)
      rw [dif_neg (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      simp [bl_apply, ee_inr, this, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (bl F r t h).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (bl F r t h).isUnit
    rwa [hΦ, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one] at h1
  refine ⟨Matrix.nonsingInvUnit M hdet, eq_of_bl ?_, fun a b => ?_⟩
  · rw [dg_bl, hΦ]; rfl
  · have := H (Fin.castAdd t a) (Fin.castAdd t b)
    rw [dif_pos (show ((Fin.castAdd t a : Fin (r + t)) : ℕ) < r ∧ ((Fin.castAdd t b : Fin (r + t)) : ℕ) < r
      from ⟨a.isLt, b.isLt⟩)] at this
    exact this

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem exists_fixed_blockVec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  intro F _ _ _ _ p _ r t χ W _ _ π z x hp hz hx hnk
  obtain ⟨ℓ', hℓ', hne⟩ := hnk
  have hA : ∀ g, ∃ A : GL (Fin r) F, dg F r t A = ℓ' g ∧ IsLift g A := fun g => exists_of_isLiftN (hℓ' g)
  choose ℓ hℓ1 hℓ2 using hA
  have hx1 : ∀ h ∈ KOne F (Fin r), (π.comp (dg F r t)) h x = x := fun h hh => dg_fix hx hh
  have hT : ∀ g h, π (dg F r t (ℓ g)) (π (dg F r t (ℓ h)) x) = π (dg F r t (ℓ (g * h))) x := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact IsLift.apply_eq hp (π := π.comp (dg F r t)) hx1 ((hℓ2 g).mul hp (hℓ2 h)) (hℓ2 (g * h))
  refine ⟨z.coeff.sum fun g c => c • π (dg F r t (ℓ g)) x, ?_, ?_, ℓ, hℓ2, ?_⟩
  · simpa only [hℓ1] using hne
  · rw [Finsupp.sum]
    exact Finset.sum_induction _ _ (fun a b => isBlockVec_add) isBlockVec_zero
      (fun g _ => isBlockVec_smul _ (dg_isBlockVec hx ((hℓ2 g).mem_KO hp)))
  · have := conv_sum (fun g => π (dg F r t (ℓ g))) (fun h => π (dg F r t (ℓ h)) x) hT z z
    rw [hz] at this
    exact this

end GlobalTheory.BlockIdem
