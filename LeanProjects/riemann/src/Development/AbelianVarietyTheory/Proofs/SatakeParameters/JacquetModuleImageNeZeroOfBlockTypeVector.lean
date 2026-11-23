import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

abbrev sz (r t : ℕ) : Fin 2 → ℕ := ![r, t]

theorem sum_sz (r t : ℕ) : ∑ a, sz r t a = r + t := by simp [sz]

def blocks2 (r t : ℕ) : (Σ a : Fin 2, Fin (sz r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sz r t)

theorem blocks2_zero (r t : ℕ) (i : Fin r) : blocks2 r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 0 i).trans ?_
  simp

theorem blocks2_one (r t : ℕ) (j : Fin t) : blocks2 r t ⟨1, j⟩ = Fin.natAdd r j := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 1 j).trans ?_
  simp [sz]

theorem twoE_false (r t : ℕ) (i : Fin r) : two (stdSum (rfl : r + t = r + t)) ⟨false, i⟩ = Fin.castAdd t i := by
  ext; simp

theorem twoE_true (r t : ℕ) (j : Fin t) : two (stdSum (rfl : r + t = r + t)) ⟨true, j⟩ = Fin.natAdd r j := by
  ext; simp

end GlobalTheory.JacBlockTwo

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inl' (r t : ℕ) (i : Fin r) : stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := by
  ext; simp

theorem stdSum_inr' (r t : ℕ) (j : Fin t) : stdSum (rfl : r + t = r + t) (Sum.inr j) = Fin.natAdd r j := by
  ext; simp

def IsUpperUnip {r t : ℕ} (g : GL (Fin (r + t)) k) : Prop :=
  (∀ (i : Fin t) (j : Fin r), (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.castAdd t j) = 0) ∧
  (∀ i j : Fin r, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.castAdd t i) (Fin.castAdd t j) =
    (1 : Matrix (Fin r) (Fin r) k) i j) ∧
  (∀ i j : Fin t, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.natAdd r j) =
    (1 : Matrix (Fin t) (Fin t) k) i j)

theorem mem_unipRad_two {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (two (stdSum (rfl : r + t = r + t))) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_two]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← stdSum_inl', ← stdSum_inr']; exact h0 i j
    · rw [← twoE_false, ← twoE_false]; exact hD false i j
    · rw [← twoE_true, ← twoE_true]; exact hD true i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j i => ?_, ?_⟩
    · have := h0 j i; rwa [← stdSum_inl', ← stdSum_inr'] at this
    · rintro (_ | _) i j
      · have := h1 i j; rwa [← twoE_false, ← twoE_false] at this
      · have := h2 i j; rwa [← twoE_true, ← twoE_true] at this

theorem mem_unipRad_blocks2 {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (blocks2 r t) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← blocks2_one, ← blocks2_zero]; exact h0 1 0 i j (by decide)
    · rw [← blocks2_zero, ← blocks2_zero]; exact hD 0 i j
    · rw [← blocks2_one, ← blocks2_one]; exact hD 1 i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · match a, b with
      | 0, 0 => intro i j hab; exact absurd hab (lt_irrefl _)
      | 0, 1 => intro i j hab; exact absurd hab (by decide)
      | 1, 0 => intro i j _; rw [blocks2_one r t i, blocks2_zero r t j]; exact h0 i j
      | 1, 1 => intro i j hab; exact absurd hab (lt_irrefl _)
    · match a with
      | 0 => intro i j; rw [blocks2_zero r t i, blocks2_zero r t j]; exact h1 i j
      | 1 => intro i j; rw [blocks2_one r t i, blocks2_one r t j]; exact h2 i j

theorem unipRad_blocks2 (r t : ℕ) :
    unipRad k (blocks2 r t) = unipRad k (two (stdSum (rfl : r + t = r + t))) := by
  ext g; rw [mem_unipRad_blocks2, mem_unipRad_two]

theorem unipRad_two_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (two (stdSum (rfl : r + t = r + t))) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨h0, h1, h2⟩ := mem_unipRad_two.1 hh.1
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by ext i j; exact h2 i j
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply]) 1
    (by rw [hsub, det_one, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

theorem mulSingle_mem_KO {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) (a : Bool) :
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) a ∈ KO k (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _
  · rw [Pi.mulSingle_eq_same]; exact hg

theorem deltaHalf_mulSingle {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    deltaHalf k (Two (Fin r) (Fin t)) (Pi.mulSingle true g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_mem_KO (r := r) hg a)

theorem act_mulSingle {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    π (leviEmb k (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle true g)) v =
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (two (stdSum (rfl : r + t = r + t)))
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_mem_KO hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_mem_KO hg a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [← twoE_true, ← twoE_false]
    exact leviEmb_apply_ne k _ _ (by decide) _ _
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Matrix (Fin r) (Fin r) k) i j :=
    fun i j => by
      rw [← twoE_false, ← twoE_false, hdef, leviEmb_apply_same, Pi.mulSingle_eq_of_ne (by decide)]
      rfl
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = g.val := by
    ext i j
    rw [Matrix.submatrix_apply, ← twoE_true, ← twoE_true, hdef, leviEmb_apply_same, Pi.mulSingle_eq_same]
  exact hv h hKO (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply])
    (Matrix.GeneralLinearGroup.det g) (by rw [hsub, Matrix.GeneralLinearGroup.val_det_apply])

theorem jacquet_ne_zero_of_isBlockVec_two : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  intro hP k _ _ _ _ r t χ V _ _ π v hsm hirr hχ hv0 hv
  refine ⟨?_, ?_⟩
  · intro hx
    apply hv0
    have hx' : (Submodule.Quotient.mk v : Jacquet π (unipRad k (blocks2 r t))) = 0 := by
      rw [unipRad_blocks2]; exact hx
    refine hP k (r + t) 2 (sz r t) (blocks2 r t) ⟨V, π, hsm, hirr⟩ v ?_ hx'
    rw [unipRad_blocks2]
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_two_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro g hg
    rw [jac_mk, deltaHalf_mulSingle hg, act_mulSingle hv hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlockTwo

end
