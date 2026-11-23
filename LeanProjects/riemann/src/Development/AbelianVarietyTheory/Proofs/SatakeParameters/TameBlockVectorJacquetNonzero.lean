import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DoubleCosetSetoidRelIffMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

abbrev sizes (r t : ℕ) : Fin (t + 1) → ℕ := Fin.cons r (fun _ => 1)

theorem sum_sizes (r t : ℕ) : ∑ a, sizes r t a = r + t := by simp [sizes, Fin.sum_cons]

def blocks (r t : ℕ) : (Σ a : Fin (t + 1), Fin (sizes r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sizes r t)

theorem blocks_zero (r t : ℕ) (i : Fin r) : blocks r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  have hv := stdBlocks_val (sizes r t) (sum_sizes r t) 0 i
  haveI : IsEmpty (Fin ((0 : Fin (t + 1)) : ℕ)) := by simp only [Fin.val_zero]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hv
  exact hv

theorem blocks_succ (r t : ℕ) (j : Fin t) (i : Fin (sizes r t j.succ)) :
    blocks r t ⟨j.succ, i⟩ = Fin.natAdd r j := by
  ext
  have hi : (i : ℕ) = 0 := by have := i.2; simp [sizes] at this; omega
  simp [blocks, stdBlocks_val, hi, Fin.sum_univ_succ, sizes]

def zeroIdx (r t : ℕ) (j : Fin t) : Fin (sizes r t j.succ) := ⟨0, by simp [sizes]⟩

theorem natAdd_eq (r t : ℕ) (j : Fin t) : Fin.natAdd r j = blocks r t ⟨j.succ, zeroIdx r t j⟩ :=
  (blocks_succ r t j _).symm

theorem blk_castAdd (r t : ℕ) (i : Fin r) : blk (blocks r t) (Fin.castAdd t i) = 0 := by
  unfold blk; rw [← blocks_zero, Equiv.symm_apply_apply]

theorem blk_natAdd (r t : ℕ) (j : Fin t) : blk (blocks r t) (Fin.natAdd r j) = j.succ := by
  unfold blk; rw [natAdd_eq, Equiv.symm_apply_apply]

theorem natAdd_ne_castAdd {r t : ℕ} (i : Fin t) (j : Fin r) : Fin.natAdd r i ≠ Fin.castAdd t j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem det_of_lowerLeft {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0) :
    M.det = (M.submatrix (Fin.castAdd t) (Fin.castAdd t)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁, h0]
  rw [this, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem det_lowerRight {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (h1 : M.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1) :
    (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = M.det := by
  rw [det_of_lowerLeft M h0, h1, det_one, one_mul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stab {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (v : W) : Subgroup G :=
  GlobalTheory.DoubleCosetSetoid.repStabilizer ρ v

theorem KOne_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsTame χ) {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    KOne k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  have hKO := GlobalTheory.StepData.KOne_le_KO hh
  have hm := GlobalTheory.StepData.mem_KOne.1 hh
  have hM : GlobalTheory.StepData.MaxM (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) - 1) := by
    intro i j
    have := hm (Fin.natAdd r i) (Fin.natAdd r j)
    simpa [Matrix.one_apply] using this
  obtain ⟨g', hg', hgv⟩ := GlobalTheory.StepData.exists_mem_KOne hM
  have hu := GlobalTheory.StepData.det_of_mem_KOne hg'
  have key := hv h hKO (fun i j => by
      have := hm (Fin.natAdd r i) (Fin.castAdd t j)
      simpa [Matrix.one_apply, natAdd_ne_castAdd i j] using this)
    (fun i j => by
      have := hm (Fin.castAdd t i) (Fin.castAdd t j)
      simpa [Matrix.one_apply] using this)
    (Matrix.GeneralLinearGroup.det g') (by rw [Matrix.GeneralLinearGroup.val_det_apply, hgv])
  show π h v = v
  rw [key, hχ _ hu, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipRad_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (blocks r t) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hh.1
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j =>
    mem_parab.1 hP _ _ (by rw [blk_castAdd, blk_natAdd]; exact Fin.succ_pos i)
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [← blocks_zero]
      exact (hD 0 i i).trans (Matrix.one_apply_eq _)
    · rw [if_neg hij]
      rw [← blocks_zero, ← blocks_zero]
      exact (hD 0 i j).trans (Matrix.one_apply_ne hij)
  have hdet : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 1 := by
    rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, det_eq_one_of_mem_unipRad k hh.1,
      Units.val_one]
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) 1 (by rw [hdet, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_leviEmb {α n : Type} {m : α → Type} [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (y : Levi k m) (hy : ∀ a, GlobalTheory.StepData.IntM (y a).val) :
    GlobalTheory.StepData.IntM (leviEmb k e y).val := by
  intro p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective q
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    exact hy a i j
  · rw [leviEmb_apply_ne k e y h]
    exact zero_mem _

abbrev single {r t : ℕ} (j : Fin t) (g : GL (Fin (sizes r t j.succ)) k) : Levi k (fun a => Fin (sizes r t a)) :=
  Pi.mulSingle j.succ g

theorem single_mem_KO {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) (a : Fin (t + 1)) : single j g a ∈ KO k (Fin (sizes r t a)) := by
  by_cases ha : a = j.succ
  · subst ha
    rw [single, Pi.mulSingle_eq_same]
    exact hg
  · rw [single, Pi.mulSingle_eq_of_ne ha]
    exact one_mem _

theorem deltaHalf_single {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) : deltaHalf k (fun a => Fin (sizes r t a)) (single j g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (single_mem_KO j hg a)

theorem act_single {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) (j : Fin t)
    {g : GL (Fin (sizes r t j.succ)) k} (hg : g ∈ KO k (Fin (sizes r t j.succ))) :
    π (leviEmb k (blocks r t) (single j g)) v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (blocks r t) (single j g) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (single_mem_KO j hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (single_mem_KO j hg a))
  have h0 : ∀ (i : Fin t) (j' : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j') = 0 := fun i j' => by
    rw [natAdd_eq, ← blocks_zero]
    exact leviEmb_apply_ne k _ _ (Fin.succ_ne_zero i) _ _
  have hx0 : single j g 0 = 1 := Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm _
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    have hx0' : ((single j g 0 : GL (Fin (sizes r t 0)) k) : Matrix (Fin (sizes r t 0)) (Fin (sizes r t 0)) k) = 1 := by
      rw [hx0, Units.val_one]
    ext i i'
    rw [Matrix.submatrix_apply, ← blocks_zero, ← blocks_zero, hdef]
    exact (leviEmb_apply_same k (blocks r t) (single j g) 0 i i').trans (congrFun (congrFun hx0' i) i')
  have key := hv h hKO (fun i j' => by simp [h0]) (fun i j' => by
      have := congrFun (congrFun h1 i) j'
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) (Matrix.GeneralLinearGroup.det g) (by
      rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, hdef, det_leviEmb k,
        Finset.prod_eq_single j.succ (fun b _ hb => by rw [single, Pi.mulSingle_eq_of_ne hb, map_one]) (by simp),
        single, Pi.mulSingle_eq_same])
  exact key

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

theorem exists_jacquet_ne_zero_of_isBlockVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  intro hP k _ _ _ _ r t χ π v hχ hv0 hv
  refine ⟨blocks r t, Submodule.Quotient.mk v, ?_, ?_⟩
  · intro hx
    apply hv0
    refine hP k (r + t) (t + 1) _ (blocks r t) π v ?_ hx
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro j g hg
    rw [GlobalTheory.SmGL.jac_mk, deltaHalf_single j hg, act_single hv j hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlock

end
