import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReduction

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in

theorem ptDet_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ hq r r' hfr hb hc
  suffices h2 : r.1.2 = r'.1.2 from Subtype.ext (Prod.ext hfr h2)
  have hd : r.1.1.deco = r'.1.1.deco := congrArg DecoF.deco hfr
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := (show PtAt R sel mu cst u j from r).mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := (show PtAt R sel mu cst u j from r').mem_ybSet hj
    have eN : r'.1.1.deco.1.N = r.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have hyin : y ∈ r.1.2 := by rw [eY, mem_coset, sub_self]; exact zero_mem _
    rw [eY, eY']
    apply coset_eq
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    by_cases hG : P.1 ∈ Pr.vGs
    · rw [if_pos hG, zpow_zero, inv_one, one_smul]
      have hm : r.1.1.deco.1.be ⟨P.1, hG⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar r ⟨P.1, hG⟩ := ⟨y, hyin, rfl⟩
      rw [hb] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos hG, zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos hG, _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq r.1.1.deco.2 ⟨P.1, hG⟩ (hq _ hG) h1 h2 hz' ez
    · rw [if_neg hG, zpow_natCast]
      have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hG
      have hfrP : frsF sel mu r.1.1 P = r.1.1.fr ⟨P.1, hPQ⟩ := by
        unfold frsF
        rw [dif_neg hG]
      have hc1 : (r.1.1.fr ⟨P.1, hPQ⟩).symm y ∈ cqOf r ⟨P.1, hPQ⟩ := ⟨y, hyin, by
        show ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r.1.1 P).symm y) ∈ _
        rw [hfrP, sub_self, smul_zero]
        exact zero_mem _⟩
      rw [hc] at hc1
      obtain ⟨y0, hy0, hmem⟩ := hc1
      change ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r'.1.1 P).symm y0) ∈ _ at hmem
      rw [if_neg hG, ← hfr, hfrP] at hmem
      have hA := (r.1.1.2 ⟨P.1, hPQ⟩ _).2 hmem
      change r.1.1.fr ⟨P.1, hPQ⟩ _ ∈ _ at hA
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hA
      rw [eY'] at hy0
      have hB := (mem_locLat _ _ _ _).1 (mem_coset.1 hy0) P
      rw [if_neg hG, zpow_natCast] at hB
      have := add_mem hA hB
      rwa [← smul_add, sub_add_sub_cancel] at this
  · have h1 := r.2
    have h1' := r'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.ChEx
