import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2

open Classical GlobalTheory.TopStep in

theorem cosetIn_smul_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr q q' γ h1 h2
  funext P
  have key : ∀ y ∈ q.1.2, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu q'.1.1 P).symm (γ.1 y) - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : j + 1 = R.m
      swap
      · have h0 : q.1.2 = ∅ := by
          have := q.2
          rw [ysAt_ys_of_ne sel mu cst hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet q hj
      have hy' : y - y0 ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N
          (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : X.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : X.E) • y ∈ q.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : X.E) • y = (qOf P.1 : X.E) • y0 + (qOf P.1 : X.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : Pr.vGs := ⟨P.1, hP⟩
      have hd : q'.1.1.deco.1 = q.1.1.deco.1.act γ.1 1 := by
        rw [h1]
        rfl
      have hf : IsLiftFr q.1.1.deco.1 w (q.1.1.deco.1.liftFr w) := liftFr_spec q.1.1.deco.2 w
      have hf' : IsLiftFr (q.1.1.deco.1.act γ.1 1) w (q'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec q'.1.1.deco.2 w
      have e1 : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      have e2 : frsF sel mu q'.1.1 P = q'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      rw [e1, e2]
      let κ := passFr γ.1 1 hf hf'
      have hκ : redGL (R.N j) P.1 κ = 1 := redGL_passFr γ.1 1 hf hf'
      set f := q.1.1.deco.1.liftFr w
      set f' := q'.1.1.deco.1.liftFr w
      have e3 : f'.symm (γ.1 y) = κ.1 (f.symm y) := by
        show _ = f'.symm (γ.1 (f (f.symm y)))
        rw [LinearEquiv.apply_symm_apply]
      rw [e3]
      have hv0 : f.symm ((qOf P.1 : X.E) • y) ∈ stdAt X.E (R.N j) P.1 := by
        rw [← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      rw [map_smul] at hv0
      have hred := redV_redGL κ hv0
      rw [hκ, Units.val_one, Matrix.one_mulVec] at hred
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hq0 : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
      refine mem_stdAt.2 fun i => ?_
      have hi1 := mem_stdAt.1 (glint_mem κ hv0) i
      have hi2 := mem_stdAt.1 hv0 i
      have hr : redP P.1 ((κ.1 ((qOf P.1 : X.E) • f.symm y) - (qOf P.1 : X.E) • f.symm y) i) = 0 := by
        rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
        exact congrFun hred i
      have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
      convert this using 1
      rw [map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · rw [if_neg hP]
      have e : (frsF sel mu q'.1.1 P).symm (γ.1 y) = (frsF sel mu q.1.1 P).symm y := by
        rw [LinearEquiv.symm_apply_eq]
        unfold frsF
        rw [dif_neg hP, dif_neg hP, h1]
        show γ.1 y = γ.1 (q.1.1.fr _ ((((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 ((q.1.1.fr _).symm y)))
        simp
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  ext z
  simp only [cosetIn, Set.mem_setOf_eq]
  rw [h2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem hz (key y hy)
    rwa [← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨γ.1 y, ⟨y, hy, rfl⟩, ?_⟩
    have := sub_mem hz (key y hy)
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this

end GlobalTheory.Mem.Col2
