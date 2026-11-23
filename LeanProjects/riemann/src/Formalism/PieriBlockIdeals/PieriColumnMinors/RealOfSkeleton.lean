import Formalism.PieriBlockIdeals.PieriColumnMinors.LrjTransposeLift
import Formalism.PieriBlockIdeals.PieriColumnMinors.LriEVPowCoe
import Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem levZ_rowDiv (p q w : ℕ) (lam2 : Fin q → ℕ) (b b' : Fin q) (k : ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (hf : f ∈ LevZ p q w lam2) :
    rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k f ∈ LevZ p q w lam2 := by
  unfold LevZ at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    exact Submodule.subset_span ⟨(b, b', k) :: ω, rfl⟩
  | zero => simpa [rowDiv] using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k (c • x) =
        c • rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k x :=
      map_zsmul (rowDivL ℚ (n := p + q) (Fin.natAdd p b) (Fin.natAdd p b') k) c x
    rw [e]
    exact Submodule.smul_mem _ c hx

theorem delL_stable (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (b b' : Fin q)
    (u : (rationalBlockModuleSetting p q w lam2).W) (hu : u ∈ DelLR l hl p q w lam2) :
    (rationalBlockModuleSetting p q w lam2).EW b b' u ∈ DelLR l hl p q w lam2 := by
  obtain ⟨m, hm, hmu⟩ := (mem_locSpan _ _ _ _).1 hu
  refine (mem_locSpan _ _ _ _).2 ⟨m, hm, ?_⟩
  rw [← map_zsmul]
  rw [mem_MW] at hmu ⊢
  have e : ((((rationalBlockModuleSetting p q w lam2).EW b b' (m • u) : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') 1 (((m • u : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) :
        MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) := by
    rw [rowDiv_one]
    rfl
  rw [e]
  exact levZ_rowDiv p q w lam2 b b' 1 _ hmu

theorem real_of_skeleton : RealOfSkeleton := by
  intro hC _hL hP hCol l p q w lam2 ξ hl ha hb hξ i' eL heL i μ hd hd2 x hx
  obtain ⟨hxN, hxμ⟩ := hx
  rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule] at hxμ
  have hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2) := by
    rw [lrc_intQ_apply]
    exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) _ _ _ x hxN
  have inputs : LemmaDInputs3 (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) i w lam2 (DelLR l hl p q w lam2)
      (xiOf ξ) (lamOf p q w lam2) (l : Zl l) eL i' :=
    { scalar := rfl
      le_w := hb
      contra := real_contragredient p q w lam2
      generated := real_generated p q w lam2 ha hb
      nondeg := real_nondegenerate p q w lam2
      stable := delL_stable l hl p q w lam2
      pieri := hP p q w lam2 ha hb i
      columns := fun tau htau => hCol p q w lam2 ha hb i tau (by simpa using htau)
      dominant := dominant_xi ξ hξ
      expL := expL_real hC l hl p q w lam2 ha hb ξ i' eL heL }
  have hdep : ∑ α : Fin p, (fun a => ((μ (idx p q a) : ℕ) : ℤ)) (Sum.inl α) + (i : ℤ) =
      (Fintype.card (Fin p) : ℤ) * (w : ℤ) := by
    simp only [Fintype.card_fin]
    have := hd
    unfold LD.IsDepth at this
    exact_mod_cast this
  have hxi : xiOf ξ (lamOf p q w lam2 - fun a => ((μ (idx p q a) : ℕ) : ℤ)) ≤ i' :=
    calc xiOf ξ (lamOf p q w lam2 - fun a => ((μ (idx p q a) : ℕ) : ℤ)) = LD.depth2 ξ (LD.blockWt p q w lam2) μ :=
          xiOf_depth2 ξ _ μ
      _ ≤ i' := hd2
  have h := depth_skeleton_third_form_holds (Zl l) ℚ (VQ p q w lam2) (Fin p) q (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) i w
    lam2 (DelLR l hl p q w lam2) (xiOf ξ) (lamOf p q w lam2) l eL i' hl (zl_unit hl) inputs
    (fun a => ((μ (idx p q a) : ℕ) : ℤ)) hdep hxi ⟨intQ _ _ x, hx'⟩ (mem_dual l hl p q w lam2 ha hb x hxN hx')
    (wt_of_hom p q w lam2 x hx' μ hxμ)
  rw [Fintype.card_fin] at h
  exact concl l hl p q w lam2 x hx' _ h.1

theorem real_of_pieri : RealOfPieri :=
  fun hP hCol => real_of_skeleton coefficient_word lower_triangular_integral hP hCol

end Formalism.CohomologicalDescent.LR
