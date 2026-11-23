import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.JacStages

namespace GlobalTheory.CompanionTheory.CoarseOcc

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  haveI : Nontrivial W := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  refine ⟨(v : V), 0, fun h0 => hu ?_⟩
  have hv0 : v = 0 := Subtype.ext h0
  rw [hv0, map_zero]

theorem sum_concat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s : ℕ}
    (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ i, (x a i).1 := by
  calc ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
        Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
    _ = ∑ a, ∑ i, (x a i).1 := Fintype.sum_sigma _

theorem exists_one_le_jm_coarse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  intro k _ _ _ _ hA s N c x _ hcat V _ _ π hs _ h1
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := (sum_concat c x).symm.trans hcat
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s N d e c (fun a b => (x a b).1) e' V π
  have hsub : IsSubquotient (piTensor fun l => (concat c x l).rep) (jac (refinePlace e e') π) := by
    rw [hE]
    exact jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
  have hnt := nontrivial_of_isSubquotient (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (concat c x)) hsub
  have hnt2 := @Function.Surjective.nontrivial _ _ hnt _ φS.symm.surjective
  have hnt3 := @Function.Surjective.nontrivial _ _ hnt2 _
    (Submodule.Quotient.mk_surjective (twKer (jac e π) (relUnipD k e') 1))
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hnt3
  let T : IrrRep (Levi k fun a => Fin (d a)) := ⟨Y, τ, hτs.isSmooth (isSmooth_jac e hs), hτ⟩
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d T
  refine ⟨fun a => ⟨d a, σ a⟩, hd, fun _ => rfl, ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)⟩
  exact (isSubquotient_of_equiv φ.symm).trans hτs

end GlobalTheory.CompanionTheory.CoarseOcc

end
