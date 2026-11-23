import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfJhMultNeZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToQuotEqZeroIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bot_ne_top_of_isSubquotient {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] {P : Representation ℂ (GL (Fin N) k) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h : IsSubquotient τ (jac e P)) : (⊥ : Subrepresentation P) ≠ ⊤ := by
  intro hb
  obtain ⟨T, f, hf⟩ := h
  haveI := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨t, rfl⟩ := hf w
  have hV : ∀ v : V, v = 0 := fun v => by
    have h1 : v ∈ (⊤ : Subrepresentation P).toSubmodule := trivial
    rw [← hb] at h1
    exact h1
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ t.1
  have h0 : t = 0 := Subtype.ext (by rw [← hu, hV u]; rfl)
  exact hw (by rw [h0, map_zero])

abbrev clx {n : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k)) : Fin 2 → IrrGL k := fun a => ⟨n, c a⟩

theorem jm_perm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k))
    (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c)) (σ : Equiv.Perm (Fin 2))
    (hy : ∑ a, (clx c (σ a)).1 = N) (hd : ∑ a, (clx c a).1 = N) :
    jm (fun a => clx c (σ a)) hy (prodIrr (clx c) hd) = 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (clx c) _ hd hy hc fun a => hc _]
  have : {e : Fin 2 ≃ Fin 2 | ∀ a, clx c (σ a) = clx c (e a)} = {σ} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => (Equiv.ext fun a => hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [this, Set.ncard_singleton]
  simp

theorem exists_surjective_jac {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : ρ.IsIrreducible)
    (S : Subrepresentation (parInd e ρ)) (hS : S.toRepresentation.IsIrreducible) :
    ∃ q : (jac e S.toRepresentation).IntertwiningMap ρ, Function.Surjective q := by
  haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hS
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  have h1 := GlobalTheory.CompanionTheory.FrobJm.frobMap_ne_zero e (incl S)
    ⟨v, fun h => hv (incl_injective S (h.trans (map_zero (incl S)).symm))⟩
  exact ⟨_, GlobalTheory.CompanionTheory.FrobJm.surjective_of_ne_zero hρ _ h1⟩

set_option maxHeartbeats 1000000 in

theorem two_cusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (hn : 0 < n)
    (c : Fin 2 → IrrCl (GL (Fin n) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = N) (hred : ¬ (prodIrr (clx c) hd).IsIrreducible) :
    ∃ S : Subrepresentation (prodIrr (clx c) hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr (clx c) hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (clx c a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (clx c a).rep)) := by
  have hy : ∑ a, (clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)).1 = N := hd
  have hP : IsSmooth (prodIrr (clx c) hd) := isSmooth_prodIrr _ hd
  have h₀ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (clx c)
  have h₁ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA fun a => clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)
  have m₀ : jm (clx c) hd (prodIrr (clx c) hd) = 1 := jm_perm hA c hc hinj 1 hd hd
  have m₁ := jm_perm hA c hc hinj Fin.revPerm hy hd
  refine exists_unique_sub (stdBlocks (fun a => (clx c a).1) hd) hP
    (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA _ hd)
    (bot_ne_top_of_isSubquotient _ h₀ (jhMult_ne_zero_iff.1 (ne_of_eq_of_ne m₀ one_ne_zero))) hred h₀ h₁
    m₀.le m₁.le ?_ ?_ ?_ ?_
  · intro Y _ _ τ hτ hs
    exact cell_cases (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1 (n := n) hn
      (X := fun a => (c a).rep.V) (fun a => (c a).rep.ρ)
      (fun a => (c a).rep.smooth) (fun a => (hc a).2) _ h₀ h₁ hτ hs
  · exact fun S hS => exists_surjective_jac (stdBlocks (fun a => (clx c a).1) hd) h₀ S hS
  · intro U _ _ Q hs hi hsub
    obtain ⟨e', he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA _ hd hc Q hs hi hsub
    rcases GlobalTheory.CompanionTheory.SegFine2.perm_two e' with rfl | rfl
    · exact Or.inl (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
    · exact Or.inr (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
  · intro S hS
    exact (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ _ _
      ((IsSubquotient.of_injective (incl S) (incl_injective S)).isSmooth hP) (hasFiniteLength_of_isIrreducible hS)

theorem concl_of_classes (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {d : ℕ} (hd0 : 0 < d)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Fin 2 → Representation ℂ (GL (Fin d) k) V)
    (c : Fin 2 → IrrCl (GL (Fin d) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = 2 * d) (E : ∀ a, (τ a).Equiv (c a).rep.ρ)
    (H : ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ).IsIrreducible) :
    ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor τ)) := by
  have he : GlobalTheory.Published.consecBlocks 2 d = stdBlocks (fun a => (clx c a).1) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun a => (clx c a).1) hd a j).symm)
    simp [mul_comm, add_comm]
  rw [he] at H ⊢
  let Φ : (multiProd (stdBlocks (fun a => (clx c a).1) hd) τ).Equiv (prodIrr (clx c) hd) := multiProdEquiv _ E
  exact GlobalTheory.CompanionTheory.SegFine2.exists_sub_of_equiv (stdBlocks (fun a => (clx c a).1) hd) Φ.symm (piTensorEquiv E).symm
    (two_cusp hA hd0 c hc hinj hd fun h => H (GlobalTheory.Parabolic.isIrreducible_of_equiv Φ.symm h))

theorem segment_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  intro H k _ _ _ _ d hd0 σ hc
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  let Δ : Segment k := ⟨d, hd0, σ.cl, ⟨σ, rfl, hc⟩, 2, two_pos⟩
  let c : Fin 2 → IrrCl (GL (Fin d) k) := fun a => (Δ.term a).2
  have hd : ∑ a, (clx c a).1 = 2 * d := Δ.sum_term_fst
  exact concl_of_classes hA hd0 (segTerm σ.ρ 2) c (fun a => Δ.isCusp_term a)
    (GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ) hd
    (fun a => (twistEquiv (equivRep σ) _).trans (Δ.first.twEquiv _ (isSmoothChar_absPow _)))
    (H k d hd0 σ hc)

end GlobalTheory.CompanionTheory.SegTwo

end
