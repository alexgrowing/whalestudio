import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_irreducible_GL_zero : ∃ t : IrrGL k, t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (GlobalTheory.LocGL.Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

private theorem equiv_of_isL [CharZero k] (HM : GlobalTheory.Published.LanglandsMultisegments) {𝔪 : Multiset (Segment k)}
    {n : ℕ} (c c' : IrrCl (GL (Fin n) k)) (hc : IsL 𝔪 (IrrGL.rep ⟨n, c⟩))
    (hc' : IsL 𝔪 (IrrGL.rep ⟨n, c'⟩)) : Nonempty (c'.rep.ρ.Equiv c.rep.ρ) := by
  obtain ⟨o, h0, ho⟩ := exists_irreducible_GL_zero (k := k)
  have hd : ∑ a, (![(⟨n, c⟩ : IrrGL k), o] a).1 = n := by simp [h0]
  have hs := (HM k).2 𝔪 0 ![⟨n, c⟩, o] ⟨n, c'⟩ hd hc ho (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero k (⟨n, c⟩ : IrrGL k) o h0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨n, c'⟩ : IrrGL k)) (IrrGL.rep (⟨n, c⟩ : IrrGL k)) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  exact (hs2.nonempty_equiv c'.rep.irr c.rep.irr).map fun e => e.symm

private theorem equiv_of_isL' [CharZero k] (HM : GlobalTheory.Published.LanglandsMultisegments) {𝔪 : Multiset (Segment k)}
    {n : ℕ} (p y : IrrRep (GL (Fin n) k)) (hp : IsL 𝔪 p.ρ) (hy : IsL 𝔪 y.ρ) : Nonempty (y.ρ.Equiv p.ρ) := by
  have ep : p.ρ.Equiv p.cl.rep.ρ := equivRep p
  have ey : y.ρ.Equiv y.cl.rep.ρ := equivRep y
  obtain ⟨e⟩ := equiv_of_isL HM p.cl y.cl (hp.of_equiv ep) (hy.of_equiv ey)
  exact ⟨(ey.trans e).trans ep.symm⟩

end

theorem UpperTheory.Lit.Cas.orderfree :
    GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.LanglandsMultisegments → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → IsCosocle π (prodIrr x hd) := by
  intro HC HM k _ _ _ _ _ 𝔪 h N x hd hx V _ _ π hπ
  obtain ⟨y, hy⟩ := HC k 𝔪 h N x hd hx
  have h1 : IsL 𝔪 y.ρ := ⟨h, x, hd, hx, hy⟩
  obtain ⟨e⟩ := equiv_of_isL' HM ⟨V, π, hπ.irr_smooth.2, hπ.irr_smooth.1⟩ y hπ h1
  exact hy.of_equiv e (.refl _)
