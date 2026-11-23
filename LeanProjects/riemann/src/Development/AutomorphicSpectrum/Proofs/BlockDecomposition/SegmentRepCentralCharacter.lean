import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistAbsPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicInductionCentralCharacterProd
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZlScalar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow_range (u : kˣ) (n : ℕ) :
    ∏ a ∈ Finset.range n, ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ) =
      ((absPow k (((n * (n - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [← Finset.sum_range_id]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Nat.cast_add, absPow_add, MonoidHom.mul_apply,
      Units.val_mul]

theorem prod_fin_absPow (l : ℕ) (c : ℂ) (u : kˣ) :
    ∏ a : Fin l, (c * ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)) =
      c ^ l * ((absPow k (((l * (l - 1) / 2 : ℕ) : ℂ)) u : ℂˣ) : ℂ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun a => ((absPow k ((a : ℕ) : ℂ) u : ℂˣ) : ℂ)), prod_absPow_range]

theorem smul_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f)
    (g : G) (C : ℂ) (h : ∀ w, π g w = C • w) (v : W) : σ g v = C • v := by
  obtain ⟨w, rfl⟩ := hf v
  rw [← map_smul, ← h w]
  exact (Representation.IntertwiningMap.isIntertwining π σ f g w).symm

theorem exists_surjective_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) :
    ∃ f : π.IntertwiningMap σ, Function.Surjective f :=
  let ⟨_, f, hf, _⟩ := h
  ⟨f, hf⟩

theorem smul_of_isCosocle {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π)
    (g : G) (C : ℂ) (hg : ∀ w, π g w = C • w) (v : W) : σ g v = C • v :=
  let ⟨f, hf⟩ := exists_surjective_of_isCosocle h
  smul_of_surjective f hf g C hg v

theorem scalarBy_term (Δ : Segment k) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) (a : Fin Δ.len) :
    Zl.ScalarBy (Δ.term a) t (c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) :=
  GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first ((a : ℕ) : ℂ) t c hc

theorem scalarBy_lseg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) (y : IrrGL k) (hy : IsLSeg Δ y.rep) (t : kˣ) (c : ℂ) (hc : Zl.ScalarBy Δ.first t c) :
    Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  rcases hy with ⟨hd, hco⟩
  have key := GlobalTheory.CompanionTheory.ZCentre.prodIrr_scalar k Δ.len y.1 Δ.term hd t (fun a => c * ((absPow k ((a : ℕ) : ℂ) (t ^ Δ.d) : ℂˣ) : ℂ)) (scalarBy_term Δ t c hc)
  simp only [prod_fin_absPow] at key
  intro v
  exact smul_of_isCosocle hco (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) _ key v

end GlobalTheory.CompanionTheory.ZlScalar
