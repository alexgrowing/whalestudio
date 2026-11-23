import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTripleMatchingExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTripleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareLM

theorem localMatching : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  intro hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, ρ, q, q', hq, hq', hrk, hirr, hfac⟩ := GlobalTheory.T.polynomial_representation_triple hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  let ι := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}
  have hirr' : ∀ N : Submodule ℂ Pr, (∀ i : ι, ∀ x ∈ N, ρ i.1.1 i.1.2 x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hirr N fun τ Y hY x hx => hN ⟨(τ, Y), hY⟩ x hx
  have hS := GlobalTheory.dixmier_commutant_scalar ι Pr (fun i => ρ i.1.1 i.1.2) hrk hirr'
  obtain ⟨h0, hadd, hsmul, hfadd, hfsmul⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ true W X A B
  obtain ⟨h0', hadd', hsmul', hfadd', hfsmul'⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ false W₁ X A₁ B
  refine ⟨Pr, q, q', hq, hq', fun α β htr hexp => ⟨GlobalTheory.T.weil_triple_matching_exists hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B α β htr, ?_⟩⟩
  intro ωA ωB Pi rf rl p p' hm
  obtain ⟨hfa, hfb⟩ := hfac α β htr hexp ωA ωB Pi rf rl p p' hm
  let S : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {f | IsFinF ψ θ true A B f}, add_mem' := fun hf hg => hadd _ _ hf hg, zero_mem' := h0,
      smul_mem' := fun c _ hf => hsmul c _ hf }
  let S' : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {f | IsFinF ψ θ false A₁ B f}, add_mem' := fun hf hg => hadd' _ _ hf hg, zero_mem' := h0',
      smul_mem' := fun c _ hf => hsmul' c _ hf }
  let βA : S →ₗ[ℂ] PolF D X.rank W.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p (fockF ψ θ true A B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  let βB : S' →ₗ[ℂ] PolF D X.rank W₁.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p' (fockF ψ θ false A₁ B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd' _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul' _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} {P : Type} [AddCommGroup P] [Module ℂ P] (pp : (WO M X → ℂ) →ₗ[ℂ] P),
      (algF ψ θ ε A' B).map pp = ⊤ →
      Submodule.span ℂ {y | ∃ f : {f // IsFinF ψ θ ε A' B f}, ∃ Q, y = pp (fockF ψ θ ε A' B f.1 Q)} = ⊤ := by
    intro M ε A' P _ _ pp h
    rw [← h, algF, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨f, Q, rfl⟩; exact ⟨_, ⟨f.1, Q, f.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, Q, hf, rfl⟩, rfl⟩; exact ⟨⟨f, hf⟩, Q, rfl⟩
  obtain ⟨Pf, r, r', e, hr, hr', he, he'⟩ := GlobalTheory.SquareLM.productForm ι Pr Pi _ _ _ _ (fun i => ρ i.1.1 i.1.2) (fun i => rl i.1.1 i.1.2)
    q q' βA βB ⊤ ⊤ hq hq' hirr' hS
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfa f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfb f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (by
      rw [← hspan p hm.mapA.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
    (by
      rw [← hspan p' hm.mapB.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
  obtain ⟨r₀, hr₀⟩ := LinearMap.exists_extend r
  obtain ⟨r₀', hr₀'⟩ := LinearMap.exists_extend r'
  have e₁ : ∀ f (hf : IsFinF ψ θ true A B f), r₀ f = r ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀ ⟨f, hf⟩
  have e₂ : ∀ f (hf : IsFinF ψ θ false A₁ B f), r₀' f = r' ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀' ⟨f, hf⟩
  refine ⟨Pf, r₀, r₀', e, fun x => ?_, fun x => ?_, fun f hf P => ?_, fun f hf P => ?_⟩
  · obtain ⟨f, _, h⟩ := hr x; exact ⟨f.1, f.2, by rw [e₁ f.1 f.2]; exact h⟩
  · obtain ⟨f, _, h⟩ := hr' x; exact ⟨f.1, f.2, by rw [e₂ f.1 f.2]; exact h⟩
  · rw [e₁ f hf]; exact he ⟨f, hf⟩ trivial P
  · rw [e₂ f hf]; exact he' ⟨f, hf⟩ trivial P

end GlobalTheory.SquareLM

end
