import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hk_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (v : V) :
    φ.toLinearEquiv (hk ρ K e v) = hk σ K e (φ.toLinearEquiv v) := by
  unfold hk
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)).trans
    (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (e q.out • ρ q.out v) = e q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem fixed_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (v : V) (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : GL ι F) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

end SlopeTestRemainingChoices

theorem choiceM : ChoiceM := by
  intro E _ _ _ n w K' k D _
  refine ⟨(Finset.univ.sup fun j => Module.finrank ℂ (fixed (prodAt (D j) w) K')) + 1, fun j => ?_⟩
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun j => Module.finrank ℂ (fixed (prodAt (D j) w) K')) (Finset.mem_univ j))

theorem choiceS_of
    (hI : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.IsolateAt (w.adicCompletion E) (Fin n))
    (hF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.FinSubq (w.adicCompletion E) (Fin n))
    (hP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.ProdFinLen (w.adicCompletion E) (Fin n)) : ChoiceS := by
  intro E _ _ _ n w K' hKo hKc P hP0 k D
  have hs : ∀ j, IsSmooth (prodAt (D j) w) := fun j => GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : ∀ j, GlobalTheory.SmGL.HasFiniteLength (prodAt (D j) w) := fun j =>
    hP E n w (Fin (D j).c) (fun i => Fin ((D j).N i)) (GlobalTheory.SmGL.stdBlocks (D j).N (D j).h)
      (fun i => ((D j).σ i w).V) (fun i => ((D j).σ i w).ρ) (fun i => ((D j).σ i w).smooth)
      (fun i => ((D j).σ i w).irred)
  choose J hJ W hW1 hW2 τ hτ hcov using fun j => hF E n w _ (prodAt (D j) w) (hs j) (hfl j)
  let _ : ∀ j, Fintype (J j) := hJ
  let _ : ∀ j i, AddCommGroup (W j i) := hW1
  let _ : ∀ j i, Module ℂ (W j i) := hW2
  let I : Type := Σ j : Fin k, {i : J j // IsEmpty ((τ j i).Equiv P.ρ)}
  obtain ⟨e, hIk, v₀, hv₀, l, hl1, hl, hkill⟩ :=
    hI E n w K' hKo hKc P.V P.ρ P.smooth P.irred hP0 I (fun x => W x.1 x.2.1) (fun x => τ x.1 x.2.1)
      (fun x => (hτ x.1 x.2.1).1) (fun x => (hτ x.1 x.2.1).2.1) (fun x => x.2.2)
  refine ⟨e, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, ?_⟩
  intro j τ' hsub hne v hv
  obtain ⟨i, ⟨φ⟩⟩ := hcov j τ'.V τ'.ρ τ'.irred hsub
  have hi : IsEmpty ((τ j i).Equiv P.ρ) := ⟨fun ψ => hne.false (φ.trans ψ)⟩
  apply φ.toLinearEquiv.injective
  rw [hk_equiv, map_zero]
  exact hkill ⟨j, i, hi⟩ _ (fixed_equiv φ K' v hv)

end PositivityTheory.Rg.BcB.F.Choice

end
