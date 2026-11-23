import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.He2

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem fin_reps {X : Type} {α : Type 1} [Finite X] (Q : X → α → Prop) :
    ∃ (k : ℕ) (Dl : Fin k → α), ∀ x D, Q x D → ∃ j, Q x (Dl j) := by
  obtain ⟨k, ⟨ε⟩⟩ := Finite.exists_equiv_fin {x // ∃ D, Q x D}
  refine ⟨k, fun j => (ε.symm j).2.choose, fun x D h => ⟨ε ⟨x, D, h⟩, ?_⟩⟩
  have := (ε.symm (ε ⟨x, D, h⟩)).2.choose_spec
  simp only [Equiv.symm_apply_apply] at this ⊢
  exact this

set_option maxHeartbeats 4000000 in

def ClauseB {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (Dl j) w)) ∧
        Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) = Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)) ∧
        FiniteDimensional ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))

set_option maxHeartbeats 4000000 in

theorem candB (hEq : StrictEqv) (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ClauseB F₀ d := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := fin_reps (X := Σ i : F₀.C.ι, Fin (kA i) × Fin (kB i)) (α := Pre E n) fun x D =>
    ∃ Pa Pb, IsJoin (F₀.μ ^ (n - F₀.C.a x.1)) (F₀.μ ^ F₀.C.a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨⟨ja, ha⟩, ⟨jb, hb⟩⟩ := hcls i s₁ s₂ Pa Pb D hc
  obtain ⟨j, Pa', Pb', hj, ha', hb'⟩ := hD ⟨i, ja, jb⟩ D ⟨Pa, Pb, hc.ctx.join, ha, hb⟩
  have hs : Strict D (Dl j) := hSJ E n _ _ _ _ Pa Pa' Pb Pb' D _ hc.ctx.join hj
    ((hEq E _ Pa _ Pa').2 ha ((hEq E _ Pa' _ Pa').1 ha')) ((hEq E _ Pb _ Pb').2 hb ((hEq E _ Pb' _ Pb').1 hb'))
  have hI := hII _ _ _ (prodAt D w) (prodAt (Dl j) w) (hSPr E n D (Dl j) hs w) (F₀.d₀.K' w)
  exact ⟨j, fun τ => hI.1 τ.V τ.ρ, hI.2.1, hAd E n (Dl j) w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1⟩

end PositivityTheory.Rg.BcB.F.FX.Bo.He2

end
