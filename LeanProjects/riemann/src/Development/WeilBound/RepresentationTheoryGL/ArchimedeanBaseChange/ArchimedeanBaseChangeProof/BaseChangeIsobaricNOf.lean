import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitS
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.LocalL
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.InertR
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcN

def CsdAsc {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ (a d : ℕ) (P : CuspSub E a), P.IsUnitary ∧ GlobalTheory.DiscSpec.IsNormalised P ∧ P.IsCsd ∧ PositivityTheory.Rg.Rs.AscEmb V P d

structure IsBaseChangeN {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ}
    {N : Fin c → ℕ} (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (m : Fin c → (E →+* ℂ) → Multiset ℂ)
    (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, CsdAsc (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  sub : ∀ w, GlobalTheory.SmGL.IsSubquotient (P w).ρ (locProd h w (σ · w))
  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (P w).ρ (GlobalTheory.LFun.KGL w n)
  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (P w).ρ (GlobalTheory.LGrp.bcParam n α)
  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (P w).ρ
  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

def BaseChangeIsobaricN : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ)
        (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))), IsBaseChangeN π h V σ m P

structure Datum (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, CsdAsc (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def SatAt (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) (B : Fin D.c → Multiset ℂˣ) : Prop :=
  ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (B i)

def Weak (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
    {w | IsSplitAt w ∧ ¬ SplitAt π D w}.Finite

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

def RunSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Datum E n, Weak π D ∧
    (∀ w ∈ S, IsSplitAt w → SplitAt π D w) ∧ ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ B, SatAt D w B

def RunInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ D : Datum E n, Weak π D ∧
    ∀ B, SatAt D w B → ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → ∑ i, B i = GlobalTheory.LGrp.bcParam n α

def Rigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ D D' : Datum E n, Weak π D → Weak π D' → ∀ w,
    (∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
      GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))) ∧
    ∀ B, SatAt D w B → ∃ B', SatAt D' w B' ∧ ∑ i, B i = ∑ i, B' i

theorem core_of (hS : RunSplit) (hI : RunInert) (hR : Rigid) (hE : Unr E) (hn : 1 ≤ n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) :
    ∃ D : Datum E n, (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
      (∀ w, IsSplitAt w → SplitAt π D w) ∧
      ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ B, SatAt D w B ∧
        ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
          (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
          ∀ α, HasSatAt π w s ϖ q α → ∑ i, B i = GlobalTheory.LGrp.bcParam n α := by
  obtain ⟨D, hD, -, hsph⟩ := hS E hE n hn π hπ ∅ (by simp)
  refine ⟨D, hD.1, fun w hw => ?_, fun w hu hw => ?_⟩
  · obtain ⟨D', hD', h1, -⟩ := hS E hE n hn π hπ {w} (by simp)
    obtain ⟨P, hP, hc⟩ := h1 w (Finset.mem_singleton_self w) hw
    exact ⟨P, (hR E n hn π hπ D D' hD hD' w).1 P hP, hc⟩
  · obtain ⟨B, hB⟩ := hsph w hu hw
    obtain ⟨D', hD', h1⟩ := hI E hE n hn π hπ w hu hw
    obtain ⟨B', hB', e⟩ := (hR E n hn π hπ D D' hD hD' w).2 B hB
    exact ⟨B, hB, fun s ϖ q a b α hα => e.trans (h1 B' hB' s ϖ q a b α hα)⟩

open GlobalTheory.PfBCI in
theorem baseChangeIsobaricN_of (hS : RunSplit) (hI : RunInert) (hR : Rigid) : BaseChangeIsobaricN := by
  intro E _ _ _ hE n hn π hπ
  obtain ⟨D, hwt, hS', hU⟩ := core_of hS hI hR hE hn π hπ
  have hex : ∀ w, ∃ P, AtPlace π D.h D.σ w P := by
    intro w
    by_cases hs : IsSplitAt w
    · obtain ⟨P, hsub, hc⟩ := hS' w hs
      exact ⟨P, split_component D.h D.σ hs P hsub (split_spherical hπ hs P hc) hc⟩
    by_cases hu : IsUnramU π w
    · obtain ⟨B, hB, hsum⟩ := hU w hu hs
      obtain ⟨P, hsub, hsph, hsat⟩ := unram_component D.h w (D.σ · w) B hB
      refine ⟨P, hsub, fun _ => hsph, fun s' ϖ q hc hinv α hα => ?_, fun h' => absurd h' hs⟩
      rw [← hsum s' ϖ q hc hinv α hα]
      exact hsat
    · obtain ⟨P, hP'⟩ := local_subquotient D.h w (D.σ · w)
      exact ⟨P, hP', fun h' => absurd h' hu, inert_of_not_unram hu P, fun h' => absurd h' hs⟩
  choose P hPw using hex
  exact ⟨D.c, D.N, D.h, D.V, D.σ, D.m, P, D.pos, D.discrete, D.csd, D.loc, D.inf, fun w => (hPw w).1,
    fun w => (hPw w).2.1, fun w => (hPw w).2.2.1, fun w => (hPw w).2.2.2, hwt⟩

end PositivityTheory.Rg.BcN

end
