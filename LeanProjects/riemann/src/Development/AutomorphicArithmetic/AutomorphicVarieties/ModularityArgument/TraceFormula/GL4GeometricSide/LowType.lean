import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LowTypeB
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomological

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting.Low

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg PositivityTheory.Rg.Cz

private theorem hasChar_of {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (χ : Fin n → ℂ) (h : HasInfCharGL π.V τ (Multiset.map χ Finset.univ.val)) (l : Fin n → ℤ)
    (hl : ∀ k, χ k = (l k : ℂ) + ((n : ℂ) - 1) / 2) : HasChar (cx τ (lieOp π)) fun k => (l k : ℂ) := by
  intro u
  have e := (GlobalTheory.capelli_cuspSub E n π τ χ h).2 (u - ((n : ℂ) - 1) / 2)
  rw [sub_add_cancel] at e
  rw [e, Finset.prod_congr rfl fun k _ => show u - ((n : ℂ) - 1) / 2 + χ k = u + (l k : ℂ) by rw [hl]; ring]

end UpperTheory.V.Z.GSp4Splitting.Low

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg PositivityTheory.Rg.Cz UpperTheory.V.Z.GSp4Splitting.Low in
theorem UpperTheory.V.Z.GSp4Splitting.lowType :
    LowType := by
  classical
  intro E _ _ _ n hn π hr w lam hlam hch
  obtain ⟨hK, hc⟩ := J.kData_holds E n
  obtain ⟨ℓ, hℓ, hw⟩ := whitLie_holds E n π
  have hG := GK.gkData_holds E n π
  have ex : ∀ τ : E →+* ℂ, ∃ l : Fin n → ℤ, Function.Injective l ∧ (HasChar (cx τ (lieOp π)) fun k => (l k : ℂ)) ∧
      (τ = w.embedding → ∀ a, l a = lam a - (a : ℕ)) ∧
      (τ = barE E w.embedding → ∀ a, l a = -lam a - ((n : ℤ) - 1) + (a : ℕ)) := fun τ => by
    by_cases h1 : τ = w.embedding
    · subst h1
      refine ⟨fun a => lam a - (a : ℕ), StrictAnti.injective fun i j hij => ?_,
        hasChar_of π _ _ hch.1 _ fun k => ?_, fun _ _ => rfl, fun e => absurd e.symm (hK.ne _)⟩
      · have := hlam hij.le
        have : (i : ℕ) < j := hij
        omega
      · simp only [infOf, if_true]
        push_cast
        ring
    · by_cases h2 : τ = barE E w.embedding
      · subst h2
        refine ⟨fun a => -lam a - ((n : ℤ) - 1) + (a : ℕ), StrictMono.injective fun i j hij => ?_,
          hasChar_of π _ _ hch.2 _ fun k => ?_, fun e => absurd e h1, fun _ _ => rfl⟩
        · have := hlam hij.le
          have : (i : ℕ) < j := hij
          omega
        · simp only [infOf, Bool.false_eq_true, if_false]
          push_cast
          ring
      · obtain ⟨l, hl, hl'⟩ := GlobalTheory.CompanionTheory.RgCz.charInt_at π hr τ
        exact ⟨l, hl, hl', fun e => absurd e h1, fun e => absurd e h2⟩
  choose l hinj hchar h1 h2 using ex
  obtain ⟨s, hs⟩ := kType_holds n hn π.V (E →+* ℂ) (Kinf E n) _ _ _ _ hK hG l hinj hchar ℓ hℓ hw
  obtain ⟨ν, ψ, h0, hH, hcone⟩ := low_abs _ _ _ _ hK hG l s hs w.embedding lam hlam (h1 _ rfl) (h2 _ rfl)
  refine ⟨ν, ψ.1, ψ.2, fun e => h0 (Subtype.ext e), ⟨fun a => ?_, fun a b hab he => ?_⟩, hcone⟩
  · exact congrArg Subtype.val (hH.1 a)
  · exact congrArg Subtype.val (hH.2 a b hab he)
