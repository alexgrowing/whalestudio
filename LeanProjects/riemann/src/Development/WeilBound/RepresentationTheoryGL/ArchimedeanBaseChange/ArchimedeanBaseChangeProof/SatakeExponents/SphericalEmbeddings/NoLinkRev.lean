import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ValuationDetKO
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.IsSmoothCharUnr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL ValuativeRel MeasureTheory
open GlobalTheory.TypeTwo.PowIrrProof

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prin_irr (χ : Fin 2 → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (h1 : χ 1 ≠ χ 0 * absPow k 1) (h2 : χ 0 ≠ χ 1 * absPow k 1) : (prinSeries χ).IsIrreducible := by
  let x : Fin 2 → IrrGL k := fun i => IrrGL.ofChar (χ i) (hχ i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = 2 := by simp [x, IrrGL.ofChar]
  have hnu : ∀ i j, χ j ≠ χ i * absPow k 1 → x j ≠ (x i).nu 1 := fun i j h e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h e
  have hnl : ∀ i j, ¬ (Segment.single (x i) (hx i)).Linked (Segment.single (x j) (hx j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Segment.not_linked_self _
    · exact GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx 0) (hx 1) (hnu 0 1 h1) (hnu 1 0 h2)
    · exact GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx 1) (hx 0) (hnu 1 0 h2) (hnu 0 1 h1)
    · exact Segment.not_linked_self _
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k 2 2 (fun i => Segment.single (x i) (hx i)) x hd hnl
      (fun i => (single_spec (hx i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin 2) fun _ => Fin 1)
    (stdBlocks (fun i => (x i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (χ i))
  let q := multiProdEquiv (stdBlocks (fun i => (x i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (χ i) (hχ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin 2) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI := nontrivial_of_isSubquotient
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin 2) fun _ => Fin 1) χ)
  obtain ⟨e⟩ := equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k 2 χ) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv e hM

theorem iP_sph {n : ℕ} (ξ : Fin n → ℂˣ) : IsSpherical (iP (k := k) ξ) := by
  obtain ⟨f, hf, hf0⟩ := Pee.exists_sph (k := k) n ξ
  exact (Submodule.ne_bot_iff _).2 ⟨f, hf, hf0⟩

theorem no_link_rev (a b : ℂˣ) (hab : ‖(a : ℂ)‖ ≤ ‖(b : ℂ)‖) : unrChar k b ≠ unrChar k a * absPow k 1 := by
  intro e
  have e' : Pus.cls (k := k) b = (Pus.cls (k := k) a).nu ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    exact e
  exact absurd hab (not_le.2 (Pus.norm_lt_of_nu (k := k) one_pos e'))

theorem irr2 (a b : ℂˣ) (h1 : unrChar k b ≠ unrChar k a * absPow k 1) (h2 : unrChar k a ≠ unrChar k b * absPow k 1) :
    (iP (k := k) ![a, b]).IsIrreducible :=
  prin_irr (fun i => unrChar k (![a, b] i)) (fun _ => Pus.isSmoothChar_unr _) h1 h2

theorem swap_param (a b : ℂˣ) : (![a, b] ∘ Equiv.swap (0 : Fin 2) 1) = ![b, a] := by
  funext i; fin_cases i <;> simp

theorem iso2 (a b : ℂˣ) (hI1 : (iP (k := k) ![a, b]).IsIrreducible) (hI2 : (iP (k := k) ![b, a]).IsIrreducible) :
    Nonempty ((iP (k := k) ![a, b]).Equiv (iP (k := k) ![b, a])) := by
  borelize (GL (Fin 2) k)
  have hA := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ![a, b] (IsSubquotient.refl _)
    (μ := Measure.haar)
  have hB := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ![b, a] (IsSubquotient.refl _)
    (μ := Measure.haar)
  have hA' := GroundTheory.Automorphic.Spherical.isSatakeParameter_comp hA (Equiv.swap (0 : Fin 2) 1)
  rw [swap_param] at hA'
  haveI := hI1
  haveI := hI2
  exact GroundTheory.Automorphic.Spherical.nonempty_equiv_of_isSatakeParameter (fun v => isSmooth_parInd _ _ v)
    (fun v => isSmooth_parInd _ _ v)
    ((GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors _).1 (iP_sph ![a, b]))
    ((GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors _).1 (iP_sph ![b, a])) hA' hB

theorem unl (a b : ℂˣ) (h : unrChar k a ≠ unrChar k b * absPow k 1) (hab : ‖(a : ℂ)‖ ≤ ‖(b : ℂ)‖) :
    ∃ T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a]), KInj k T := by
  have h' := no_link_rev (k := k) a b hab
  obtain ⟨e⟩ := iso2 a b (irr2 a b h' h) (irr2 b a h h')
  refine ⟨e.toIntertwiningMap, fun v _ hv => ?_⟩
  exact e.toLinearEquiv.injective (hv.trans (map_zero _).symm)

end PositivityTheory.Rg.BcB.N3.Pse

end
