import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem finiteDimensional_Ks_one {l : ℕ} [Fact l.Prime] (K : FinExt l) (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : K0 K = K.1 := inf_eq_left.mpr hK
  have hK1 : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin : ({x : Om l | x ^ (l ^ 1) = 1}).Finite := by
    apply ((Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (pow_pos hl 1)).2 hx
  haveI : Finite ({x : Om l | x ^ (l ^ 1) = 1}) := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    refine ⟨Polynomial.X ^ (l ^ 1) - 1, Polynomial.monic_X_pow_sub_C 1 (pow_pos hl 1).ne', ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    simp only [pow_one] at hx
    simp [hx]
  unfold Ks
  rw [h0]
  infer_instance

theorem exists_caseA_enl : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q →
    D.nd.l i ≠ D.host.d → ∃ C : TruncatedSeriesCountingIdentities.CoefExt D i w hw, CaseA (D.nbr i w hw).Kw C.LL := by
  intro D i w hw hs hq hd
  have h2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hs
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i hs hq hd w hw
  haveI := finiteDimensional_Ks_one (D.nbr i w hw).Kw hur
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).LL.1 := (D.nbr i w hw).LL.2
  let N : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    IntermediateField.normalClosure ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) (Om (D.nd.l i))
  haveI hN : FiniteDimensional ℚ_[D.nd.l i] ↥N := normalClosure.is_finiteDimensional _ _ _
  let LL : FinExt (D.nd.l i) := ⟨N ⊔ (D.nbr i w hw).LL.1, inferInstance⟩
  refine ⟨⟨LL, le_sup_right⟩, hur, h2, le_rfl, fun h => absurd h h2, ?_, ?_⟩
  · have h0 : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hur
    unfold Ks
    rw [h0]
    exact le_sup_left
  · intro τ x
    apply le_sup_left (b := (D.nbr i w hw).LL.1)
    exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.UseLoc
