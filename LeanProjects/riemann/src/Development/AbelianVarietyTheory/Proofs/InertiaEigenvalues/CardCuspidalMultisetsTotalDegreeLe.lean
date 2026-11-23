import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardGenericIrreducibleCharactersGLnLeStatement
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.CuspMultisetCount

theorem degL_toList {g : ℕ} [Fact g.Prime] (M : Multiset (Pc g)) :
    degL M.toList = (M.map fun p => p.1).sum := by
  unfold degL
  conv_rhs => rw [← Multiset.coe_toList M]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem stdAddChar_ne_one (g : ℕ) [Fact g.Prime] : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) ≠ 1 := by
  intro h
  have h1 := congrArg (fun ψ : AddChar (ZMod g) ℂ => ψ 1) h
  simp only [AddChar.one_apply] at h1
  have h0 : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) 0 = 1 := AddChar.map_zero_eq_one _
  have := ZMod.injective_stdAddChar (N := g) (h1.trans h0.symm)
  exact one_ne_zero this

theorem card_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)),
    (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  intro g _ n hn S hS
  set ψ : AddChar (ZMod g) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ ≠ 1 := stdAddChar_ne_one g
  have hdeg : ∀ M ∈ S, degL M.toList = n := fun M hM => (degL_toList M).trans (hS M hM).1
  have hcusp : ∀ M ∈ S, ∀ p ∈ M.toList, IsCusp p.2 := fun M hM p hp =>
    (hS M hM).2 p (Multiset.mem_toList.1 hp)
  have hchar : ∀ M ∈ S, IsChar (hcL M.toList n) := fun M hM =>
    (GlobalTheory.gl_list_product_perm_char g M.toList M.toList n (hdeg M hM).symm
      (fun p hp => Label.isChar_of_isIrr (hcusp M hM p hp).2.1)).1
  have key : ∀ M ∈ S, ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL M.toList n) ≠ 0 :=
    fun M hM => GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal g ψ hψ M.toList n (hdeg M hM) (hcusp M hM)
  choose! f hf using key
  have hfin : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.Finite :=
    (GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one (Gn g n)).1.subset fun ρ h => h.1
  have hinj : Set.InjOn f (S : Set (Multiset (Pc g))) := by
    intro M hM M' hM' heq
    have h1 := (hf M hM).2.2
    have h2 := (hf M' hM').2.2
    rw [heq] at h1
    have hne := Label.ip_ne_zero_of_common (f M') _ _ (hf M' hM').1 (hchar M hM) (hchar M' hM') h1 h2
    have hp : M.toList.Perm M'.toList := by
      by_contra hnp
      exact hne ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g M.toList M'.toList n (hdeg M hM) (hdeg M' hM')
        (hcusp M hM) (hcusp M' hM')).1 hnp)
    rw [← Multiset.coe_toList M, ← Multiset.coe_toList M']
    exact Multiset.coe_eq_coe.2 hp
  calc S.card = (S : Set (Multiset (Pc g))).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.ncard :=
        Set.ncard_le_ncard_of_injOn f (fun M hM => ⟨(hf M hM).1, (hf M hM).2.1⟩) hinj hfin
    _ ≤ g ^ n - g ^ (n - 1) := GlobalTheory.T.ncard_generic_irreducible_characters_GLn_le g ψ hψ n hn

end GlobalTheory.GLq.CuspMultisetCount
