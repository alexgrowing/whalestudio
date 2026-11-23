import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem roots_prod_X_sub_C {n : ℕ} (k : Fin n → ℂ) :
    (∏ a, (Polynomial.X - Polynomial.C (k a))).roots = Multiset.map k Finset.univ.val := by
  have hprod : (∏ a, (Polynomial.X - Polynomial.C (k a))) =
      ((Multiset.map k Finset.univ.val).map fun x => Polynomial.X - Polynomial.C x).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

theorem exists_perm_of_capelliPolynomial_eq {n : ℕ} (f g : Fin n → ℂ)
    (h : ∀ Y, Formalism.QuantumDeterminants.capP f Y = Formalism.QuantumDeterminants.capP g Y) :
    ∃ τ : Equiv.Perm (Fin n), ∀ a, f a = g (τ a) := by
  classical
  have hp : (∏ a, (Polynomial.X - Polynomial.C (-f a))) = ∏ a, (Polynomial.X - Polynomial.C (-g a)) := by
    apply Polynomial.funext
    intro Y
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    exact h Y
  have hmap : Multiset.map (fun a => -f a) Finset.univ.val = Multiset.map (fun a => -g a) Finset.univ.val := by
    rw [← roots_prod_X_sub_C (fun a => -f a), ← roots_prod_X_sub_C (fun a => -g a)]
    exact congrArg Polynomial.roots hp
  have hcard : ∀ c : ℂ, Fintype.card {a // -f a = c} = Fintype.card {a // -g a = c} := by
    intro c
    have hc := congrArg (Multiset.count c) hmap
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card, Finset.filter_val,
      Finset.filter_val]
    convert hc using 3 <;> simp [eq_comm]
  let e : ∀ c, {a // -f a = c} ≃ {a // -g a = c} := fun c => Fintype.equivOfCardEq (hcard c)
  let τ : Equiv.Perm (Fin n) :=
    ((Equiv.sigmaFiberEquiv (fun a => -f a)).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv (fun a => -g a))
  refine ⟨τ, fun a => ?_⟩
  have key : -g (τ a) = -f a := (e (-f a) ⟨a, rfl⟩).2
  exact neg_inj.mp key.symm

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
