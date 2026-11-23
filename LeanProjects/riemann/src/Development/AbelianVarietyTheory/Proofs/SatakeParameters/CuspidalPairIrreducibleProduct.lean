import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningOfCentralFiltrationStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCellsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SwapTwo

open GlobalTheory.JacTensor GlobalTheory.EmptyFirstBlock

theorem nonempty_equiv_of_apply_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) {v : V} (hv : f v ≠ 0) : Nonempty (ρ.Equiv σ) := by
  let K : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g x hx => by
    show f (ρ g x) = 0
    rw [f.isIntertwining]
    have hx' : f x = 0 := hx
    rw [hx', map_zero]⟩
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, f.isIntertwining _ _ g x⟩⟩
  refine ⟨GlobalTheory.LocGL.equivOfBijective f ⟨?_, ?_⟩⟩
  · rcases eq_bot_or_eq_top K with h | h
    · refine (injective_iff_map_eq_zero f.toLinearMap).2 fun x hx => ?_
      have : x ∈ K := hx
      rw [h] at this
      exact this
    · exact absurd (show v ∈ K from h ▸ trivial) hv
  · rcases eq_bot_or_eq_top R with h | h
    · exact absurd (show f v ∈ R from ⟨v, rfl⟩) (by rw [h]; exact hv)
    · intro w
      obtain ⟨x, hx⟩ := (show w ∈ R from h ▸ trivial)
      exact ⟨x, hx⟩

theorem exists_jac_map_ne_zero : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)),
    (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n),
    ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')), φ x ≠ 0 := by
  intro _ hGL k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  obtain ⟨z, c, c', hz, hcc, hX, hbad⟩ := GlobalTheory.T.exists_central_scalar_distinct_geometricLemma_cells k d σ hσ hd1 hnt
  obtain ⟨N, b, hb⟩ := (hGL k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![1, 0]] := ⟨⟨![![0, d 0], ![1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two, hd1]
      · fin_cases j <;> simp [Fin.sum_univ_two, hd1]⟩, rfl⟩
  have hgood : (b (b.symm G0)).1 1 0 = 1 := by rw [Equiv.apply_symm_apply, hG0]; rfl
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv k d σ hd1 (b (b.symm G0)) hgood
  have hbad' : ∀ t, t ≠ b.symm G0 → (b t).1 1 0 = 0 := by
    intro t ht
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    by_contra hne
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  have hstep : ∀ t, t ≠ b.symm G0 → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y := by
    intro t ht y
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    apply E.toLinearEquiv.injective
    have h1 : E.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) z y) = _ := LinearMap.congr_fun (E.isIntertwining' z) y
    have h2 := hbad (b t) (hbad' t ht) (b t).nonempty_rows.some (b t).nonempty_cols.some (E.toLinearEquiv y)
    exact h1.trans (h2.trans (LinearEquiv.map_smul E.toLinearEquiv c' y).symm)
  obtain ⟨φ, v, hv⟩ := GlobalTheory.T.exists_intertwining_of_central_filtration_step (jac e' (multiProd e fun i => (σ i).π))
    (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) N S hmono h0 hN z hz (b.symm G0) c (fun _ => c')
    (fun _ _ => hcc.symm) hstep
    ⟨(h4 (b.symm G0) f₀ g₀).some.trans E₀⟩ hX
    (GlobalTheory.ProdSupport.nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr)
  exact ⟨φ, v, hv⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_of_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (φ : G →* H) (h : Representation.IsIrreducible (ρ.comp φ)) :
    ρ.IsIrreducible := by
  haveI : Nontrivial V := Model.nontrivial_of_isIrreducible h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact hv h1
  · rcases eq_bot_or_eq_top (⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩ :
        Subrepresentation (ρ.comp φ)) with h' | h'
    · left
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2
    · right
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2

theorem not_equiv_twist_symm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (π₁ : Irr k r) (π₂ : Irr k t),
    (∀ (h : r = t) (α : ℂˣ), ¬ Nonempty ((h ▸ π₁ : Irr k t).π.Equiv (twist π₂.π (detChar (Fin t) (unrChar k α))))) →
    ∀ (h : t = r) (α : ℂˣ), ¬ Nonempty ((h ▸ π₂ : Irr k r).π.Equiv (twist π₁.π (detChar (Fin r) (unrChar k α)))) := by
  intro k _ _ _ _ r t π₁ π₂ hnt h α ⟨φ⟩
  subst h
  refine hnt rfl α⁻¹ ?_
  have heq : twist (twist π₁.π (detChar (Fin t) (unrChar k α))) (detChar (Fin t) (unrChar k α⁻¹)) = π₁.π := by
    ext g v
    simp only [twist_apply, detChar_apply, unrChar_apply, smul_smul, inv_zpow]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have e := (GlobalTheory.LocGL.twistEquiv φ (detChar (Fin t) (unrChar k α⁻¹))).symm
  rw [heq] at e
  exact ⟨e⟩

theorem isIrreducible_multiProd_two (hU : GlobalTheory.Published.UnlinkedProductIrreducible) {n : Type} [Fintype n]
    [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π)
    (hnt : ∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α)))))
    (e : (Σ i, Fin (d i)) ≃ n) : (multiProd e fun i => (σ i).π).IsIrreducible := by
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  have hsupp : ∀ i, IsCuspSupport (σ i).π (fun _ : Fin 1 => d i) (fun _ => (σ i).π) := fun i => by
    obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (σ i).smooth (oneBlock (d i)) fun _ _ => rfl
    exact ⟨(σ i).irr, fun _ => ⟨(hσ i).1, (σ i).irr, (hσ i).2⟩, oneBlock (d i),
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩
  have h2 := hU k (d 0) (d 1) 1 1 (σ 0) (σ 1) _ _ _ _ (hsupp 0) (hsupp 1) fun _ _ h α => hnt h α
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (σ i).π
  have h3 := GlobalTheory.Parabolic.isIrreducible_of_equiv E₁ h2
  have hc : Fintype.card (Fin (d 0 + d 1)) = Fintype.card n := by
    rw [Fintype.card_fin, ← hd, ← Fintype.card_congr e]; simp
  let ψ : Fin (d 0 + d 1) ≃ n := Fintype.equivOfCardEq hc
  obtain ⟨E₂⟩ := GlobalTheory.T.normalisedParabolicInduction_reindex_equiv k (Fin 2) (fun i => Fin (d i)) _ _ (stdBlocks d hd) ψ _ (piTensor fun i => (σ i).π)
  have h4 := isIrreducible_of_comp _ (GlobalTheory.Parabolic.isIrreducible_of_equiv E₂ h3)
  obtain ⟨E₃⟩ := (Placing.parInd_jac_placing k (Fin 2) n (fun i => Fin (d i)) ((stdBlocks d hd).trans ψ) e _).1
    (piTensor fun i => (σ i).π)
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E₃ h4

theorem swap_two_equiv : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 → (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), Nonempty ((multiProd e fun i => (σ i).π).Equiv (multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hBZ hGL hU k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  have h1 := isIrreducible_multiProd_two hU d σ hσ hnt e
  have h2 := isIrreducible_multiProd_two hU (fun i => d (Equiv.swap 0 1 i)) (fun i => σ (Equiv.swap 0 1 i))
    (fun i => hσ _) (not_equiv_twist_symm k (d 0) (d 1) (σ 0) (σ 1) hnt) e'
  obtain ⟨φ, x, hx⟩ := exists_jac_map_ne_zero hBZ hGL k n d σ hσ hd1 hnt e e'
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.SwapTwo

end
