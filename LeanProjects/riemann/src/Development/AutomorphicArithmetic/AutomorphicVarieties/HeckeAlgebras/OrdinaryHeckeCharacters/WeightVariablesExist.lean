import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem weight_variables_exist (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ)
    (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, W.LocAb l (F.Gv v) (F.Iv v) (d v)) (Λ : LamObj r) (D : ℕ)
    (hD : ∑ v, d v = D) :
    ∃ (v : Fin (n * D) → F.Vl) (i : Fin (n * D) → Fin n) (γ : ∀ k, F.Gv (v k)) (c : Fin (n * D) → O)
      (e : MvPowerSeries (Empty ⊕ Fin (n * D)) O ≃ₐ[O] Λ.Λ), ∀ k, ∃ hγ : γ k ∈ F.Iv (v k),
      residue O (c k) * (r.psib (v k) (i k) (γ k) : ResidueField O) = 1 ∧
      e (MvPowerSeries.X (.inr k)) = algebraMap O Λ.Λ (c k) * (Λ.κ (v k) (i k) ⟨γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  obtain ⟨e, ψ₀, hψ₀, he⟩ := (W.lam_ex_free l F O n r d A).2 Λ
  have hc : Fintype.card (Σ v : F.Vl, Fin n × Fin (d v)) = n * D := by
    rw [Fintype.card_sigma, ← hD, Finset.mul_sum]
    simp
  let ε : Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) := (Fintype.equivFinOfCardEq hc).symm
  choose g hgI hg using fun (v : F.Vl) (j : Fin (d v)) => ((A v).inertia (Pi.single j 1, 0)).2 rfl
  let ε' : Empty ⊕ Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) :=
    (@Equiv.emptySum Empty (Fin (n * D)) ⟨Empty.elim⟩).trans ε
  refine ⟨fun k => (ε k).1, fun k => (ε k).2.1, fun k => g (ε k).1 (ε k).2.2,
    fun k => ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ),
    (MvPowerSeries.renameEquiv O ε').trans e, fun k => ⟨hgI _ _, ?_, ?_⟩⟩
  · have h1 := (hψ₀ (ε k).1 (ε k).2.1).red (g (ε k).1 (ε k).2.2)
    have h2 : ∀ x : O, Alg.res O O x = residue O x := fun x => (Alg.res O O).commutes x
    rw [h2] at h1
    show residue O _ * ((r.psib (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2) : (ResidueField O)ˣ) : ResidueField O) = 1
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  · have h1 := he (ε k).1 (ε k).2.1 (ε k).2.2 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ (hg _ _)
    have h2 : MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (ε k) := by
      exact MvPowerSeries.rename_X _ _
    show e (MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k))) =
      algebraMap O Λ.Λ ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ) *
        ((Λ.κ (ε k).1 (ε k).2.1 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ : Λ.Λˣ) : Λ.Λ) - 1
    rw [h1, h2, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, add_sub_cancel_left]

theorem UpperTheory.V.Hi.levelUR2WtVars :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r), Pa.LocCFT s → ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] Λ.Λ), ∀ k, ∃ hγ : wt.γ k ∈ V.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O Λ.Λ (wt.c k) * (Λ.κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  intro l hl L Ω _ _ _ _ _ _ s n V c r _ Λ h
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h
  let d : V.frame.Vl → ℕ := d₀
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  obtain ⟨v, i, γ, cc, e, H⟩ := weight_variables_exist l V.frame c.O n r d (fun v => (hA v).some) Λ _ hsum
  exact ⟨⟨v, i, γ, cc⟩, e, H⟩
