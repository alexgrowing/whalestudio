import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem loc_one_of' {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem eq_of_ae {L : Type} [Field L] [NumberField L] (a b : HChar L)
    (h : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, a.UnrAt u ∧ b.UnrAt u ∧ a.val u = b.val u) : a = b := by
  let ρ : HChar L := a * b⁻¹
  have hl : ∀ u x, ρ.loc u x = a.loc u x * (b.loc u x)⁻¹ := fun _ _ => rfl
  have hev : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ρ.UnrAt u ∧ ρ.val u = 1 := by
    filter_upwards [h] with u hu
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hl, hu.1 x hx, hu.2.1 x hx]; simp
    · have e : ρ.val u = a.val u * (b.val u)⁻¹ := rfl
      rw [e, hu.2.2, mul_inv_cancel]
  have h1 : ρ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ρ.1 ρ.2.1 ρ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of' ρ w this.1 this.2 y
  have h2 : ρ = 1 := Subtype.ext h1
  exact mul_inv_eq_one.1 h2

theorem UpperTheory.Gal.GamX.rkLiftOf :
    UpperTheory.Gal.GamX.RkLiftOf := by
  unfold RkLiftOf RkLift
  intro hN K L _ _ _ _ _ _ _ ψ ψ' hW v w
  obtain ⟨ξ, hξ⟩ := hN K L ψ
  suffices e : ψ' = ξ by rw [e]; exact (hξ v w).1
  refine eq_of_ae _ _ ?_
  filter_upwards [hW, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ')] with u h1 h2 h3
  have h2' : ψ.UnrAt (u.under (𝓞 K)) := h2
  have h3' : ψ'.UnrAt u := h3
  have hl : u.asIdeal.LiesOver (u.under (𝓞 K)).asIdeal := ⟨rfl⟩
  obtain ⟨-, hu, d⟩ := hξ (u.under (𝓞 K)) ⟨u, hl⟩
  obtain ⟨b, c⟩ := hu h2'
  have hnv : ∀ {F : Type} [Field F] [NumberField F] (x : HeightOneSpectrum (𝓞 F)), normV x = Ideal.absNorm x.asIdeal :=
    fun x => by rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hf : normV u = normV (u.under (𝓞 K)) ^ fdeg (⟨u, hl⟩ : PlacesOver L (u.under (𝓞 K))) := by
    rw [hnv, hnv]; exact d
  obtain ⟨B, hB, hB'⟩ := h1 _ hf
  obtain rfl := CG.HasSat.unique hB (CG.hasSat_ofChar h2')
  have e := CG.HasSat.unique hB' (CG.hasSat_ofChar h3')
  rw [Multiset.map_singleton, Multiset.singleton_inj] at e
  exact ⟨h3', b, e.symm.trans c.symm⟩
