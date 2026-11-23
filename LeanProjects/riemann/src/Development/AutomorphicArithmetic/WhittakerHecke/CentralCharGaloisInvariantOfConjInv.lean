import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
open NumberField IsDedekindDomain GroundTheory.Global Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.LocalScalarValues

open GroundTheory.Global.AdeleBaseChange GlobalTheory.Mem.LocTriv

variable {E : Type} [Field E] [NumberField E]

private theorem loc_eq_val (ψ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (hu : ψ.UnrAt w)
    (y : (w.adicCompletion E)ˣ) (hy : IsUnifAt w y) : ψ.loc w y = ψ.val w := by
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

private theorem smul_local (c : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    ∃ x' : ((c • w).adicCompletion E)ˣ, Valued.v (x' : (c • w).adicCompletion E) = Valued.v (x : w.adicCompletion E) ∧
      c • (Neutral.B1.localIdele E w x : IdeleGroup E) = Neutral.B1.localIdele E (c • w) x' := by
  have hs : ∀ u, ((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 u =
      finiteCompletionMap (c : E ≃+* E) u (ev (comapPrime (c : E ≃+* E) u) (Neutral.B1.localIdele E w x : AdeleRing (𝓞 E) E)) :=
    fun u => smul_snd c _ u
  refine ⟨Units.map (ev (c • w)) (c • (Neutral.B1.localIdele E w x : IdeleGroup E)), ?_,
    Units.ext (Prod.ext ?_ (Subtype.ext (funext fun u => ?_)))⟩
  · change Valued.v (((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 (c • w)) = _
    rw [hs, valued_finiteCompletionMap, comapPrime_eq_inv_smul, inv_smul_smul, ev_local_self]
  · funext u
    change (c • ((Neutral.B1.localIdele E w x : IdeleGroup E) : AdeleRing (𝓞 E) E)).1 u = 1
    rw [smul_fst]
    exact map_one _
  · change ((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 u =
      ev u (Neutral.B1.localIdele E (c • w) _ : AdeleRing (𝓞 E) E)
    by_cases hu : u = c • w
    · subst hu
      rw [ev_local_self]
      rfl
    · have h1 : comapPrime (c : E ≃+* E) u ≠ w := by
        rw [comapPrime_eq_inv_smul]
        rintro rfl
        exact hu (smul_inv_smul c u).symm
      rw [ev_local_ne hu, hs, ev_local_ne h1]
      exact map_one _

end UpperTheory.LocalScalarValues

open UpperTheory.LocalScalarValues in
theorem UpperTheory.centralChar_galois_invariant_of_conjInv :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar E), P.HasCentChar ω → ConjInv P → ∀ (c : E ≃ₐ[ℚ] E) (z : IdeleGroup E), ω.1 (c • z) = ω.1 z := by
  intro E _ _ _ P ω hω hc c z
  let ψ : Neutral.B1.Ideles E →* ℂˣ :=
    { toFun := fun a => ω.1 (c • (a : IdeleGroup E)) * (ω.1 a)⁻¹
      map_one' := by
        rw [smul_one, map_one, inv_one, mul_one]
      map_mul' := fun a b => by
        rw [smul_mul', map_mul, map_mul, mul_inv, mul_mul_mul_comm] }
  have hψ : ∀ a, ψ a = ω.1 (c • (a : IdeleGroup E)) * (ω.1 a)⁻¹ := fun _ => rfl
  have hcont : Continuous ψ :=
    (ω.2.1.comp (continuous_const_smul c)).mul ω.2.1.inv
  have hd : ∀ k, ψ (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have e : ∀ k : Eˣ, (Neutral.B1.diagUnits E k : IdeleGroup E) = IdeleGroup.diagonal E k := fun _ => Units.ext rfl
    have e2 : ∀ k : Eˣ, ω.1 (IdeleGroup.diagonal E k) = 1 := fun k => (congrArg ω.1 (e k)).symm.trans (ω.2.2 k)
    rw [hψ, e, smul_diagonal, e2, e2, inv_one, mul_one]
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ω.UnrAt w ∧ ω.UnrAt (c • w) ∧
      ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
        ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B := by
    have h1 := Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)
    have h2 := (MulAction.injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2, hc] with w a b d using ⟨a, b, d⟩
  have h1 : ψ = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ hcont hd (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have hw' := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      obtain ⟨hu, hu', hs⟩ := hw'
      refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.comp (Neutral.B1.localIdele E w)) (fun x hx => ?_) y
      obtain ⟨x', hv, he⟩ := smul_local c w x
      obtain ⟨B, hB, hB'⟩ := hs (c • w) (HeightOneSpectrum.ext (Ideal.under_smul (𝓞 ℚ) w.asIdeal c))
      have e1 : ω.1 (Neutral.B1.localIdele E w x) = B.prod :=
        (loc_eq_val ω w hu x hx).trans (PositivityTheory.jumpWindows.PSmo.val_eq_prod hω hB)
      have e2 : ω.1 (Neutral.B1.localIdele E (c • w) x') = B.prod :=
        (loc_eq_val ω (c • w) hu' x' (hv.trans hx)).trans (PositivityTheory.jumpWindows.PSmo.val_eq_prod hω hB')
      rw [MonoidHom.comp_apply, hψ, he, e1, e2, mul_inv_cancel]
  have h2 : ψ z = 1 := by rw [h1]; rfl
  rw [hψ, mul_inv_eq_one] at h2
  exact h2
