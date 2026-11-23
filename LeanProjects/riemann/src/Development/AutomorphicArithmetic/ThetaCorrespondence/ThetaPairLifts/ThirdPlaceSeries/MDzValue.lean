import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.DzValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem character_inertia_eq_of_congruent_generator [IsTotallyComplex E] (H : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h} (hl : _root_.UpperTheory.One.M.LawsM a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : GlobalTheory.GLq.LabelDatum g) (t : G E Ω) (ht : t ∈ Ine (F := E) A)
    (hT : TameCoupled A κ t L.gen) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ)
    (htm : GlobalTheory.SplitWeil.IsTame μ) (n : ℕ) (hn : n.Coprime g)
    (hgen : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (n : ZMod g) = L.gen 1) (x : (w.adicCompletion E)ˣ)
    (hx : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - (n : w.adicCompletion E)) < 1) :
    μ (a (ineIncl h ⟨t, ht⟩)) = μ x := by
  haveI : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  let u₀ : (ZMod g)ˣ := ZMod.unitOfCoprime n hn
  have hu₀ : IsUnit ((n : ℕ) : ℤ_[g]) := isUnit_of_map_unit (PadicInt.toZMod (p := g)) _ (by
    rw [map_natCast]; exact u₀.isUnit)
  obtain ⟨θ, hθ⟩ := exists_red i hi hw μ htm
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.DepthZeroModel.exists_label L θ u₀ (by rw [ZMod.coe_unitOfCoprime]; exact hgen)
  have h1 := H E Ω g A w h rc (_root_.UpperTheory.One.M.New.close hl) i hi κ L t ht hT 1 (Or.inl rfl) (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)
    (IrrGL.isCusp_ofChar μ hμ) _ P hP (inflates_units i θ μ hμ hθ)
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)) = _ := hl.one μ hμ
  rw [h2, e, WD.inePol_of_mem_Ine _ ht, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd] at h1
  have h3 := congrArg (fun p => p.coeff 0) h1
  have h4 : μ (a (ineIncl h ⟨t, ht⟩)) = θ u₀ := Units.ext (by simpa using h3)
  have h5 : u₀ = Units.map (PadicInt.toZMod (p := g)).toMonoidHom hu₀.unit := Units.ext (by simp [u₀])
  rw [h4, h5, hθ]
  set y : (w.adicCompletion E)ˣ :=
    Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hu₀.unit) with hy
  have hyn : (y : w.adicCompletion E) = n := by simp [hy]
  have hyi : valuation (w.adicCompletion E) ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
    have e4 : ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        i (((hu₀.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) := by
      rw [hy, ← map_inv, ← map_inv]; rfl
    rw [e4]; exact val_int_le i hi _
  have h6 : μ (x * y⁻¹) = 1 := htm _ (by
    have e3 : ((x * y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((x : w.adicCompletion E) - n) * ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [← hyn, sub_mul, Units.mul_inv]; simp
    rw [e3, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hyi)
  rw [map_mul, map_inv, mul_inv_eq_one] at h6
  exact h6.symm
end DiscreteGroups.sglob.DzType.Rt
end
end
