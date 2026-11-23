import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiIntComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.XiBound

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {l : O} (hl : l ∈ IsLocalRing.maximalIdeal O) (z : K) :
    ∃ (n : ℕ) (o : O), algebraMap O K o = algebraMap O K (l ^ n) * z := by
  by_cases h0 : l = 0
  · exact ⟨1, 0, by simp [h0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
  have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw
    exact (IsLocalRing.mem_maximalIdeal _).1 hl (hw ▸ w.isUnit)
  have hdvd : (d : O) ∣ l ^ k := by
    rw [hv, hw, mul_pow, ← pow_mul]
    exact mul_dvd_mul (Units.isUnit v).dvd (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero he)))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨k, a * t, ?_⟩
  simp only at hz
  rw [ht, map_mul, map_mul, ← hz]
  ring

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  intro hA hR hI D X E Y hF hP i hi j b s h P hd
  classical
  obtain ⟨u, c, hu, hK⟩ := GlobalTheory.XiIntComb.xi_int_comb hA hR hI D X E Y hF hP i hi j b s h P hd
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hFa : Faithful (Y.Z.rd i j b) :=
    realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
      hν X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  have hinj := hFa.injective
  set lam : ℂ := (Y.Z.ν i j b)⁻¹ * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) with hlam

  have step : ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x,
      Y.Z.rd i j b x = Y.Z.ρ.xi i j b D.nexp Q M h P a →
      ∃ x' ∈ D.nexp.Bsup i ((j : ℕ) + 1) b, Y.Z.rd i j b x' = lam • Y.Z.rd i j b x := by
    intro Q M hQ hs a x hx
    obtain ⟨n, o, m, hm, he⟩ := hK Q M hQ hs a
    let y : NX.Fm Y.S i ((j : ℕ) + 1) b :=
      ∑ k, ((show NX.KB Y.S i b from algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) :
        NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1))
    have hy : y ∈ NX.Bsup Y.S i ((j : ℕ) + 1) b := by
      refine Submodule.sum_mem _ fun k _ => ?_
      exact (NX.Bsup Y.S i ((j : ℕ) + 1) b).smul_mem (o k) (Submodule.subset_span ⟨m k, hm k, rfl⟩)
    have hey : evK Y.YS X.geo.v₀ Y.Z.good i j b y = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
      refine (map_sum (evK Y.YS X.geo.v₀ Y.Z.good i j b) (fun k => ((show NX.KB Y.S i b from algebraMap (D.ntw.O i)
        (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) : NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1)))
        Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [TensorProduct.smul_tmul', evK_tmul, smul_eq_mul, mul_one]
      rfl
    let x' := (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y
    refine ⟨x', (Y.sup i _ b (Nat.le_add_left _ _) j.2 x').2 (by simp only [x', LinearEquiv.apply_symm_apply]; exact hy), ?_⟩
    change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x') = _
    rw [show Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x' = y from LinearEquiv.apply_symm_apply _ _, hey, ← he, hx, hlam,
      smul_smul]
  by_cases hex : ∃ μ : FractionRing (D.ntw.O i), Y.Z.ρ.e i b μ = lam
  · obtain ⟨μ, hμ⟩ := hex
    obtain ⟨N, o, ho⟩ := exists_pow_mul_mem (K := FractionRing (D.ntw.O i)) (D.ntw.O_l i) μ⁻¹
    refine ⟨N, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', hx'B, hx'⟩ := step Q M hQ hs a x hx
    have hμx : x' = μ • x := hinj (by rw [hx', map_smulₛₗ, hμ])
    by_cases hμ0 : μ = 0
    · exfalso
      rw [hμ0, map_zero, hlam] at hμ
      have hl : ((D.ntw.l i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero
      exact mul_ne_zero (inv_ne_zero hν) (mul_ne_zero (pow_ne_zero _ hl) hu) hμ.symm
    have : ((D.ntw.l i : D.ntw.O i) ^ N) • x = o • x' := by
      rw [hμx, ← algebraMap_smul (FractionRing (D.ntw.O i)) o, ← algebraMap_smul (FractionRing (D.ntw.O i)) ((D.ntw.l i : D.ntw.O i) ^ N),
        smul_smul, ho, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hx'B
  · refine ⟨0, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', -, hx'⟩ := step Q M hQ hs a x hx
    by_cases h0 : Y.Z.rd i j b x = 0
    · rw [hinj (h0.trans (map_zero _).symm), smul_zero]
      exact Submodule.zero_mem _
    · exact absurd (hFa.mem_range_of_smul h0 ⟨x, rfl⟩ ⟨x', hx'⟩) hex

end GlobalTheory.XiBound
