import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValue
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightEstimate
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed

private theorem norm_le_one_of_isIntegral_int' {q : ℕ} [Fact q.Prime]
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (z : K₀) (hz : IsIntegral ℤ_[q] z) :
    ‖(z : PadicAlgCl q)‖ ≤ 1 := by
  obtain ⟨g, hmo, hg⟩ := hz
  have hc : ∀ a : ℤ_[q], ‖((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) a‖ ≤ 1 := by
    intro a
    have h1 : ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) a
        = algebraMap ℚ_[q] (PadicAlgCl q) (a : ℚ_[q]) := rfl
    rw [h1, PadicAlgCl.norm_extends]
    exact a.2
  have hg' : Polynomial.eval₂ ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀))
      (z : PadicAlgCl q) g = 0 := by
    have h := congrArg (fun w => (K₀.val : K₀ →+* PadicAlgCl q) w) hg
    simp only [Polynomial.hom_eval₂, map_zero] at h
    exact h
  by_contra hlt
  push_neg at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hmo.coeff_natDegree, map_one,
    one_mul] at hg'
  have hn : g.natDegree ≠ 0 := by
    intro h0
    rw [h0, Finset.sum_range_zero, pow_zero, zero_add] at hg'
    exact one_ne_zero hg'
  have hsum : ‖∑ i ∈ Finset.range g.natDegree,
      ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) (g.coeff i) * (z : PadicAlgCl q) ^ i‖
      ≤ ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ g.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc _ ≤ 1 * ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) :=
          mul_le_mul (hc _) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have hyn : (z : PadicAlgCl q) ^ g.natDegree = -∑ i ∈ Finset.range g.natDegree,
      ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) (g.coeff i) * (z : PadicAlgCl q) ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hg'
  have h1 : ‖(z : PadicAlgCl q)‖ ^ g.natDegree ≤ ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) := by
    rw [← norm_pow, hyn, norm_neg]
    exact hsum
  have h2 : ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) < ‖(z : PadicAlgCl q)‖ ^ g.natDegree :=
    pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem exists_isometric_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (p : ℕ) [Fact p.Prime], OverLa la T.V io e₀ → T.FinRes → (p : 𝓞 c.F) ∈ la.asIdeal → ∃ ι : T.Fr →+* PadicAlgCl p, ∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x := by
  intro E _ _ _ H l c la T io e₀ p _ hOver hFin hp
  haveI : Finite (IsLocalRing.ResidueField T.V) := hFin
  obtain ⟨q, hq, K₀, eK, eV, hfin, he⟩ := GlobalTheory.exists_ringEquiv_integralClosure_padicInt T.V T.Fr
  let ι : T.Fr →+* PadicAlgCl q := (K₀.val : K₀ →+* PadicAlgCl q).comp eK.toRingHom
  have hιapp : ∀ x, ι x = ((eK x : K₀) : PadicAlgCl q) := fun x => rfl
  have hV : ∀ v : T.V, ‖ι (algebraMap T.V T.Fr v)‖ ≤ 1 := by
    intro v
    rw [hιapp, he v]
    exact norm_le_one_of_isIntegral_int' K₀ _ (eV v).2
  have hram : 0 < ramOverZ la := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ram_pos hp
  have he0 : 0 < e₀ := (show 0 < e₀ ∧ _ from hOver).1
  obtain ⟨hmul, hone, hpos, hrange⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts E H l c p la T e₀ he0 hram
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0r : (p : ℝ) ≠ 0 := by positivity
  have hN : (0 : ℝ) < (e₀ : ℝ) * (ramOverZ la : ℝ) :=
    mul_pos (Nat.cast_pos.mpr he0) (Nat.cast_pos.mpr hram)
  have hpF : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (p : T.Fr) = (p : ℝ)⁻¹ := by
    have h := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.absT_natCast p la T io e₀ hp hOver
    rwa [map_natCast] at h
  have hpF0 : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (algebraMap T.V T.Fr ↑u⁻¹) ≤ 1 :=
      (hrange _).mpr ⟨_, rfl⟩
    have h2 : algebraMap T.V T.Fr ↑u⁻¹ * (p : T.Fr) = 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr) p, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h3 := hmul (algebraMap T.V T.Fr ↑u⁻¹) (p : T.Fr)
    rw [h2, hone, hpF] at h3
    have h4 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have h5 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    have h6 := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.absT_nonneg p la T e₀ (algebraMap T.V T.Fr ↑u⁻¹)
    nlinarith
  have hqN : ‖ι (q : T.Fr)‖ = (q : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) q, PadicAlgCl.norm_extends,
      Padic.norm_p]
  have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 := hV ↑u⁻¹
    have h2 : ι (algebraMap T.V T.Fr ↑u⁻¹) * ι (q : T.Fr) = 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr) q, ← hu, ← map_mul ι, ← map_mul (algebraMap T.V T.Fr),
        Units.inv_mul, map_one, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hqN] at h3
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    have h4 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have h5 : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
    have h6 := norm_nonneg (ι (algebraMap T.V T.Fr ↑u⁻¹))
    nlinarith
  have hqp : p = q := by
    by_contra hne
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq.out (Fact.out)).mpr (Ne.symm hne)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      have h := congrArg (Int.cast : ℤ → T.V) hab
      push_cast at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  subst hqp
  have hpN : ‖ι (p : T.Fr)‖ = (p : ℝ)⁻¹ := hqN
  have hpowA : ∀ (y : T.Fr) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (y ^ n)
      = GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ y ^ n := by
    intro y n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hpinv : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (p : T.Fr)⁻¹ = p := by
    have h := hmul (p : T.Fr) (p : T.Fr)⁻¹
    rw [mul_inv_cancel₀ hpF0, hone, hpF, eq_comm, inv_mul_eq_one₀ hp0r] at h
    exact h.symm
  have hiff : ∀ x : T.Fr, ‖ι x‖ ≤ 1 ↔ GlobalTheory.GoodPts.InV T x := by
    intro x
    constructor
    · intro hx
      by_contra hxV
      have hxV' : x ∉ (algebraMap T.V T.Fr).range := hxV
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hxV' ⟨0, map_zero _⟩
      have hA : 1 < GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x :=
        lt_of_not_ge (fun h => hxV' ((hrange x).mp h))
      have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
      have hAy : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ < 1 := by
        have h := hmul x x⁻¹
        rw [mul_inv_cancel₀ hx0, hone] at h
        have := hpos _ hy0
        nlinarith
      have hk : (1 : ℝ) ≤ (vV T.V x⁻¹ : ℝ) := by
        have h := hAy
        simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hy0] at h
        by_contra hlt
        push_neg at hlt
        have hk0 : vV T.V x⁻¹ ≤ 0 := by
          have : vV T.V x⁻¹ < 1 := by exact_mod_cast hlt
          omega
        have hk0' : (vV T.V x⁻¹ : ℝ) ≤ 0 := by exact_mod_cast hk0
        have hexp : 0 ≤ -((vV T.V x⁻¹ : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) := by
          have := div_nonpos_iff.mpr (Or.inr ⟨hk0', hN.le⟩)
          linarith
        have := Real.one_le_rpow hp1.le hexp
        linarith
      have hAN : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ ^ (e₀ * ramOverZ la) ≤ (p : ℝ)⁻¹ := by
        simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hy0]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le hp1.le
        have : -((vV T.V x⁻¹ : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * ((e₀ * ramOverZ la : ℕ) : ℝ)
            = -(vV T.V x⁻¹ : ℝ) := by
          push_cast
          field_simp
        rw [this]
        linarith
      have hz_mem : x⁻¹ ^ (e₀ * ramOverZ la) * (p : T.Fr)⁻¹ ∈ (algebraMap T.V T.Fr).range := by
        apply (hrange _).mp
        rw [hmul, hpowA, hpinv]
        calc GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ ^ (e₀ * ramOverZ la) * (p : ℝ)
            ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_right hAN (by positivity)
          _ = 1 := inv_mul_cancel₀ hp0r
      obtain ⟨w, hw⟩ := hz_mem
      have h1 := hV w
      rw [hw, map_mul, map_pow, map_inv₀, map_inv₀, norm_mul, norm_pow, norm_inv, norm_inv, hpN,
        inv_inv] at h1
      have hxpos : 0 < ‖ι x‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hx0)
      have h2 : 1 ≤ ‖ι x‖⁻¹ := (one_le_inv₀ hxpos).mpr hx
      have h4 : 1 ≤ ‖ι x‖⁻¹ ^ (e₀ * ramOverZ la) := one_le_pow₀ h2
      have h5 : 1 * (p : ℝ) ≤ ‖ι x‖⁻¹ ^ (e₀ * ramOverZ la) * p :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    · rintro ⟨v, rfl⟩
      exact hV v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hz := GlobalTheory.GeoTie.ReadExt.norm_eq_zpow T ι hiff hπ
  have hvp : (vV T.V (p : T.Fr) : ℝ) = (e₀ : ℝ) * (ramOverZ la : ℝ) := by
    have h := hpF
    simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hpF0] at h
    have h2 := congrArg Real.log h
    rw [Real.log_rpow (by positivity), Real.log_inv] at h2
    have hlog : 0 < Real.log p := Real.log_pos hp1
    have h3 : (vV T.V (p : T.Fr) : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ)) = 1 := by
      have h4 : ((vV T.V (p : T.Fr) : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * Real.log p
          = 1 * Real.log p := by linarith
      exact mul_right_cancel₀ hlog.ne' h4
    rwa [div_eq_one_iff_eq hN.ne'] at h3
  have hvpZ : vV T.V (p : T.Fr) = ((e₀ * ramOverZ la : ℕ) : ℤ) := by
    have : (vV T.V (p : T.Fr) : ℝ) = (((e₀ * ramOverZ la : ℕ) : ℤ) : ℝ) := by
      rw [hvp]
      push_cast
      ring
    exact_mod_cast this
  have hrp : ‖ι (algebraMap T.V T.Fr π)‖ ^ (e₀ * ramOverZ la) = (p : ℝ)⁻¹ := by
    rw [← zpow_natCast, ← hvpZ, ← hz _ hpF0, hpN]
  have hNne : e₀ * ramOverZ la ≠ 0 := (Nat.mul_pos he0 hram).ne'
  have hrval : ‖ι (algebraMap T.V T.Fr π)‖ = (p : ℝ) ^ (-(1 / ((e₀ : ℝ) * (ramOverZ la : ℝ)))) := by
    refine (pow_left_inj₀ (n := e₀ * ramOverZ la) (norm_nonneg _) (by positivity) hNne).mp ?_
    rw [hrp, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : -(1 / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * ((e₀ * ramOverZ la : ℕ) : ℝ) = -1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨ι, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT]
  · rw [hz x hx, hrval]
    simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hx]
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed
