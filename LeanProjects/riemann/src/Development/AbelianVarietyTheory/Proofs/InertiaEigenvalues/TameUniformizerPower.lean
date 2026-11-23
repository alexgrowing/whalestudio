import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TauOneCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

theorem val_lt_of_mem {x : 𝓞 E} (hx : x ∈ w.asIdeal) :
    valuation (w.adicCompletion E) (algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  rw [adic_valued_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact hx

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi in
theorem val_int_le (z : ℤ_[g]) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) ≤ 1 :=
  (val_le_iff _).2 (GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi _ z.2)

include hi in
theorem val_int_lt (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (z : ℤ_[g]) (hz : PadicInt.toZMod z = 0) :
    valuation (w.adicCompletion E) (i (z : ℚ_[g])) < 1 := by
  have h1 : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [PadicInt.coe_mul, map_mul, map_mul, PadicInt.coe_natCast, map_natCast]
  exact mul_lt_one_of_nonneg_of_lt_one_right (val_int_le i hi c) zero_le
    ((val_lt_iff _).2 (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w g hw))

include hi in
theorem exists_red (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hT : GlobalTheory.SplitWeil.IsTame μ) :
    ∃ θ : (ZMod g)ˣ →* ℂˣ, ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      μ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z)) := by
  have hs := IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g))
    (ZMod.ringHom_surjective _) (IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _))
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  let φ : ℤ_[g]ˣ →* ℂˣ :=
    μ.comp ((Units.map i.toRingHom.toMonoidHom).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom))
  have hker : f.ker ≤ φ.ker := fun z hz => by
    rw [MonoidHom.mem_ker] at hz ⊢
    apply hT
    have h1 : PadicInt.toZMod ((z : ℤ_[g]) - 1) = 0 := by
      have e := congrArg Units.val hz
      rw [map_sub, map_one, sub_eq_zero]
      exact e
    have := val_int_lt i hi hw ((z : ℤ_[g]) - 1) h1
    simpa [φ] using this
  exact ⟨f.liftOfSurjective hs ⟨φ, hker⟩, fun z => MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hker⟩ z⟩

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem inflates_units (i : ℚ_[g] ≃+* w.adicCompletion E) (θ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ)
    (hθ : ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z))) :
    GlobalTheory.SerSys.TameGen.Inflates ((GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom))
      (GlobalTheory.Published.DepthZeroModel.tauOne θ) := by
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  have h1 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k) =
      Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.inc, RingHom.map_det]
  have h2 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.red, RingHom.map_det]
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k)) := by
    ext; simp
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, h1, h2, hθ]

theorem value_at_gen (H : GlobalTheory.Published.DepthZeroInertia) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (hε : IsDeligneEps ε) {rc : IrrGL (w.adicCompletion E) → WD h} (hl : Laws a ha ε rc)
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
  have h1 := H E Ω g A w h rc ⟨a, ha, ε, hε, hl⟩ i hi κ L t ht hT 1 (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)
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

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open GlobalTheory.TameRes

theorem residue_of_cong {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime] (hAP : IsPlaceOver (F := E) A P)
    (hN : normV P = g) (hgP : ((g : ℕ) : 𝓞 E) ∈ P.asIdeal) (hgP2 : ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hσ : σ ∈ Ine (F := E) A) (hζ : IsGenSys ζ) (hT : TameCoupled A κ σ ζ) (u ϖ : 𝓞 E) (π : Ω)
    (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hπ : π ^ (normV P - 1) = algebraMap E Ω (ϖ : E))
    (hv : A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1) :
    ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧
      algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hg2 : 2 ≤ g := hgp.two_le
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  rw [hN] at hπ

  have hg1 : 0 < g - 1 := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hg1
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hy; exact hgΩ hy.symm
  have hTy : redThrough A κ (σ y / y) = ζ 1 := hT 1 one_pos y (by rw [pow_one]; exact hy)
  have hϖ0 : algebraMap E Ω (ϖ : E) ≠ 0 := by
    rw [ne_eq, map_eq_zero, RingOfIntegers.coe_eq_zero_iff]
    rintro rfl; exact hϖ2 (zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hπ; exact hϖ0 hπ.symm
  have hϖg : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation ((g : ℕ) : Ω) := by
    have e : ((g : ℕ) : Ω) = algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) := by simp
    rw [e]
    exact le_antisymm (val_le_of_unif hAP hϖ hgP hgP2) (val_le_of_unif hAP hgP hϖ hϖ2)
  have hπy : A.valuation π = A.valuation y := by
    have h1 : A.valuation π ^ (g - 1) = A.valuation y ^ (g - 1) := by
      rw [← map_pow, ← map_pow, hπ, hy, hϖg]
    exact (pow_left_inj₀ zero_le zero_le hg1.ne').mp h1
  have hvy0 : A.valuation y ≠ 0 := by simpa using hy0
  have hw1 : A.valuation (π / y) = 1 := by rw [map_div₀, hπy, div_self hvy0]
  have hwσ : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw1.le
  have hσy0 : σ y ≠ 0 := fun h => hy0 (σ.injective (by rw [h, map_zero]))
  have key : σ π / π - σ y / y = (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    rw [map_div₀]
    field_simp
  have hq : A.valuation (σ y / y) ≤ 1 := (A.valuation_le_one_iff _).2 (tameQuot_mem A σ hg1 hgΩ hy)
  have h1 : A.valuation (σ π / π - σ y / y) < 1 := by
    rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw1, div_one]
    calc A.valuation (σ y / y) * A.valuation (σ (π / y) - π / y)
        ≤ 1 * A.valuation (σ (π / y) - π / y) := by gcongr
      _ < 1 := by rw [one_mul]; exact hwσ

  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem P g hN hgP u
  have hua' : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 := by
    have := (hAP (u - (a : 𝓞 E))).2 hua
    simpa using this
  have h3 : A.valuation (σ y / y - (a : Ω)) < 1 := by
    have e : σ y / y - (a : Ω) = -(σ π / π - σ y / y) + (σ π / π - algebraMap E Ω (u : E)) +
        (algebraMap E Ω (u : E) - (a : Ω)) := by ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ hv) hua'
    rw [Valuation.map_neg]; exact h1
  have haA : (a : Ω) ∈ A := by exact_mod_cast (natCast_mem A a)
  have hred : redThrough A κ (σ y / y) = (a : Formalism.CyclotomicNorms.Fbar g) := by
    rw [redThrough_eq_of_val_sub κ (tameQuot_mem A σ hg1 hgΩ hy) haA h3]
    unfold redThrough
    rw [dif_pos haA]
    have : (⟨(a : Ω), haA⟩ : A) = (a : A) := Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast]
  have hz : ζ 1 = (a : Formalism.CyclotomicNorms.Fbar g) := by rw [← hTy, hred]
  refine ⟨a, ?_, hua, by rw [map_natCast, hz]⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
  intro hd
  have h0 : (a : Formalism.CyclotomicNorms.Fbar g) = 0 := (CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g a).2 hd
  have ho := (hζ 1 one_pos).1
  rw [hz, h0, pow_one] at ho
  have hz0 : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    exact zero_ne_one
  omega

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

def labDatum {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : GlobalTheory.GLq.LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

end GlobalTheory.DepthZeroRankOneLabel

open GlobalTheory.WeilDeligne in
theorem GlobalTheory.DepthZeroRankOneLabel.wild_trivial (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (hT : GlobalTheory.SplitWeil.IsTame μ)
    (a : Weil (D.nd.plOm.2 (D.naut.plGw k v)) →* ((D.naut.plGw k v).adicCompletion D.host.E)ˣ)
    (ha : GlobalTheory.LocLanglands.IsLocalArtin (D.nd.plOm.2 (D.naut.plGw k v)) a)
    (ε : GlobalTheory.LocLanglands.EpsFamily (D.nd.plOm.1 (D.naut.plGw k v)))
    (rc : GlobalTheory.LocGL.IrrGL ((D.naut.plGw k v).adicCompletion D.host.E) → WD (D.nd.plOm.2 (D.naut.plGw k v)))
    (hl : GlobalTheory.LocLanglands.Laws a ha ε rc) :
    ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : G D.host.E D.nd.Om) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 := by
  have htame := GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((hl.depth (GlobalTheory.LocGL.IrrGL.ofChar μ hμ)).1 (by
    refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv
      (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep (Irr.ofDet 1 μ hμ).toIrrRep).some.symm ?_
    refine (Submodule.ne_bot_iff _).2 ⟨(show (Irr.ofDet 1 μ hμ).V from (1 : ℂ)), GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_,
      (one_ne_zero : (1 : ℂ) ≠ 0)⟩
    have hu' : u ∈ GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin 1) := hu
    have h1 := GlobalTheory.StepData.mem_KOne.1 hu' 0 0
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    have h2 : μ (Matrix.GeneralLinearGroup.det u) = 1 := hT _ (by
      have e : ((Matrix.GeneralLinearGroup.det u : (_)ˣ) : (D.naut.plGw k v).adicCompletion D.host.E) = u.val 0 0 := by
        simp [Matrix.det_fin_one]
      rw [e]; exact h1)
    change (GlobalTheory.SmGL.detRep (Fin 1) μ) u (1 : ℂ) = (1 : ℂ)
    simp [GlobalTheory.SmGL.detRep, h2]))
  rw [hl.one, WD.lpOfChar, WD.tame_mk] at htame
  intro σ hσ
  have h2 := LinearMap.congr_fun (htame σ hσ) (fun _ => 1)
  have h3 := congrFun h2 0
  simpa using h3

theorem GlobalTheory.DepthZeroRankOneLabel.lab_eq_of_tameRep : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → labAt hL D k v (Irr.ofDet 1 μ hμ) = X - C c := by
  intro hDZ hL D Γ k v μ hμ hT u hu hex c hc
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨a, ha, ε, hε, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hSet : GlobalTheory.WeilDeligne.TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k)
      (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have e1 : rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 μ hμ) =
      GlobalTheory.WeilDeligne.WD.lpOfChar _ (μ.comp a) (ha.smooth hμ) := hl.one μ hμ
  have hwild : ∀ σ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : G D.host.E D.nd.Om) ∈ GlobalTheory.WeilDeligne.Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 :=
    GlobalTheory.DepthZeroRankOneLabel.wild_trivial D k v μ hμ hT a ha ε _ hl
  have hval : μ (a ⟨D.ntypes.tg k v, GlobalTheory.WeilDeligne.Ine_le_Weil _ hSet.2.1⟩) =
      μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) := by
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hw := D.naut.plGw_over k v
    have hN := GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw
    have hw2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal ^ 2 := fun h2 => by
      have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (D.host.g_prime k).ne_zero
      have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
      have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h2)
      exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
    obtain ⟨ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hex
    obtain ⟨n, hn, hun, hgen⟩ := GlobalTheory.DepthZeroRankOneLabel.residue_of_cong _ _ _ (D.nd.plOm.2 _) hN hw hw2
      (Γ.kv k v) _ (Γ.ζ k) (D.ntypes.tg_mem k v) (Γ.ζ_gen k) (Γ.tg_tame k v) u ϖ π hϖ hϖ2 hπ hv
    have hx := GlobalTheory.DepthZeroRankOneLabel.val_lt_of_mem hun
    exact GlobalTheory.DepthZeroRankOneLabel.value_at_gen hDZ hε hl (I.i k v) (I.cont k v) hw (Γ.kv k v)
      (GlobalTheory.DepthZeroRankOneLabel.labDatum (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
      _ (D.ntypes.tg_mem k v) (Γ.tg_tame k v) μ hμ hT n hn hgen _ (by simpa using hx)
  unfold labAt
  rw [e1, GlobalTheory.WeilDeligne.WD.lab_lpOfChar_eq_iff hSet _ hwild c, hc, MonoidHom.comp_apply, hval]
