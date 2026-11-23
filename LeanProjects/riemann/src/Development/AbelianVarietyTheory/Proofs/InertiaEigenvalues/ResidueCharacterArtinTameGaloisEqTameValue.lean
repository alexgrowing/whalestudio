import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TameResRead

section Gal

open GlobalTheory.TameValChar

theorem tameVal_eq_of_tameRep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ),
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) →
    ∀ (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E), u ∉ P.asIdeal → NX.TameRep P e σ u → NX.tameVal φ P e u = φ σ := by
  intro E Ω _ _ _ _ _ M _ φ P e m hopen hm hI
  classical
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω P A0 hA0
  obtain ⟨hq2, hq1⟩ := two_le_normV_and_not_mem P
  set q := Formalism.ConjugateSelfDual.normV P with hqdef
  set n := q - 1 with hndef
  obtain ⟨N0, hN0⟩ := hI A0 hA0 γ hγ.1
  set L := n * m ^ N0 with hLdef
  have hL : ((L : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    rw [hLdef, Nat.cast_mul, Nat.cast_pow]
    exact P.isPrime.mul_notMem hq1 (fun h => hm (P.isPrime.mem_of_pow_mem _ h))
  have hL0 : L ≠ 0 := ne_zero_of_not_mem hL
  obtain ⟨ϖ0, hϖ0, hϖ0'⟩ : ∃ ϖ0 : 𝓞 E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖ0ne : algebraMap E Ω (ϖ0 : E) ≠ 0 := by
    intro h
    apply hϖ0'
    have : ϖ0 = 0 := by
      have h' : ((ϖ0 : E)) = 0 := (map_eq_zero _).1 h
      exact_mod_cast h'
    rw [this]
    exact zero_mem _
  obtain ⟨π1, hπ1⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ0 : E)) (Nat.pos_of_ne_zero hL0)
  have hπ1ne : π1 ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0] at hπ1
    exact hϖ0ne hπ1.symm
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A0.valuation (τ y / y - 1) < 1) → φ τ = 1 := fun τ hτ =>
    GlobalTheory.WildOpenKernel.eq_one_of_wild φ P A0 m hA0 hopen hm τ hτ (hI A0 hA0 τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
  have hγL : φ γ ^ L = 1 := by
    rw [hLdef, mul_comm, pow_mul, hN0, one_pow]
  have hJ := GlobalTheory.TameJoint.exists_pow_joint φ P A0 L γ π1 (ϖ0 : E) hA0 hopen hL hγ hw hγL hπ1ne hπ1
  set ζ1 := γ π1 / π1 with hζ1def
  have hγπ1 : γ π1 = ζ1 * π1 := by rw [hζ1def, div_mul_cancel₀ _ hπ1ne]
  have hζ1L : ζ1 ^ L = 1 := by
    rw [hζ1def, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  obtain ⟨σ0, hσ0, hprim⟩ := GlobalTheory.TameRootSurj.main P A0 L ϖ0 π1 hA0 hL hϖ0 hϖ0' hπ1
  obtain ⟨b0, -, hb0⟩ := hJ σ0 hσ0
  have hζ1prim : IsPrimitiveRoot ζ1 L := by
    rw [hb0, mul_div_cancel_right₀ _ hπ1ne] at hprim
    have h1 : L ∣ orderOf ζ1 := hprim.eq_orderOf ▸ orderOf_pow_dvd b0
    have h2 : orderOf ζ1 ∣ L := orderOf_dvd_of_pow_eq_one hζ1L
    have h3 : orderOf ζ1 = L := Nat.dvd_antisymm h2 h1
    exact h3 ▸ IsPrimitiveRoot.orderOf ζ1

  obtain ⟨τ, hτ⟩ := ReciprocityTheory.Gal.exists_isFrob hA0
  have hσF : τ * γ * τ⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A0 := ReciprocityTheory.Gal.conj_mem_Ine hτ.1 hγ.1
  set η := (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 / π1 with hηdef
  have hη : η ^ L = 1 := by
    rw [hηdef, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  have hyη : (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 = η * π1 := by rw [hηdef, div_mul_cancel₀ _ hπ1ne]
  have hγη : γ η = η := ine_fix_root hA0 hL hγ.1 hη
  have hcalc : (τ * γ * τ⁻¹) π1 = ζ1 ^ q * π1 := by
    have e1 : (τ * γ * τ⁻¹) π1 = τ (γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1)) := rfl
    have e2 : γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1) = ζ1 * (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 := by
      rw [hyη, map_mul, hγη, hγπ1]; ring
    rw [e1, e2, map_mul, ReciprocityTheory.Gal.mul_inv_apply, frob_root hA0 hL hτ hζ1L]
  obtain ⟨b, hbφ, hbπ⟩ := hJ _ hσF
  have hφconj : φ (τ * γ * τ⁻¹) = φ γ := by
    rw [map_mul, map_mul, mul_comm (φ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [hcalc] at hbπ
  have hζq : ζ1 ^ q = ζ1 ^ b := mul_right_cancel₀ hπ1ne hbπ
  have hmod : q ≡ b [MOD L] := modEq_of_pow_eq hζ1prim hL0 hζq
  have hordγ : orderOf (φ γ) ∣ L := orderOf_dvd_of_pow_eq_one hγL
  have hγq : φ γ ^ q = φ γ ^ b := pow_eq_pow_iff_modEq.2 (hmod.of_dvd hordγ)
  have hγn : φ γ ^ n = 1 := by
    have h1 : φ γ ^ n * φ γ = φ γ := by
      rw [← pow_succ, show n + 1 = q by omega, hγq, ← hbφ, hφconj]
    exact mul_eq_right.1 h1

  set π0 := π1 ^ (m ^ N0) with hπ0def
  have hπ0 : π0 ^ n = algebraMap E Ω (ϖ0 : E) := by
    rw [hπ0def, ← pow_mul, mul_comm, ← hLdef]
    exact hπ1
  have hπ0ne : π0 ≠ 0 := pow_ne_zero _ hπ1ne
  set ζ0 := ζ1 ^ (m ^ N0) with hζ0def
  have hζ0prim : IsPrimitiveRoot ζ0 n := hζ1prim.pow (Nat.pos_of_ne_zero hL0) (by rw [hLdef, mul_comm])
  have hC : ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A0, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π0 = ζ0 ^ b * π0 := by
    intro σ hσ
    obtain ⟨b, h1, h2⟩ := hJ σ hσ
    refine ⟨b, h1, ?_⟩
    rw [hπ0def, map_pow, h2, hζ0def, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
  have hn1A : ¬ A0.valuation (n : Ω) < 1 := not_val_lt_one hA0 hq1
  have hordn : orderOf (φ γ) ∣ n := orderOf_dvd_of_pow_eq_one hγn
  have hK : ∀ (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (a : ℕ), Formalism.L2.NX.TameRep P e σ u →
      A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 → φ σ = φ γ ^ a := by
    intro σ u a hσ ha
    obtain ⟨g, hg, hgv⟩ := GlobalTheory.TameMove.tameRep_move P e σ u A0 ϖ0 π0 hA0 hϖ0 hϖ0' hπ0 hσ
    obtain ⟨b, hbφ, hbπ⟩ := hC _ hg
    have hφg : φ (g * σ * g⁻¹) = φ σ := by
      rw [map_mul, map_mul, mul_comm (φ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [hbπ, mul_div_cancel_right₀ _ hπ0ne] at hgv
    have hab : ζ0 ^ a = ζ0 ^ b := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A0 hn1A ?_ ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · have e1 : ζ0 ^ a - ζ0 ^ b = (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) - (ζ0 ^ b - (algebraMap E Ω (u : E)) ^ e) := by
          ring
        rw [e1]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hgv)
    have hmod' : a ≡ b [MOD n] := modEq_of_pow_eq hζ0prim (ne_zero_of_not_mem hq1) hab
    rw [← hφg, hbφ]
    exact (pow_eq_pow_iff_modEq.2 (hmod'.of_dvd hordn)).symm
  intro σ u hu hσ
  obtain ⟨a, ha⟩ := GlobalTheory.TamePowTeich.exists_zeta_pow_close P A0 ζ0 hA0 hζ0prim u e hu
  have hex : ∃ σ : Formalism.ConjugateSelfDual.G E Ω, Formalism.L2.NX.TameRep P e σ u := ⟨σ, hσ⟩
  rw [Formalism.L2.NX.tameVal, dif_pos hex, hK _ u a hex.choose_spec ha, hK σ u a hσ ha]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem zpow_apply_root {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) {σ : Formalism.ConjugateSelfDual.G E Ω} (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) {ζ π : Ω}
    (hζ : ζ ^ k = 1) (hπ : σ π = ζ * π) (e : ℤ) : (σ ^ e) π = ζ ^ e * π := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (ne_zero_of_not_mem hk)] at hζ
    exact zero_ne_one hζ
  have hfix : σ ζ = ζ := ine_fix_root hA hk hσ hζ
  induction e using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, AlgEquiv.mul_apply, ih, map_mul, map_zpow₀, hfix, hπ, zpow_add₀ hζ0, zpow_one]
    ring
  | pred i ih =>
    apply σ.injective
    rw [← AlgEquiv.mul_apply, ← zpow_one_add, map_mul, map_zpow₀, hfix, hπ,
      show (1 + (-(i : ℤ) - 1)) = -(i : ℤ) by ring, ih, zpow_sub_one₀ hζ0]
    field_simp

theorem tameRep_zpow {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P)
    {σ : Formalism.ConjugateSelfDual.G E Ω} (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) {ϖ : 𝓞 E} {π : Ω} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hπ : π ^ (normV P - 1) = algebraMap E Ω (ϖ : E)) {u : 𝓞 E} (hu : u ∉ P.asIdeal)
    (hv : A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1) (e : ℤ) : NX.TameRep P e (σ ^ e) u := by
  obtain ⟨hq2, hq1⟩ := two_le_normV_and_not_mem P
  have hϖ : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (ne_zero_of_not_mem hq1)] at hπ
    exact hϖ hπ.symm
  have hζ : (σ π / π) ^ (normV P - 1) = 1 := by
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, div_self hϖ]
  refine ⟨A, hA, zpow_mem hσ e, ϖ, π, h1, h2, hπ, ?_⟩
  rw [zpow_apply_root hA hq1 hσ hζ (div_mul_cancel₀ _ hπ0).symm e, mul_div_cancel_right₀ _ hπ0]
  exact zpow_close (L_vone P A hA u hu) hv e

end Gal

open Formalism.IndefR.Datum in

theorem eq_res_locU {D : D7} {M : Type} [CommGroup M] {χ : (AE D)ˣ →* M} {PP : Pl D.host.E}
    (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) {c : (kP PP)ˣ →* M} (hc : IsResAt χ PP c) (a : 𝓞 D.host.E)
    (ha0 : (a : D.host.E) ≠ 0) (z : (kP PP)ˣ) (hz : (z : kP PP) = Ideal.Quotient.mk PP.asIdeal a) :
    χ (Formalism.L2.JoinChr.locU h.1.1 (Units.mk0 (a : D.host.E) ha0)) = c z := by
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP h
  have he : idemAt PP * idemAt PP = idemAt PP := h.1.1
  have hb : toEAf D (incA D (a : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  have hval : ((Formalism.L2.JoinChr.locU h.1.1 (Units.mk0 (a : D.host.E) ha0) : (AE D)ˣ) : AE D) =
      1 + idemAt PP * (incA D (a : D.host.E) - 1) := rfl
  generalize Formalism.L2.JoinChr.locU h.1.1 (Units.mk0 (a : D.host.E) ha0) = x at hval ⊢
  generalize incA D (a : D.host.E) = b at hb hval
  have hv : toEAf D (x : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hval, GlobalTheory.ConjTwist.map_loc, hb]
    rfl
  have hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  refine hc x ?_ hx z ?_
  · rw [hval]
    linear_combination (1 - b) * he
  · have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F PP) e2).trans ?_
    rw [GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hz]
    ring

theorem res_zpow_eq_tameVal : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (rc : Recip D D.nd.Om), rc.Good → ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (φ : G D.host.E D.nd.Om →* Rˣ), IsOpen (φ.ker : Set (G D.host.E D.nd.Om)) → ∀ (PP : Pl D.host.E) (m : ℕ), ((m : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A PP → ∀ σ ∈ Ine (F := D.host.E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) → Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP → ∀ c : (kP PP)ˣ →* Circle, IsResAt (GlobalTheory.SeriesTie.charOf rc f φ) PP c → ∀ (e : ℤ) (u : 𝓞 D.host.E), u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((c z : Circle) : ℂ) ^ e = f (NX.tameVal φ PP e u).1 := by
  intro hGAR D rc hrc R _ f φ hopen PP m hm hI hid c hc e u hu z hz
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om PP
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem PP
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ PP.asIdeal ∧ ϖ0 ∉ PP.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := PP.asIdeal) PP.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV PP - 1 by omega)
  have hu0 : (u : D.host.E) ≠ 0 := fun h => hu (by
    rw [show u = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hxu : IsUnitAt PP (Formalism.L2.Host.atFin PP (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : PP.adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om rc.art hrc.artin
    PP A hA ϖ hϖ1 hϖ2 π hπ (Formalism.L2.Host.atFin PP (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [Formalism.L2.Host.atFin])
  have hsym : rc.sym (Formalism.L2.JoinChr.locU hid.1.1 (Units.mk0 (u : D.host.E) hu0)) =
      GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ := by
    rw [hσart, Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext (hrc.loc PP _ (GlobalTheory.HeckeDetChar.isPlIdem hid) (Units.mk0 (u : D.host.E) hu0))
  obtain ⟨N, hN⟩ := hI A hA σ hσI
  have h1 := charOf_eq rc f hopen hsym (pow_ne_zero N (GlobalTheory.TameValChar.ne_zero_of_not_mem hm)) hN
  rw [eq_res_locU hid hc u hu0 z hz] at h1
  rw [tameVal_eq_of_tameRep φ PP e m hopen hm hI _ u hu (tameRep_zpow hA hσI hϖ1 hϖ2 hπ hu hσval e), h1, map_zpow]
  have h2 : ∀ w : Rˣ, f (w : R) = ((Units.map f.toMonoidHom w : ℂˣ) : ℂ) := fun _ => rfl
  rw [h2, h2, map_zpow, Units.val_zpow_eq_zpow_val]

end GlobalTheory.TameResRead

end
