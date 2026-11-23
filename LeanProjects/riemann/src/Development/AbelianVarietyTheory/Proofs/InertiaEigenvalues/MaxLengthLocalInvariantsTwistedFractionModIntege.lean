import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

noncomputable def divBy (a : O) : O →ₗ[O] KmodO O :=
  (Submodule.mkQ _).comp ((LinearMap.mulLeft O ((algebraMap O (FractionRing O) a)⁻¹)).comp
    (Algebra.linearMap O (FractionRing O)))

theorem divBy_apply (a y : O) : divBy a y =
    Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y) := rfl

theorem ker_divBy {a : O} (ha : a ≠ 0) : LinearMap.ker (divBy a) = Ideal.span {a} := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  ext y
  rw [LinearMap.mem_ker, divBy_apply, Ideal.mem_span_singleton]
  refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    have hb' : algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y := hb
    rw [map_mul, hb', mul_inv_cancel_left₀ h0]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    change algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) (a * b)
    rw [map_mul, inv_mul_cancel_left₀ h0]

theorem mem_range_divBy {a : O} (ha : a ≠ 0) (x : KmodO O) (hx : a • x = 0) :
    x ∈ LinearMap.range (divBy a) := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  rw [divBy_apply]
  congr 1
  have hy' : algebraMap O (FractionRing O) y = algebraMap O (FractionRing O) a * z := by
    rw [← Algebra.smul_def]; exact hy
  rw [hy', inv_mul_cancel_left₀ h0]

theorem length_le_of_smul_eq_zero {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : Module.length O P ≤ addVal O a := by
  have hle : P ≤ LinearMap.range (divBy a) := fun x hx => mem_range_divBy ha x (hP x hx)
  let f : P →ₗ[O] O ⧸ Ideal.span {a} :=
    (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).toLinearMap.comp
      ((LinearMap.quotKerEquivRange (divBy a)).symm.toLinearMap.comp (Submodule.inclusion hle))
  have hf : Function.Injective f := by
    intro x y hxy
    have := (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).injective hxy
    have := (LinearMap.quotKerEquivRange (divBy a)).symm.injective this
    exact Submodule.inclusion_injective hle this
  calc Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := Module.length_le_of_injective f hf
    _ = addVal O a := Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a

theorem lenUnit_le_of_smul_eq_zero (l : ℕ) {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : lenUnit (O := O) l P ≤ lenUnit (O := O) l (O ⧸ Ideal.span {a}) := by
  unfold lenUnit
  have hne : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
    exact fun h => ha (addVal_eq_top_iff.mp h)
  have h1 : (Module.length O P).toNat ≤ (Module.length O (O ⧸ Ideal.span {a})).toNat :=
    ENat.toNat_le_toNat ((length_le_of_smul_eq_zero ha P hP).trans_eq
      (Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a).symm) hne
  gcongr

end DVR

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

theorem lenUnit_invariants_le (D : D7) (i : D.nd.Loc) (hls : D.nd.l i ∉ D.host.small)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ) (hn : 0 < n) :
    lenUnit (O := D.nd.O i) (D.nd.l i)
        ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w))) ≤
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℚ) := by
  haveI := D.nd.lPrime i
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ hgI
  set b : (D.nd.O i)ˣ := Formalism.MainNotions.N.Glob.epsO D.nd i g with hbdef
  have hb : (b : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ 1 * ((1 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) := by
    rw [Units.val_one, mul_one, ← UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hls, ← hg]
    rfl
  set a : D.nd.O i := (b : D.nd.O i) ^ n - 1 with hadef
  have hva : addVal (D.nd.O i) a =
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℕ∞) * addVal (D.nd.O i) ((D.nd.l i : ℕ) : D.nd.O i) := by
    rw [hadef, hb]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_pow_sub_one (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i)
      (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) 1 le_rfl (fun h => absurd h hl2) 1 n hn
  have ha0 : a ≠ 0 := by
    intro h
    have ht : addVal (D.nd.O i) a = ⊤ := by rw [h]; simp
    rw [hva] at ht
    obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
    rw [he] at ht
    exact absurd ht (by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _)
  have hkill : ∀ x ∈ Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)),
      a • x = 0 := by
    intro x hx
    have hfix := (Representation.mem_invariants _ x).mp hx ⟨g, hgD⟩
    have hfix' : ((b ^ n)⁻¹ : (D.nd.O i)ˣ) • x = x := by
      have e1 : ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)) ⟨g, hgD⟩ x =
          (((b ^ (-(n : ℤ)) : (D.nd.O i)ˣ)) : D.nd.O i) • x := by
        rfl
      rw [e1] at hfix
      rw [Units.smul_def, ← zpow_natCast, ← zpow_neg]
      exact hfix
    rw [hadef, sub_smul, one_smul]
    conv_lhs => rw [← hfix']
    rw [Units.smul_def, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, ← Units.smul_def, hfix', sub_self]
  calc lenUnit (O := D.nd.O i) (D.nd.l i) _
      ≤ lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) :=
        lenUnit_le_of_smul_eq_zero (D.nd.l i) ha0 _ hkill
    _ = _ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i hva

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

theorem unbotD_le {m : WithBot ℚ} {c : ℚ} (h : m ≤ (c : WithBot ℚ)) (hc : 0 ≤ c) : m.unbotD 0 ≤ c := by
  cases m with
  | bot => simpa using hc
  | coe a => simpa using h

theorem one_add_padicValNat_le (l : ℕ) [Fact l.Prime] {n t : ℕ} (hn : 0 < n) (hnt : n < t) :
    1 + padicValNat l n ≤ 2 * t := by
  have h1 : l ^ padicValNat l n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
  have h2 : 2 ^ padicValNat l n ≤ l ^ padicValNat l n :=
    Nat.pow_le_pow_left (Fact.out : l.Prime).two_le _
  have h3 : padicValNat l n < 2 ^ padicValNat l n := Nat.lt_two_pow_self
  omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small →
    D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) →
    ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  intro D i col hl2 _ _ hcol
  haveI := D.nd.lPrime i
  have key : h0 D.nd i col ≤ 2 * (D.R.t : ℚ) := by
    unfold h0
    refine unbotD_le ?_ (by positivity)
    apply Finset.max_le
    intro y hy
    obtain ⟨⟨w, n⟩, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hn0, hnt⟩ := Finset.mem_Ioo.mp hn
    refine WithBot.coe_le_coe.mpr ((lenUnit_invariants_le D i hl2 w (hcol w hw) n hn0).trans ?_)
    exact_mod_cast one_add_padicValNat_le (D.nd.l i) hn0 hnt
  exact_mod_cast key

end GlobalTheory.InvariantsKO
