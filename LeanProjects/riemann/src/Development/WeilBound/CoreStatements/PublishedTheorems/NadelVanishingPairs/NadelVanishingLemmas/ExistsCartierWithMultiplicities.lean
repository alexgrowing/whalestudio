import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisorStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 3 0
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩
private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_zpow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (n : ℤ) (v : X) :
    Scheme.ord ((g ^ n : (X.functionField)ˣ) : X.functionField) v =
      n * Scheme.ord (g : X.functionField) v := by
  let φ : (X.functionField)ˣ →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd (Scheme.ord (a : X.functionField) v)
      map_one' := by simp [Scheme_ord_one]
      map_mul' := fun a b => by
        rw [Units.val_mul, Scheme.ord_mul a.ne_zero b.ne_zero, ofAdd_add] }
  have h := map_zpow φ g n
  have h2 := congrArg Multiplicative.toAdd h
  simpa [φ, toAdd_zpow, smul_eq_mul] using h2

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_open {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X} (U : X.Opens)
    (hy : y ∈ U) (h : (X.functionField)ˣ)
    (hord : ∀ v ∈ U, Scheme.ord (h : X.functionField) v = 0) : UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ, (∀ v ∈ U, Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z (hz.mem_open U.isOpen hy))).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv => by rw [Scheme_ord_units_inv, hord v hv, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

private theorem exists_local_unit_ord_eq_finite_sum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [DecidableEq X] (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (c : X → ℤ)
    (S : Finset X) (hS : ∀ z ∈ S, Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : (X.functionField)ˣ, ∀ v ∈ U,
      Scheme.ord (f : X.functionField) v = ∑ z ∈ S, if v = z then c z else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, fun v _ => by simp [Scheme_ord_one]⟩
  | insert z S hzS ih =>
    obtain ⟨U1, hx1, f1, hf1⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨U2, hx2, π, hπ⟩ := PrimeDivCartier.exists_local_eqn X hufd z
      (hS z (Finset.mem_insert_self z S)) x
    refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, f1 * π ^ (c z), fun v hv => ?_⟩
    rw [Finset.sum_insert hzS, Units.val_mul, Scheme.ord_mul f1.ne_zero (π ^ c z).ne_zero,
      Scheme_ord_units_zpow, hf1 v hv.1, hπ v hv.2]
    split_ifs <;> simp [add_comm]

theorem _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ,
        (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) →
          ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  intro X _ _ hufd c hfin hc
  classical
  have hS : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 :=
    fun z hz => hc z (hfin.mem_toFinset.mp hz)
  have hsum : ∀ v, (∑ z ∈ hfin.toFinset, if v = z then c z else 0) = c v := by
    intro v
    rw [Finset.sum_ite_eq]
    split_ifs with hv
    · rfl
    · have : c v = 0 := by
        by_contra h'
        exact hv (hfin.mem_toFinset.mpr h')
      exact this.symm
  choose U hxU f hf using fun x => exists_local_unit_ord_eq_finite_sum hufd c hfin.toFinset hS x
  have hmem : (fun x => germOf x (f x)) ∈ cartierGroup X := by
    intro x
    refine ⟨U x, hxU x, f x, fun y hy => ?_⟩
    rw [germOf_eq_iff]
    have hu := unitAt_of_ord_eq_zero_on_open hufd (U x ⊓ U y) ⟨hy, hxU y⟩ (f x * (f y)⁻¹)
      (fun v hv => by
        rw [Units.val_mul, Scheme.ord_mul (f x).ne_zero ((f y)⁻¹).ne_zero, Scheme_ord_units_inv,
          hf x v hv.1, hf y v hv.2, add_neg_cancel])
    simpa [div_eq_mul_inv] using hu
  let D : CartierDiv X := (⟨fun x => germOf x (f x), hmem⟩ : cartierGroup X)
  refine ⟨D, fun z => ?_⟩
  have he : D.IsEqn z (f z) := rfl
  rw [he.mult_eq, hf z z (hxU z), hsum]
