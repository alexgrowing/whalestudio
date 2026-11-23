import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoEqn

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

def ordU (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem ord_prod_zpow {ι : Type} (J : Finset ι) (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (ordU (Y := Y) v) (fun j => u j ^ m j) J)
  rw [toAdd_prod] at h
  calc Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v
      = Multiplicative.toAdd (ordU v (∏ j ∈ J, u j ^ m j)) := rfl
    _ = ∑ j ∈ J, Multiplicative.toAdd (ordU v (u j ^ m j)) := h
    _ = ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

end GlobalTheory.Discrepancy.MonoEqn

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

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_generizations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X}
    (h : (X.functionField)ˣ)
    (hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (h : X.functionField) v = 0) :
    UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z hz hz1)).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv hv1 => by rw [Scheme_ord_units_inv, hord v hv hv1, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

open GlobalTheory.Discrepancy.MonoEqn in

theorem GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ D : CartierDiv Y, D.supp ≤ B → D.IsEqn y (∏ j ∈ J, u j ^ D.mult (w j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc D hD
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    fun x => AbelianProjective.ufd_stalk (K := k) q x
  obtain ⟨h, hh⟩ := D.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := hh.exists_nhds
  have key : ∀ v, v ⤳ y → Order.coheight v = 1 →
      Scheme.ord (((∏ j ∈ J, u j ^ D.mult (w j)) : Y.functionFieldˣ) : Y.functionField) v =
        D.mult v := by
    intro v hv hv1
    rw [ord_prod_zpow]
    by_cases hex : ∃ j ∈ J, v = w j
    · obtain ⟨j0, hj0, rfl⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [hc.ord_self j0 hj0, mul_one]
      · intro j hj hne
        rw [hc.ord_other j hj (w j0) hv (fun heq => hne (hc.inj hj hj0 heq.symm)), mul_zero]
      · intro h'
        exact absurd hj0 h'
    · have h0 : D.mult v = 0 := by
        by_contra hne
        exact hex ((hc.mem v hv hv1).mp (hD (CartierDiv.mem_supp_of_mult_ne_zero hne)))
      rw [h0]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [hc.ord_other j hj v hv (fun heq => hex ⟨j, hj, heq⟩), mul_zero]
  show D.germ y = germOf y _
  rw [show D.germ y = germOf y h from hh, germOf_eq_iff]
  have hu := unitAt_of_ord_eq_zero_on_generizations hufd ((∏ j ∈ J, u j ^ D.mult (w j)) * h⁻¹)
    (fun v hv hv1 => by
      rw [Units.val_mul, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _), Scheme_ord_units_inv,
        key v hv hv1, ← (hW v (hv.mem_open W.isOpen hyW)).mult_eq, add_neg_cancel])
  simpa [div_eq_mul_inv] using hu
