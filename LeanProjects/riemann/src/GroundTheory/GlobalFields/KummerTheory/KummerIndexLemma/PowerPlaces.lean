import Mathlib
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom
import GroundTheory.GlobalFields.KummerTheory.SplittingKummer
import GroundTheory.GlobalFields.SplittingFromInequality
import GroundTheory.GlobalFields.IdeleGroups.LocalNorms

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh Module
  Filter IntermediateField AdeleBaseChange

namespace KummerIndex

section Radical

variable (K : Type*) [Field K] (p : ℕ)

def radicalGroup (y : Kˣ) : Subgroup Kˣ :=
  Subgroup.zpowers y ⊔ unitsPow K p

variable {K p}

theorem unitsPow_le_radicalGroup (y : Kˣ) : unitsPow K p ≤ radicalGroup K p y :=
  le_sup_right

theorem mem_radicalGroup_self (y : Kˣ) : y ∈ radicalGroup K p y :=
  le_sup_left (a := Subgroup.zpowers y) (Subgroup.mem_zpowers y)

theorem radicalGroup_le {y : Kˣ} {H : Subgroup Kˣ} (hy : y ∈ H) (hH : unitsPow K p ≤ H) :
    radicalGroup K p y ≤ H :=
  sup_le ((Subgroup.zpowers_le).2 hy) hH

theorem radicalClasses_radicalGroup (y : Kˣ) :
    radicalClasses K p (radicalGroup K p y) =
      Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [radicalClasses, radicalGroup, Subgroup.map_sup, MonoidHom.map_zpowers,
    QuotientGroup.map_mk'_self, sup_bot_eq]

theorem natCard_radicalQuotient (y : Kˣ) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) =
      orderOf (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [Nat.card_congr (radicalQuotientEquiv K p _).toEquiv, radicalClasses_radicalGroup,
    Nat.card_zpowers]

instance finite_radicalQuotient [NeZero p] (y : Kˣ) :
    Finite (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_radicalQuotient]
  exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p, NeZero.pos p, UnitsModPow.pow_eq_one _ _ _⟩)).ne'

theorem natCard_radicalQuotient_of_not_mem [Fact p.Prime] {y : Kˣ} (hy : y ∉ unitsPow K p) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) = p := by
  rw [natCard_radicalQuotient]
  refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
  rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable [Fact p.Prime] [HasEnoughRootsOfUnity K p] (Ω : Type*) [Field Ω] [Algebra K Ω]
  [IsSepClosed Ω]

theorem finrank_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    finrank K (kummerExtension K p Ω (radicalGroup K p y)) = p := by
  rw [finrank_kummerExtension, natCard_radicalQuotient_of_not_mem hy]

theorem isCyclic_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    IsCyclic Gal(kummerExtension K p Ω (radicalGroup K p y)/K) :=
  isCyclic_of_prime_card (p := p) (by
    rw [IsGalois.card_aut_eq_finrank, finrank_kummerExtension_radicalGroup Ω hy])

theorem unitsPowIn_kummerExtension_radicalGroup (y : Kˣ) :
    unitsPowIn K p (kummerExtension K p Ω (radicalGroup K p y)) = radicalGroup K p y :=
  unitsPowIn_kummerExtension K p Ω _ (unitsPow_le_radicalGroup y)

theorem exists_pow_eq_kummerExtension_radicalGroup (y : Kˣ) :
    ∃ α : kummerExtension K p Ω (radicalGroup K p y), α ^ p = algebraMap K _ (y : K) := by
  have h := mem_radicalGroup_self (p := p) y
  rw [← unitsPowIn_kummerExtension_radicalGroup Ω y] at h
  exact mem_unitsPowIn.1 h

end Radical

section Place

open SemiLocal

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.exists_place_mem_unitsPowIn_not_mem
    (hFI : FirstInequality.{u}) {a x : Kˣ} (hx : x ∉ radicalGroup K p a)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (haS : ∀ v ∉ S, v.valuation K (a : K) = 1) (hxS : ∀ v ∉ S, v.valuation K (x : K) = 1) :
    ∃ v ∉ S, a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      x ∉ unitsPowIn K p (v.adicCompletion K) := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  let Ω := AlgebraicClosure K
  let L := kummerExtension K p Ω (radicalGroup K p a)
  have hL : unitsPowIn K p L = radicalGroup K p a :=
    unitsPowIn_kummerExtension_radicalGroup Ω a
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω a
  have : HasEnoughRootsOfUnity L p := hasEnoughRootsOfUnity_of_ringHom (algebraMap K L) p
  let xL : Lˣ := Units.map (algebraMap K L : K →* L) x
  have hxL : xL ∉ unitsPow L p := by
    intro h
    apply hx
    rw [← hL]
    exact Subgroup.mem_comap.2 h
  let L' := kummerExtension L p (AlgebraicClosure L) (radicalGroup L p xL)
  have hfin : finrank L L' = p := finrank_kummerExtension_radicalGroup _ hxL
  have : IsCyclic Gal(L'/L) := isCyclic_kummerExtension_radicalGroup _ hxL
  suffices h : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, SplitsCompletely L' w by
    have h1 := hFI.finrank_eq_one_of_eventually_splitsCompletely h
    rw [hfin] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, below K w ∉ S :=
    tendsto_below.eventually hS.eventually_cofinite_notMem
  filter_upwards [hev] with w hw
  rw [splitsCompletely_kummerExtension_iff]
  suffices key : xL ∈ unitsPowIn L p (w.adicCompletion L) by
    intro c hc
    exact mem_unitsPowIn.1 (radicalGroup_le key (unitsPow_le_unitsPowIn L p _) hc)
  set v := below K w
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hw (hpS v h)
  let ιK : Kˣ →* (w.adicCompletion L)ˣ := Units.map (algebraMap K (w.adicCompletion L) : K →* _)
  let ιv : (v.adicCompletion K)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L) : _ →* _)
  let κ : Kˣ →* (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K) : K →* _)
  have hικ (z : Kˣ) : ιv (κ z) = ιK z := by
    apply Units.ext
    simp only [ιv, ιK, κ, Units.coe_map, MonoidHom.coe_coe]
    exact (IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L) _).symm
  have hxLw : ((ιK x : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      algebraMap L (w.adicCompletion L) (xL : L) := by
    simp only [ιK, xL, Units.coe_map, MonoidHom.coe_coe]
    exact IsScalarTower.algebraMap_apply K L (w.adicCompletion L) _
  suffices h : ιK x ∈ unitsPow (w.adicCompletion L) p by
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    refine mem_unitsPowIn.2 ⟨b, ?_⟩
    rw [← hxLw, ← hb, Units.val_pow_eq_pow_val]
  by_cases ha : a ∈ unitsPowIn K p (v.adicCompletion K)
  · obtain ⟨b, hb⟩ := mem_unitsPow.1 (Subgroup.mem_comap.1 (hcon v hw ha))
    refine mem_unitsPow.2 ⟨ιv b, ?_⟩
    rw [← map_pow, hb]
    exact hικ x
  · have ha' : κ a ∉ unitsPow (v.adicCompletion K) p := fun h ↦ ha (Subgroup.mem_comap.2 h)
    obtain ⟨k, hk⟩ := exists_mul_zpow_inv_mem_unitsPow v p hpv
      (units_map_mem_localUnits v (haS v hw)) (units_map_mem_localUnits v (hxS v hw)) ha'
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hk
    have hα0 : algebraMap L (w.adicCompletion L) (α : L) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      intro h0
      have h1 : (α : kummerExtension K p Ω (radicalGroup K p a)) = 0 := h0
      rw [h1, zero_pow (Fact.out : p.Prime).ne_zero, eq_comm, map_eq_zero] at hα
      exact a.ne_zero hα
    let αw : (w.adicCompletion L)ˣ := Units.mk0 _ hα0
    have hαw : αw ^ p = ιK a := by
      apply Units.ext
      simp only [αw, ιK, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      rw [← map_pow]
      change algebraMap L (w.adicCompletion L) ((α ^ p : kummerExtension K p Ω _) : L) = _
      rw [hα, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    refine mem_unitsPow.2 ⟨ιv b * αw ^ k, ?_⟩
    have hb' : ιv b ^ p = ιK x * (ιK a ^ k)⁻¹ := by
      rw [← map_pow, hb, map_mul, map_inv, map_zpow, hικ, hικ]
    have hαk : (αw ^ k) ^ p = ιK a ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαw]
    rw [mul_pow, hb', hαk, inv_mul_cancel_right]

end Place

end KummerIndex

end GroundTheory.Global
