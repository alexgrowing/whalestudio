import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

theorem card_le_of_pow_eq {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (h : ∀ x : F, x ^ n = x) :
    Nat.card F ≤ n := by
  haveI := Fintype.ofFinite F
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero F hn
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id (fun x => by simp [h]) ?_)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hn, ← Nat.card_eq_fintype_card]
  omega

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]

omit [NumberField L] in
theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have h : IsIntegral A (algebraMap L Ω (x : L)) :=
    (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

variable [Algebra K L] [IsScalarTower K L Ω]

theorem isPlaceOver_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K L Ω]
  exact h (algebraMap (𝓞 K) (𝓞 L) x)

theorem normV_eq_pow [IsAlgClosure L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hA : IsPlaceOver A w)
    {σ : G K Ω} (hσ : IsFrob A (normV (w.under (𝓞 K))) σ) (hI : Ine (F := K) A ≤ galOf K L Ω) {m : ℕ}
    (hm : ∀ n, σ ^ n ∈ galOf K L Ω ↔ m ∣ n) : normV w = normV (w.under (𝓞 K)) ^ m := by
  set v := w.under (𝓞 K)
  have h2 : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  set f := w.asIdeal.inertiaDeg (𝓞 K)
  haveI := w.isMaximal
  haveI := v.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < normV v := Finite.one_lt_card
  have hw : 1 < normV w := Finite.one_lt_card
  have hf : 0 < f := Nat.pos_of_ne_zero fun h => by
    rw [h, pow_zero] at h2
    omega
  obtain ⟨s, hs⟩ := exists_isFrob hA
  have hs' : IsFrob A (normV v ^ f) (galEmb K L Ω s) := h2 ▸ ⟨hs.1, hs.2⟩
  have h3 : m ∣ f := by
    rw [← hm]
    have := hI (inv_mul_mem_Ine_of_isFrob hs' (GlobalTheory.FrobRestrict.isFrob_pow hσ f))
    exact ((galOf K L Ω).mul_mem_cancel_left ((galOf K L Ω).inv_mem (galEmb_mem K L Ω s))).1 this
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hf.ne' (zero_dvd_iff.1 h3)
  have h4 : normV w ≤ normV v ^ m := by
    refine card_le_of_pow_eq (Nat.one_lt_pow hm0 hq) fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h5 := (GlobalTheory.FrobRestrict.isFrob_pow hσ m).2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    rw [(hm m).2 dvd_rfl x] at h5
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, ← hA]
    simpa using h5
  rw [h2] at h4 ⊢
  rw [le_antisymm ((pow_le_pow_iff_right₀ hq).1 h4) (Nat.le_of_dvd hf h3)]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def compAt (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infPart : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

theorem ideleMap_mem_infConn {a : Ideles K} (ha : a ∈ infConn K) : ideleMap K L a ∈ infConn L := by
  obtain ⟨y, hy, rfl⟩ := ha
  have hc : Continuous (infiniteAdeleMap K L) :=
    continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp (Continuous.prodMk_left 0))
  refine ⟨Units.map (infiniteAdeleMap K L).toMonoidHom y, ?_,
    Units.ext (Prod.ext rfl (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)).symm)⟩
  have := (Continuous.units_map (infiniteAdeleMap K L).toMonoidHom hc).image_connectedComponent_subset 1 ⟨y, hy, rfl⟩
  rwa [map_one] at this

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]

theorem descend [TopologicalSpace B] [T1Space B] {artK : Ideles K →* Gab K Ω} {artL : Ideles L →* Gab L Ω}
    (hK : IsGlobalArtin artK) (hL : IsGlobalArtin artL) (μ : Gab L Ω →* B) (hμ : Continuous μ) :
    ∃ ν : G K Ω →* B, Continuous ν ∧ ∀ (x : Ideles K) (σ : G K Ω), artK x = toAb K Ω σ →
      ν σ = μ (artL (ideleMap K L x)) := by
  let ψ : Ideles K →* B := μ.comp (artL.comp (ideleMap K L))
  have hψ : Continuous ψ := hμ.comp (hL.quot.continuous.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap K L))
  have hk : ∀ z ∈ (diagUnits L).range ⊔ infConn L, μ (artL z) = 1 := fun z hz => by
    have : z ∈ artL.ker := hL.ker ▸ Subgroup.le_topologicalClosure _ hz
    rw [MonoidHom.mem_ker.1 this, map_one]
  have hle : artK.ker ≤ ψ.ker := by
    rw [hK.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
    · rintro _ ⟨k, rfl⟩
      exact hk _ (Subgroup.mem_sup_left ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele K L k).symm⟩)
    · intro y hy
      exact hk _ (Subgroup.mem_sup_right (ideleMap_mem_infConn K L hy))
    · exact isClosed_singleton.preimage hψ
  let f : Gab K Ω →* B := artK.liftOfSurjective hK.quot.surjective ⟨ψ, hle⟩
  have hf : ∀ x, f (artK x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply artK _ _ ⟨ψ, hle⟩ x
  have hc : Continuous f := by
    rw [hK.quot.isQuotientMap.continuous_iff]
    exact hψ.congr fun x => (hf x).symm
  refine ⟨f.comp (toAb K Ω), hc.comp continuous_quot_mk, fun x σ h => ?_⟩
  rw [MonoidHom.comp_apply, ← h, hf]
  rfl

omit [Algebra K L] in
variable (K L Ω) in

def overL : galOf K L Ω →* G L Ω where
  toFun s := AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) s.2
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
