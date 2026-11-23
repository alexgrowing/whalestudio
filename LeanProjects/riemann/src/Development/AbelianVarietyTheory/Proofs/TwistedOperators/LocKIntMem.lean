import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.TwistValues

section General

variable {L : Type} [Field L] [NumberField L]

theorem locK_int_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hP : P ∈ S) (b : 𝓞 L) (k : Lˣ) (hk : (k : L) = b) : χ.locK P k ∈ Λ := by
  classical
  have hb : b ≠ 0 := by
    rintro rfl
    exact k.ne_zero hk
  have h0 : P.intValuation b ≠ 0 := P.intValuation_ne_zero b hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation b = WithZero.exp (-(n : ℤ)) := by
    have h1 := P.intValuation_le_one b
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    refine ⟨(-WithZero.log (P.intValuation b)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => n + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 : P.intValuation (a - b) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    have h1 := ha P hP
    rw [if_pos rfl] at h1
    exact (P.intValuation_le_pow_iff_mem _ _).2 h1
  have h2 : P.intValuation a = P.intValuation b := by
    refine Valuation.map_eq_of_sub_lt _ (h1.trans_lt ?_)
    rw [hn, WithZero.exp_lt_exp]
    push_cast
    omega
  have ha0 : (a : L) ≠ 0 := by
    intro h
    have h3 : a = 0 := by exact_mod_cast h
    rw [h3, map_zero] at h2
    exact h0 h2.symm
  have hmem : χ.locK P (Units.mk0 _ ha0) ∈ Λ := by
    have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
    rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
      have h1 := ha v hvS
      rw [if_neg hvP] at h1
      exact Ideal.pow_le_self (Nat.succ_ne_zero n) h1))] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
    exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _
  have hval : ∀ z : L, Valued.v (algebraMap L (P.adicCompletion L) z) = P.valuation L z :=
    fun z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P z
  have hint : ∀ z : 𝓞 L, P.valuation L (z : L) = P.intValuation z := fun z => P.valuation_of_algebraMap z
  have h4 : χ.locK P (Units.mk0 _ ha0 * k⁻¹) = 1 := by
    have e : ((atFin P (Units.mk0 _ ha0 * k⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
        algebraMap L (P.adicCompletion L) ((a : L) * (b : L)⁻¹) := by
      rw [← hk, ← Units.val_inv_eq_inv_val]
      rfl
    refine ht P _ ?_ ?_
    · unfold IsUnitAt
      rw [e, hval, map_mul, map_inv₀, hint, hint, h2, mul_inv_cancel₀ h0]
    · have e' : (a : L) * (b : L)⁻¹ - 1 = ((a - b : 𝓞 L) : L) * (b : L)⁻¹ := by
        have : (b : L) ≠ 0 := hk ▸ k.ne_zero
        push_cast
        field_simp
      rw [e, ← map_one (algebraMap L (P.adicCompletion L)), ← map_sub, hval, e', map_mul, map_inv₀, hint, hint, hn]
      refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4 ▸ hmem

theorem locK_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ∈ Λ := by
  by_cases hP : P ∈ S
  · obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
    have hb0 : (b : L) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have h1 := locK_int_mem χ Λ S ht hi hu hv hP b (Units.mk0 _ hb0) rfl
    have h2 := locK_int_mem χ Λ S ht hi hu hv hP a (k * Units.mk0 _ hb0) (by
      rw [Units.val_mul, ← e]
      exact div_mul_cancel₀ _ hb0)
    rw [map_mul] at h2
    exact (mul_mem_cancel_right h1).1 h2
  · have h : χ.locK P k = χ.val P ^ ordF P k := GlobalTheory.Mem.Chr.CharModel.locK_unr (F := L) ⟨χ.1, χ.2⟩ (hu P hP) k
    rw [h]
    exact Λ.zpow_mem (hv P hP) _

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
  Formalism.L2.Col GlobalTheory.RationalValues
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_mem {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (M : Subfield ℂ) (hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ M) (x : (AE D)ˣ) : ((c x : Circle) : ℂ) ∈ M := by
  have h1 : ∀ x, c x ^ n = 1 := HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨y, hy⟩ := IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn (a x) (ha x).2
  rw [hab x, map_mul, ← hy, map_pow, h1, one_mul]
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j j1 j2 (PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom (b x))
  rw [hprod (b x) (hb x).1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => hM P _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem xiH_locK_mem (hL : R.toLevCh.Is A.μ0) (hon : R.fam_pl_onto) (hmu : R.fam_muVal)
    (hok : ∀ t P, P ∈ A.ok t ↔ Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))))
    (i : Fin D.R.m) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ R.Q t ∪ R.Q A.μ0
  have hQ : ∀ v ∈ R.Q t, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).UnrAt v := fun v hv => by
    by_contra hn
    rcases (hL.Q_ram t v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : (((R.xiH t).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm (hL.xi_triv t) (hu v hv) hc, Units.val_one]
      show (((R.xiH t).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hon v (hs _ hS)
      have h1 : (R.C.mu0 i * R.xiH t).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i t P ((hok t P).2 (hs _ fun w hw => hw.elim (hS w) (hQ w)))⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i A.μ0 P ((hok A.μ0 P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact locK_mem (R.xiH t) _ (T ∪ T.image conjPrime₂) (hL.xi_tame t) (TypeValues.inf_eq_one _ hn ho) hu hv PP k

theorem xiVal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → GlobalTheory.TwistField.XiVal R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF t x
  obtain ⟨_, _, _, hT⟩ := hF.tie
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact char_mem _ _ (hL.xi t) hn ho _
    (xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t) x

end GlobalTheory.TwistValues
