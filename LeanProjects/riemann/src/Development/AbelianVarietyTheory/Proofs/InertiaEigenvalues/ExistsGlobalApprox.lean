import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletionsStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistValues
variable {D : D7}

theorem pow_eq_one (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) (hc : ChrEq δc δ) (n : ℕ)
    (hn : δ.OrderDvd n) (x : (AE D)ˣ) : δc x ^ n = 1 := by
  have hH : IsHeckeChar D (δc ^ n) := by
    refine ⟨?_, fun k => ?_⟩
    · exact (continuous_pow n).comp hc.1.1
    · rw [MonoidHom.pow_apply, hc.1.2 k, one_pow]
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) hH (fun y hy => by
    rw [MonoidHom.pow_apply]
    exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hc n hn y hy) x
  rwa [MonoidHom.pow_apply] at this

theorem exists_pow_of_snd {R A B I : Type} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B)
    (s : A ≃+* (I → ℂ)) (n : ℕ) (hn : 0 < n) (x : Rˣ) (hx : (e x).2 = 1) : ∃ V : Rˣ, x = V ^ n := by
  have hz : ∀ τ, s (e x).1 τ ≠ 0 := by
    intro τ h0
    have h1 : s (e x).1 * s (e ((x⁻¹ : Rˣ) : R)).1 = 1 := by
      rw [← map_mul, ← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one, map_one]
    have := congrFun h1 τ
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  choose w hw using fun τ => IsAlgClosed.exists_pow_nat_eq (s (e x).1 τ) hn
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h0 => hz τ (by rw [← hw τ, h0, zero_pow hn.ne'])
  let wi : I → ℂ := fun τ => (w τ)⁻¹
  have hwi : w * wi = 1 := funext fun τ => mul_inv_cancel₀ (hw0 τ)
  have hiw : wi * w = 1 := funext fun τ => inv_mul_cancel₀ (hw0 τ)
  let U : (A × B)ˣ := ⟨(s.symm w, 1), (s.symm wi, 1), by
      rw [Prod.mk_mul_mk, ← map_mul, hwi, map_one, mul_one]; rfl, by
      rw [Prod.mk_mul_mk, ← map_mul, hiw, map_one, mul_one]; rfl⟩
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom U, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  change (x : R) = (e.symm (s.symm w, 1)) ^ n
  rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow,
    show w ^ n = s (e x).1 from funext fun τ => by rw [Pi.pow_apply, hw τ], RingEquiv.symm_apply_apply, ← hx,
    Prod.mk.eta, RingEquiv.symm_apply_apply]

theorem eq_one_of_finPart (c : (AE D)ˣ →* Circle) (n : ℕ) (hn : 0 < n) (hpow : ∀ x, c x ^ n = 1) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨V, hV⟩ := exists_pow_of_snd e (Formalism.IndefR.Eqv.splitEquiv D) n hn x ((he _).2.trans hx)
  rw [hV, map_pow, hpow]

theorem exists_global_approx : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) :=
  GlobalTheory.T.exists_field_element_relative_approx_completions

set_option maxHeartbeats 1000000 in
open Formalism.L2.Host in

theorem mem_of_infPart {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle)
    (hc : ChrEq δc δ) (n : ℕ) (hn : 0 < n) (hord : δ.OrderDvd n) (htame : ∀ v, δ.TameAt v) (hval : δ.ValuesIn 0 σ)
    (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 δc δ hc
  have hev := GlobalTheory.HeckeSplit.eventually_unrAt δ.1 δ.2.1
  set Rm := (Filter.eventually_cofinite.1 hev).toFinset with hRmdef
  have hRm : ∀ P, P ∉ Rm → δ.UnrAt P := fun P hP => by
    by_contra h
    exact hP ((Set.Finite.mem_toFinset _).2 h)
  let zz : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x
  have hz0 : ∀ P, (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 zz.isUnit).1
  obtain ⟨k, hk⟩ := exists_global_approx D.host.E Rm (fun P => (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P)
    (fun P _ => hz0 P)
  let K : (AE D)ˣ := Units.map (incA D).toMonoidHom k
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e1 : δc x = δc (b (x * K⁻¹)) := by
    have : δc (x * K⁻¹) = δc x := by rw [map_mul, map_inv, hc.1.2 k, inv_one, mul_one]
    rw [← this]
    conv_lhs => rw [hab (x * K⁻¹)]
    rw [map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha _).2, one_mul]
  set y := b (x * K⁻¹) with hydef
  have hy : infPart D (y : AE D) = 1 := (hb _).1
  have hyP : ∀ P, ι (finPart D (y : AE D)) P =
      (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P * algebraMap D.host.E _ ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro P
    rw [(hb _).2, Units.val_mul, map_mul, map_mul]
    have : ((K⁻¹ : (AE D)ˣ) : AE D) = incA D ((k⁻¹ : D.host.Eˣ) : D.host.E) := rfl
    rw [this]
    show _ * ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((k⁻¹ : D.host.Eˣ) : D.host.E)) P = _
    rw [h1]
    rfl

  let yy : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom y
  have hy0 : ∀ P, ι (finPart D (y : AE D)) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 yy.isUnit).1
  obtain ⟨S0, -, -, hS0⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN yy
  choose kk hkk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hy0 P)
  have key := hprod y hy (S0 ∪ Rm) kk (fun P _ => ⟨(hkk P).1, (hkk P).2.1⟩)
    (fun P hP => hS0 P fun h => hP (Finset.mem_union_left _ h))
  rw [e1, key]
  refine prod_mem fun P _ => ?_
  have hva : ∀ t : D.host.E, Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) t) = P.valuation D.host.E t :=
    fun t => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P t
  by_cases hR : P ∈ Rm
  ·
    set zP := (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P with hzP
    have hk0 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) ≠ 0 := by
      rw [hva]; exact (Valuation.ne_zero_iff _).2 k.ne_zero
    have hlt : WithZero.exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hzv : Valued.v zP = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) := by
      refine (Valuation.map_eq_of_sub_lt _ ?_).symm
      rw [Valuation.map_sub_swap]
      exact (hk P hR).trans_lt (mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hz0 P))) hlt)
    have hkinv : algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) *
        algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hkv' : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) *
        Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1 := by
      rw [← map_mul, hkinv, map_one]
    have hyv : Valued.v (ι (finPart D (y : AE D)) P) = 1 := by
      rw [hyP, map_mul, mul_comm, hzv]; exact hkv'
    have hy1 : Valued.v (ι (finPart D (y : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
      have : ι (finPart D (y : AE D)) P - 1 = (zP - algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) *
          algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
        rw [hyP, sub_mul, mul_comm (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)), hkinv]
      rw [this, map_mul]
      calc Valued.v (zP - _) * Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E))
          ≤ WithZero.exp (-1 : ℤ) * Valued.v zP *
            Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) :=
            mul_le_mul' (hk P hR) le_rfl
        _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, hzv, mul_comm (Valued.v (algebraMap _ _ (k : D.host.E))), hkv', mul_one]
    obtain ⟨q1, q2, q3⟩ := hkk P
    have hq : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E)) = 1 := by
      rw [hva, ← q1, hyv]
    have hq1 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have e2 : algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1 =
          (ι (finPart D (y : AE D)) P - 1) - (ι (finPart D (y : AE D)) P - algebraMap D.host.E _ (kk P : D.host.E)) := by ring
      rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le hy1 ?_)
      rw [← hva, hq, mul_one] at q3
      simpa using q3
    have ht := htame P (Formalism.L2.Host.atFin P (kk P)) hq hq1
    have : δ.locK P (kk P) = 1 := ht
    rw [this, Units.val_one]
    exact one_mem _
  ·
    have hu := hRm P hR
    have hkv0 : P.valuation D.host.E (kk P : D.host.E) ≠ 0 := (Valuation.ne_zero_iff _).2 (kk P).ne_zero
    have hm : P.valuation D.host.E (kk P : D.host.E) = WithZero.exp (-(-WithZero.log (P.valuation D.host.E (kk P : D.host.E)))) := by
      rw [neg_neg, WithZero.exp_log hkv0]
    rw [GlobalTheory.CharUnramVal.locK_eq_val_zpow δ P hu (kk P) _ hm, Units.val_zpow_eq_zpow_val]
    refine zpow_mem ?_ _
    obtain ⟨t, ht⟩ := hval P hu
    refine ⟨t, ht.trans ?_⟩
    simp [Formalism.L2.Host.HChar.valTw]

theorem mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := by
  intro D V pd k _ σ δ δc hT dd hdd g
  obtain ⟨hc, ⟨n, hn, hord⟩, -, htame, -, hval⟩ := hT
  have key : ∀ x : (AE D)ˣ, ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
    intro x
    obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
    rw [hab x, map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha x).2, one_mul]
    exact mem_of_infPart σ δ δc hc n hn hord htame hval _ (hb x).1
  rcases hdd with ⟨hex, hv⟩ | ⟨hex, hv⟩
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx]
    exact key x
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx, MonoidHom.inv_apply, Circle.coe_inv]
    exact inv_mem (key x)

end GlobalTheory.TwistValues
