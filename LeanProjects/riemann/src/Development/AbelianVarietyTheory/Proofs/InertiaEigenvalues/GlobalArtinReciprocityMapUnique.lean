import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_one_of_unit_unif {B : Type} [Group B] (v : HeightOneSpectrum (𝓞 E)) (f : (v.adicCompletion E)ˣ →* B)
    (hu : ∀ x, IsUnitAt v x → f x = 1) (hp : ∀ x, IsUnifAt v x → f x = 1) (x : (v.adicCompletion E)ˣ) : f x = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hv : Valued.v ((π : E) : v.adicCompletion E) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : ((π : E) : v.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let p : (v.adicCompletion E)ˣ := Units.mk0 _ hπ0
  have hpv : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1) := hv
  have hfp : f p = 1 := hp p hpv
  have key : ∀ n : ℤ, ∀ y : (v.adicCompletion E)ˣ, Valued.v (y : v.adicCompletion E) = WithZero.exp n → f y = 1 := by
    intro n
    induction n using Int.induction_on with
    | zero => exact fun y hy => hu y (by show Valued.v _ = 1; rw [hy, WithZero.exp_zero])
    | succ n ih =>
      intro y hy
      have h1 : f (y * p) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, hpv, ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, hfp, mul_one] at h1
    | pred n ih =>
      intro y hy
      have h1 : f (y * p⁻¹) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, Units.val_inv_eq_inv_val, map_inv₀, hpv, ← WithZero.exp_neg,
          ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, map_inv, hfp, inv_one, mul_one] at h1
  have h0 : Valued.v (x : v.adicCompletion E) ≠ 0 := by simp
  exact key _ x (WithZero.exp_log h0).symm

variable {Ω : Type} [Field Ω] [Algebra E Ω]

theorem unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    {B : Type} [Group B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E))
    (hu' : ∀ y, IsUnitAt v y → χ (art' (localIdele E v y)) = 1) (x : (v.adicCompletion E)ˣ) (hx : IsUnifAt v x) :
    χ (art (localIdele E v x)) = χ (art' (localIdele E v x)) := by
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, e'⟩ := (ha'.frob v A hA _).mpr ⟨σ, hσ, e⟩
  have hxy : IsUnitAt v (x * y⁻¹) := by
    show Valued.v _ = 1
    have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hx, ← hy, mul_inv_cancel₀ hy0]
  have h2 : localIdele E v x = localIdele E v (x * y⁻¹) * localIdele E v y := by
    rw [← map_mul, inv_mul_cancel_right]
  conv_rhs => rw [h2, map_mul, map_mul, hu' _ hxy, one_mul, e']

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_infPart {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hloc : ∀ v x, D (localIdele E v x) = 1) (x : Ideles E) :
    D x = D (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E x)) := by
  have hnhds : {z : Ideles E | D z = D x} ∈ nhds x := by
    have e : {z : Ideles E | D z = D x} = (fun z => x⁻¹ * z) ⁻¹' (D.ker : Set (Ideles E)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      rw [inv_mul_eq_one, eq_comm]
    rw [e]
    exact ((continuous_const.mul continuous_id).isOpen_preimage _ hD).mem_nhds (by simp)
  obtain ⟨T, hT⟩ := ((GlobalTheory.HeckeSplit.tendsto_truncIdele x).eventually hnhds).exists
  have h1 : ∀ v ∈ T, D (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := fun v _ => hloc v _
  rw [← show D (GlobalTheory.HeckeSplit.truncIdele x T) = D x from hT, GlobalTheory.HeckeSplit.truncIdele, map_mul, map_prod,
    Finset.prod_eq_one h1, mul_one]

theorem eq_one_of_local {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hdiag : ∀ k : Eˣ, D (diagUnits E k) = 1) (hinf : ∀ y ∈ infConn E, D y = 1)
    (hloc : ∀ v x, D (localIdele E v x) = 1) : D = 1 := by
  ext x
  rw [eq_infPart D hD hloc x, MonoidHom.one_apply]
  set y := GlobalTheory.HeckeSplit.infPart E x
  let C := Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ
  have hopen : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (C : Set (InfiniteAdeleRing E)ˣ)) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_connectedComponentOfOne_inf E)
  obtain ⟨k, hk⟩ := (denseRange_units_inf E).exists_mem_open hopen ⟨y, by simp [C.one_mem]⟩
  set kinf : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k with hkinf
  have hk' : y⁻¹ * kinf ∈ C := hk
  have h1 : D (GlobalTheory.HeckeSplit.infIdele E kinf) = 1 := by
    have h := eq_infPart D hD hloc (diagUnits E k)
    have e : GlobalTheory.HeckeSplit.infPart E (diagUnits E k) = kinf := Units.ext rfl
    rw [e, hdiag k] at h
    exact h.symm
  have h2 : D (GlobalTheory.HeckeSplit.infIdele E (y⁻¹ * kinf)) = 1 := hinf _ ⟨_, hk', rfl⟩
  have e : y = kinf * (y⁻¹ * kinf)⁻¹ := by group
  rw [e, map_mul, map_inv, map_mul, map_inv, h1, h2, inv_one, mul_one]

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem globalArtin_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  intro E Ω _ _ _ _ _ art art' ha ha'
  classical
  ext x
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  have hker : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → IsOpen ((χ.comp a).ker : Set (Ideles E)) := by
    intro a h
    have e : ((χ.comp a).ker : Set (Ideles E)) = a ⁻¹' U := by
      ext y
      simp [χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [e]
    exact hU.preimage h.quot.continuous
  have hdiag : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ k : Eˣ, a (diagUnits E k) = 1 := by
    intro a h k
    have hk : diagUnits E k ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hinf : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ y ∈ infConn E, a y = 1 := by
    intro a h y hy
    have hk : y ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  let ψ : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  let ψ' : Ideles E →* Gab E Ω ⧸ U := χ.comp art'
  let D : Ideles E →* Gab E Ω ⧸ U := ψ / ψ'
  let V : Subgroup (Ideles E) := ψ.ker ⊓ ψ'.ker
  have hV : IsOpen (V : Set (Ideles E)) := (hker art ha).inter (hker art' ha')
  have hDV : ∀ z ∈ V, D z = 1 := fun z hz => by
    show ψ z / ψ' z = 1
    rw [MonoidHom.mem_ker.mp hz.1, MonoidHom.mem_ker.mp hz.2, div_one]
  have hDo : IsOpen (D.ker : Set (Ideles E)) := Subgroup.isOpen_mono (fun z hz => hDV z hz) hV
  have hDd : ∀ k : Eˣ, D (diagUnits E k) = 1 := fun k => by
    show χ (art _) / χ (art' _) = 1
    rw [hdiag art ha, hdiag art' ha', map_one, div_one]
  have hDi : ∀ y ∈ infConn E, D y = 1 := fun y hy => by
    show χ (art _) / χ (art' _) = 1
    rw [hinf art ha y hy, hinf art' ha' y hy, map_one, div_one]
  obtain ⟨S, M, -, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E V hV ∅

  have hgood : ∀ v ∉ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    refine eq_one_of_unit_unif v (D.comp (localIdele E v)) (fun y hy => hDV _ (hSu v hv y hy)) (fun y hy => ?_) z
    show ψ _ / ψ' _ = 1
    rw [div_eq_one]
    exact unif_eq ha ha' χ v (fun y' hy' => MonoidHom.mem_ker.mp (hSu v hv y' hy').2) y hy

  have hbad : ∀ v ∈ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    have ho : IsOpen ((D.comp (localIdele E v)).ker : Set (v.adicCompletion E)ˣ) :=
      hDo.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele v)
    have ho1 : IsOpen (((1 : (v.adicCompletion E)ˣ →* Gab E Ω ⧸ U)).ker : Set (v.adicCompletion E)ˣ) := by
      rw [MonoidHom.ker_one]
      exact isOpen_univ
    refine GlobalTheory.units_adicCompletion_hom_ext E v _ (D.comp (localIdele E v)) 1 ho ho1 (fun c => ?_) z
    rw [MonoidHom.one_apply, MonoidHom.comp_apply, ← locUnit_apply]
    let m : ℕ := (WithZero.log (v.valuation E (c : E))).natAbs
    obtain ⟨a, hap, hapos⟩ :=
      GlobalTheory.FinPlaceApproxPos.approxpos_target E S (fun u => if u = v then (c : E) else 1) (M + 1 + m)
    have haW : v.valuation E (a - c) ≤ WithZero.exp (-(((M + 1 : ℕ) : ℤ) + m)) := by
      have := hap v hv
      rw [if_pos rfl] at this
      exact val_le_of_le v this (by push_cast; omega)
    have hz : v.valuation E (a / c - 1) ≤ WithZero.exp (-((M + 1 : ℕ) : ℤ)) :=
      val_div_sub_one_le v c.ne_zero le_rfl haW
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
      push_cast at hz
      omega
    let au : Eˣ := Units.mk0 a ha0
    let q : Eˣ := au / c
    have hq : (q : E) = a / c := by simp [q, au]
    have hqV : locUnit E v q ∈ V := hSc v hv q (by rw [hq]; exact val_le_of_le v hz (by push_cast; omega))
    have hprod := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E _ D hDo hDd hDi au (fun φ => hapos φ) S
      (fun u hu => by rw [locUnit_apply]; exact hgood u hu _)
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => hDV _ (hSc u hu au (by
      have := hap u hu
      rw [if_neg hne] at this
      exact val_le_of_le u this (by push_cast; omega))))] at hprod
    have e : au = c * q := by simp [q]
    rw [e, map_mul, map_mul, hDV _ hqV, mul_one] at hprod
    exact hprod
  have hD : D = 1 := eq_one_of_local D hDo hDd hDi fun v z => by
    by_cases hv : v ∈ S
    · exact hbad v hv z
    · exact hgood v hv z
  have h1 : χ (art x / art' x) = 1 := by
    rw [_root_.map_div]
    exact DFunLike.congr_fun hD x
  exact (QuotientGroup.eq_one_iff _).mp h1

end GlobalTheory.ArtinUniq
