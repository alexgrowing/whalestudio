import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.LTCrys
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EqNegOneOfJumpAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfHasSumZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfLt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD GlobalTheory.PZ GlobalTheory.PMC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PMC.BrChar

theorem map_algebraMap {l : ℕ} [Fact l.Prime] (K : FinExt l) (τ : ↥K.1 →+* Om l)
    (hτ : ∀ y : ↥K.1, ‖(y : Om l)‖ ≤ 1 → ‖τ y‖ ≤ 1) (q : ℚ_[l]) :
    τ (algebraMap ℚ_[l] ↥K.1 q) = algebraMap ℚ_[l] (Om l) q := by
  let f : ℚ_[l] →+* Om l := τ.comp (algebraMap ℚ_[l] ↥K.1)
  have hf : ∀ x : ℚ_[l], ‖x‖ ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => hτ _ (by
    show ‖algebraMap ℚ_[l] (Om l) x‖ ≤ 1
    rwa [norm_algebraMap'])
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hlO : ‖(l : Om l)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  have hc : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.continuousAt_iff.2 fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
    have hp : 0 < ‖(l : ℚ_[l])‖ ^ n := pow_pos (norm_pos_iff.2 hl0) n
    refine ⟨_, hp, fun x hx => ?_⟩
    rw [dist_zero_right] at hx
    rw [map_zero, dist_zero_right]
    have h1 := hf (x / (l : ℚ_[l]) ^ n) (by rw [norm_div, norm_pow, div_le_one hp]; exact hx.le)
    rw [map_div₀, map_pow, map_natCast, norm_div, norm_pow, hlO, div_le_one hp] at h1
    exact h1.trans_lt hn
  exact congrFun ((Padic.denseRange_ratCast l).equalizer hc (continuous_algebraMap ℚ_[l] (Om l))
    (funext fun r => by simp)) q

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
    ∀ (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (LL : FinExt l)
      (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) →
      ∃ (τ₀ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ) (π' : ↥(OL Bw.Kw)) (z : ℕ → Om l),
        (∀ x : E, j₀.1 (algebraMap E (w.adicCompletion E) x) = ((τ₀ ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) ∧
        LTData Bw.Kw χ π' z ∧ ((τ₀ (π' : ↥Bw.Kw.1) : ↥LL.1) : Qbar l) = j₀.1 (π : w.adicCompletion E) ∧
        ∀ g : ↥(Dec (F := E) A), ent ψ g = ((τ₀ ((χ (Bw.e g) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : ↥LL.1) : Qbar l) := by
  intro E Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hψc hψ

  have hmem : ∀ g, ent ψ g ∈ LL.1 := fun g => Subtype.property _
  have hv : Valued.v ((1 : w.adicCompletion E) + π) = 1 := by
    apply Valuation.map_one_add_of_lt
    unfold IsUnifAt at hπ
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπL : j₀.1 (π : w.adicCompletion E) ∈ LL.1 := by
    have h0 : (1 : w.adicCompletion E) + π ≠ 0 := fun h0 => by simp [h0] at hv
    obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 _ h0)
    have hd : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [hσ, GlobalTheory.PY.LTInh.ord_unit (x := Units.mk0 _ h0) hv] at this
      omega
    have := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, hd, hσ] at this
    simp only [zpow_zero, mul_one, Units.val_mk0, map_add, map_one] at this
    simpa using LL.1.sub_mem this LL.1.one_mem
  have hall : ∀ x : w.adicCompletion E, j₀.1 x ∈ LL.1 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [map_zero]; exact LL.1.zero_mem
    obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 x hx)
    have h1 := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, map_mul, map_zpow₀, hσ, Units.val_mk0] at h1
    have h2 := LL.1.mul_mem h1 (LL.1.inv_mem (LL.1.toSubfield.zpow_mem hπL (deg σ)))
    have h3 : j₀.1 (π : w.adicCompletion E) ^ deg σ ≠ 0 := zpow_ne_zero _ (by simp)
    rwa [mul_inv_cancel_right₀ h3] at h2

  obtain ⟨⟨j, hj, hjE⟩, H⟩ := GlobalTheory.LTTateC.main E Ω l w A h O Bw hB a ha
  obtain ⟨-, H2, H3⟩ := H j hj hjE
  obtain ⟨k, hk⟩ := GlobalTheory.LTTateC.exists_ringEquiv_Kw Bw j hj hjE
  obtain ⟨π', hπ', hππ⟩ := H2 π hπ
  obtain ⟨⟨c, hc, hcW⟩, H4⟩ := H3 π' hπ' π hππ

  let τ : ↥Bw.Kw.1 →+* Om l := j₀.1.comp (k.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hτk : ∀ x, τ (k x) = j₀.1 x := fun x => congrArg j₀.1 (k.symm_apply_apply x)
  have hτ : ∀ y : ↥Bw.Kw.1, ‖(y : Om l)‖ ≤ 1 → ‖τ y‖ ≤ 1 := fun y hy => by
    obtain ⟨x, rfl⟩ := k.surjective y
    rw [hk, GlobalTheory.LTTateC.norm_le_one_iff j hj] at hy
    rw [hτk]
    exact (GlobalTheory.LTTateC.norm_le_one_iff j₀.1 j₀.2 x).2 hy
  let τ₀ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1 :=
    { τ.codRestrict LL.1 (fun y => hall _) with
      commutes' := fun q => Subtype.ext (map_algebraMap Bw.Kw τ hτ q) }
  have hτ₀ : ∀ x, ((τ₀ (k x) : ↥LL.1) : Qbar l) = j₀.1 x := hτk

  let χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ :=
    (Units.map (k : w.adicCompletion E →+* ↥Bw.Kw.1).toMonoidHom).comp (c.comp Bw.e.symm.toMonoidHom)
  have hχ : ∀ g, ((χ g : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) = k (c (Bw.e.symm g) : (w.adicCompletion E)ˣ) := fun _ => rfl
  obtain ⟨χ₁, z, hz⟩ := exists_ltData_of_irreducible l Bw.Kw π' hπ'
  obtain ⟨_, hF, v, hvz, hS, hv0, -, -⟩ := ltData_tilt_hyps l Bw.Kw χ₁ π' z hz
  obtain ⟨-, hz0, hz1, hzr, -⟩ := hz
  obtain ⟨_, hiff⟩ := GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom l Bw.Kw π' hπ'
  refine ⟨τ₀, χ, π', z, fun x => ?_, ⟨hπ', hz0, hz1, hzr, fun g => ?_⟩, ?_, fun g => ?_⟩
  · rw [← hτ₀]
    congr 2
    exact Subtype.ext ((hk _).trans (hjE x))
  · obtain ⟨⟨u, -, hu⟩, H5⟩ := H4 c hc hcW g
    refine ⟨u, Subtype.ext (by rw [hχ, hk]; exact hu), _, (hiff u _).2 rfl, fun n => ?_⟩
    have h6 := H5 u hu _ hF v hS hv0 n
    have hind : Topology.IsInducing (algebraMap (Om l) ℂ_[l]) :=
      (AddMonoidHomClass.isometry_of_norm (algebraMap (Om l) ℂ_[l])
        fun y => PadicComplex.norm_extends l y).isEmbedding.isInducing
    rw [← hind.hasSum_iff]
    have e2 : ((Formalism.Per.σO (g : GQ l) (v n) : Formalism.Per.OC l) : ℂ_[l]) =
        algebraMap (Om l) ℂ_[l] ((g : GQ l) (z n)) := by
      refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (v n)).trans ?_
      rw [hvz]
      exact GlobalTheory.RingBasics.σC_coe _ _
    rw [e2] at h6
    refine (congrArg (HasSum · _) (funext fun i => ?_)).mp h6
    push_cast
    rw [hvz, Function.comp_apply, map_mul, map_pow]
    rfl
  · rw [← hτ₀]
    congr 2
    exact Subtype.ext (hππ.symm.trans (hk _).symm)
  · rw [hχ, hτ₀, MulEquiv.symm_apply_apply]
    have hd := (GlobalTheory.LTExt.ext_profinite h (B := Unit) 1 continuous_const).1
    refine congrFun (hd.equalizer hψc (j₀.2.comp hc) (funext fun σ => ?_)) g
    show ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (c ⟨σ, Weil_le_Dec h σ.2⟩ : (w.adicCompletion E)ˣ)
    rw [hψ, hcW, Units.val_mul, Units.val_zpow_eq_zpow_val]

end GlobalTheory.PMC.BrChar

end
