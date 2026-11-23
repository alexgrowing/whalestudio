import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NeZeroOfMemRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne

section Transport

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
  (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (i : ℚ_[p] ≃+* w.adicCompletion F) (hi : Continuous i)
include hw hi

theorem norm_symm_le (z : w.adicCompletion F) (hz : ‖z‖ ≤ 1) : ‖i.symm z‖ ≤ 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have h2 : ‖t⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one t⁻¹ (-1)).2 (by simpa using h1)
    exact this
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h3 : ‖t⁻¹ / (p : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one₀ (by have := (Fact.out : p.Prime).one_lt; positivity)]
    simpa using h2
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h3
  have e : z⁻¹ = (p : w.adicCompletion F) * i.toRingHom (t⁻¹ / (p : ℚ_[p])) := by
    rw [map_div₀, map_inv₀, map_natCast]
    change z⁻¹ = (p : w.adicCompletion F) * ((i t)⁻¹ / p)
    rw [ht, RingEquiv.apply_symm_apply]
    have hpE : (p : w.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    field_simp
  have h5 : ‖z⁻¹‖ < 1 := by
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h4) (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw)
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  rw [norm_inv] at h5
  have := (one_le_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

omit hw in

theorem norm_symm_lt (z : w.adicCompletion F) (hz : ‖z‖ < 1) : ‖i.symm z‖ < 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h1
  have e : i.toRingHom t⁻¹ = z⁻¹ := by
    rw [map_inv₀]; change (i t)⁻¹ = z⁻¹; rw [ht, RingEquiv.apply_symm_apply]
  rw [e, norm_inv] at h4
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  have := (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

theorem exists_ker_red {n : ℕ} (u : GL (Fin n) (w.adicCompletion F))
    (hu : u ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion F) (Fin n)) :
    ∃ y : (GlobalTheory.GLp.red p n).ker, GlobalTheory.GLp.inc p n y = Matrix.GeneralLinearGroup.map i.symm.toRingHom u := by
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne w n).2, GlobalTheory.AdelicU.mem_princ_iff,
    GlobalTheory.AdelicU.mem_GLint_iff] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have hM : ∀ a b, ‖i.symm (u.1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 a b)))
  have hN : ∀ a b, ‖i.symm ((u⁻¹).1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 a b)))
  let M : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm (u.1 a b), hM a b⟩
  let N : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm ((u⁻¹).1 a b), hN a b⟩
  have hMm : M.map (PadicInt.Coe.ringHom (p := p)) = u.1.map i.symm := rfl
  have hNm : N.map (PadicInt.Coe.ringHom (p := p)) = (u⁻¹).1.map i.symm := rfl
  have hinj : Function.Injective (Matrix.map · (PadicInt.Coe.ringHom (p := p)) : Matrix (Fin n) (Fin n) ℤ_[p] → _) :=
    Matrix.map_injective Subtype.coe_injective
  have e1 : M * N = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  have e2 : N * M = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
  let y : GL (Fin n) ℤ_[p] := ⟨M, N, e1, e2⟩
  have hy : GlobalTheory.GLp.red p n y = 1 := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    change PadicInt.toZMod (M a b) = (1 : Matrix (Fin n) (Fin n) (ZMod p)) a b
    have h4 : M a b - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) a b ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      have h5 := norm_symm_lt w p i hi _ (Valued.toNormedField.norm_lt_one_iff.2 (h3 a b))
      convert h5 using 1
      rw [PadicInt.norm_def, PadicInt.coe_sub, Matrix.sub_apply, map_sub]
      congr 1
      by_cases hab : a = b
      · subst hab; simp; rfl
      · simp [Matrix.one_apply_ne hab]; rfl
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h4
    rw [h4]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  exact ⟨⟨y, hy⟩, Units.ext rfl⟩

end Transport

theorem exists_pull (D : D7) (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : QRep (D.host.g k) n)
    (hπ : IrrSm π) (hfix : fixK1 π.ρ ≠ ⊥) :
    ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)),
      Nonempty (π ≅ pull I k v σ) ∧
      GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥ := by
  let _ := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (hπ.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 hπ.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩, ?_⟩
  · change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
    rw [hg]
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
    refine (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, hy0⟩
    obtain ⟨z, hz⟩ := exists_ker_red (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v) (I.i k v) (I.cont k v) u hu
    change π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom u) y = y
    rw [← hz]
    have := (Submodule.mem_iInf _).1 hy z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem tame_of_isTameWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h}
    (hx : GlobalTheory.LocLanglands.IsTameWD x) : x.tame := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  refine (WD.tame_mk a).2 fun σ hσ => ha σ ⟨Wild_le_Ine hσ, fun y hy => ?_⟩
  have e : (σ : G E Ω) y - y = ((σ : G E Ω) y / y - 1) * y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_mul]
  exact mul_lt_of_lt_one_left h0 (hσ y hy)

end GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in

theorem GlobalTheory.SerSys.inertiaCharpoly_isLabel_of_action : Green → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), IsRc hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → LabParam D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    obtain ⟨a, ha, ε, -, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((hl.depth _).1 ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine actK_e_eq_self _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) ?_ (hP k v) D.R.r π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
