import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupledStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem principalCongruence_fixed_vector_rational_local_field {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥) :
    fixK1 (pull I k v τ).ρ ≠ ⊥ := by
  have hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hle : ∀ t : ℚ_[D.host.g k], ‖t‖ ≤ 1 → ‖I.i k v t‖ ≤ 1 := fun t ht =>
    GlobalTheory.TypeRec.Model.emb_le (D.naut.plGw k v) (D.host.g k) (I.i k v).toRingHom (I.cont k v) t ht
  have hlt : ∀ t : ℚ_[D.host.g k], ‖t‖ < 1 → ‖I.i k v t‖ < 1 := by
    intro t ht
    have hp := (Fact.out : (D.host.g k).Prime)
    have h2 : ‖t‖ ≤ ((D.host.g k : ℕ) : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one t (-1)).2 (by simpa using ht)
    have hp0 : ((D.host.g k : ℕ) : ℚ_[D.host.g k]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h3 : ‖t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one₀ (by have := hp.one_lt; positivity)]
      simpa using h2
    have e : I.i k v t = ((D.host.g k : ℕ) : (D.naut.plGw k v).adicCompletion D.host.E) *
        I.i k v (t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])) := by
      rw [← map_natCast (I.i k v) (D.host.g k), ← map_mul, mul_div_cancel₀ _ hp0]
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hle _ h3))
      (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt (D.naut.plGw k v) (D.host.g k) hw)
  have hint : ∀ (q : GL (Fin n) ℤ_[D.host.g k]) a b,
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n q)).1 a b ∈
        (D.naut.plGw k v).adicCompletionIntegers D.host.E := by
    intro q a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (Valued.toNormedField.norm_le_one_iff.1 (hle _ (PadicInt.norm_le_one (q.1 a b))))
  have hone : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) a b =
      I.i k v (((1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b : ℤ_[D.host.g k]) : ℚ_[D.host.g k]) := by
    intro a b
    by_cases h' : a = b
    · subst h'; simp
    · simp [Matrix.one_apply_ne h']
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun z => ?_, hy0⟩
  have hu : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z) ∈
      GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n) := by
    rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne (D.naut.plGw k v) n).2, GlobalTheory.AdelicU.mem_princ_iff,
      GlobalTheory.AdelicU.mem_GLint_iff]
    refine ⟨⟨fun a b => hint _ a b, fun a b => ?_⟩, fun a b => ?_⟩
    · rw [← map_inv, ← map_inv]
      exact hint _ a b
    · have hz : GlobalTheory.GLp.red (D.host.g k) n z = 1 := z.2
      have hab : PadicInt.toZMod ((z : GL (Fin n) ℤ_[D.host.g k]).1 a b) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (D.host.g k))) a b :=
        congrArg (fun m : GL (Fin n) (ZMod (D.host.g k)) => m.1 a b) hz
      have h4 : (z : GL (Fin n) ℤ_[D.host.g k]).1 a b - (1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b ∈
          RingHom.ker (PadicInt.toZMod (p := D.host.g k)) := by
        rw [RingHom.mem_ker, map_sub, hab]
        by_cases h' : a = b
        · subst h'; simp
        · simp [Matrix.one_apply_ne h']
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h4
      have h5 := hlt _ h4
      apply Valued.toNormedField.norm_lt_one_iff.1
      rw [Matrix.sub_apply, hone a b]
      convert h5 using 2
      rw [PadicInt.coe_sub, map_sub]
      rfl
  change τ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z)) y - y = 0
  rw [sub_eq_zero]
  exact GlobalTheory.Parabolic.mem_fixed.1 hy _ hu

theorem principalCongruenceFixedVectors_ne_bot_of_iso {g : ℕ} [Fact g.Prime] {n : ℕ} {π π' : QRep g n} (e : π ≅ π') (h : fixK1 π'.ρ ≠ ⊥) :
    fixK1 π.ρ ≠ ⊥ := by
  intro hb
  apply h
  rw [Submodule.eq_bot_iff] at hb ⊢
  intro x hx
  have hy : (e.inv.hom x) ∈ fixK1 π.ρ := by
    simp only [fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro q
    rw [← Rep.hom_comm_apply, hx q]
  have h0 := hb _ hy
  have : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← this, h0, map_zero]

end GlobalTheory.LabPin

namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem typeLab_of_local : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := GlobalTheory.T.exists_class_map_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := GlobalTheory.T.exists_type_components hL D T I rc hrc Rw rep hRow hDep
  have hP : LabParam D L rc := GlobalTheory.SerSys.Bridge.labParam_of D L rc hG (GlobalTheory.T.tame_support_compatible hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact GlobalTheory.T.tame_parameter_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := GlobalTheory.SerSys.inertiaCharpoly_isLabel_of_action hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent D I rep cp hcomp σ k v _ h2 s hs⟩

end GlobalTheory.LabPin
