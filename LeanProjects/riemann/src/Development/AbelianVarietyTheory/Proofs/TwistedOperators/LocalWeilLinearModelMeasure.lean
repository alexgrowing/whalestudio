import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LatVac
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.MixedForm

theorem char_eq_local_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι ν₀ hν
  have h := hT.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  haveI : Nonempty (Fin a) := ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) hT.geo.lt⟩⟩
  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ 0 ≠ 0 := by
    obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v a (a + a')
    obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (by rw [show f = 0 from funext hc, map_zero])
    have hf' : (fun Y => f (Y + Y₀)) ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
      ⟨hf.1.comp_continuous (continuous_add_const Y₀), hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩
    obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn hf'
    exact ⟨φ, hφ, by rw [e]; simpa using hY⟩
  refine ⟨t.comp σ, Or.inr (MonoidHom.ext fun x => ?_)⟩
  obtain ⟨g', rfl⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a) x
  set g := GlobalTheory.LeviAtPlace.leviHom h t G.V.J hJ hT.geo.hV.herm g' with hgdef
  have hg : g ∈ UAt σ G.V (evFin F v) := GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  have g1 : (mat g).map (piW t) = g'.1 := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  have g2 : (((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_snd,
      GlobalTheory.LeviAtPlace.conjComp, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.det_one, one_mul, Matrix.det_transpose, ← map_inv]
    rfl
  obtain ⟨g'', e, hact⟩ := hν g hg
  obtain rfl : g' = g'' := Units.ext (g1.symm.trans e)
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero h G.M B.ψ hT.base.std _ _ om hT.weil t ι hι g hg _ g2 φ φ₁ hφ hA
  rw [hact φ hφ φ₁ hφ₁ hA, chrW_div, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ (((a + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g') (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _), Fintype.card_fin]
    push_cast
    rfl
  rw [k2] at k1
  simp only [GlobalTheory.SplitFlip.omA, map_one, GlobalTheory.SplitFlip.apow_one, MonoidHom.one_apply, Units.val_one, mul_one,
    Matrix.mul_zero, Matrix.zero_mul] at k1
  have k3 := mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero _ _) (mul_right_cancel₀ hφ0 k1)
  rw [MonoidHom.inv_apply, ← inv_eq_iff_eq_inv]
  exact Units.ext k3

end GlobalTheory.MixedForm

end
