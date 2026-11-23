import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalRealPlaceScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHyperbolicPlaneResidueStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.SplitUnitLift

namespace GlobalTheory.LocTypeGood

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldAt' {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

theorem notRealPow_of_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ τ : E →ₐ[F] Fv F v, NotRealPow τ X.α X.β := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv τ t ht
  have hnr := GlobalTheory.NuGood.not_root_of_unity F E σ B a a' G X om om' hT v hv τ
  have hdiv : chrW X.ν τ = chrW X.α τ * (chrW X.β τ)⁻¹ := by
    ext x
    simp [Chars.ν, chrW, locChar, div_eq_mul_inv]
  have hval : ((chrW X.ν τ (unifAt v) : ℂˣ) : ℂ) =
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t : ℝ) : ℂ) := by
    rw [hdiv, ht, GlobalTheory.SmGL.val_absPow_ofReal]
  have hn : ‖((chrW X.ν τ (unifAt v) : ℂˣ) : ℂ)‖ = 1 := by
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  have hpos : 0 < GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t :=
    Real.rpow_pos_of_pos (GlobalTheory.SmGL.nabs_pos' _ _) t
  have h1 : GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t = 1 := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hn
    exact hn
  apply hnr 1 one_ne_zero
  apply Units.ext
  rw [zpow_one, hval, h1]
  simp

theorem locType : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ (v : Pl F), X.Good v → ∀ (τ : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (ε : F)
        (herm : ∀ k l, σ ((sp i).J l k) = algebraMap F E ε * (sp i).J k l) (hJ : IsUnit ((sp i).J.map τ).det)
        (e : Fin (a - 2 * (i + 1) + a') ≃ Fin (d₁ - 2 * i)),
        ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i,
          HasLocType hcm τ (sp i).J ε herm hJ e (chrW X.α τ) (chrW X.β τ) f := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi v hv τ hcm ε herm hJ e f hf
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have hsk := GlobalTheory.ThK.DescB.NextStep.skew_sp (p := G.p) hσ B hT.geo.hW.skew hH hiso
  have hgen := notRealPow_of_good F E σ B a a' G X om om' hT v hv τ
  have hreg := GlobalTheory.ThK.DescB.Nondeg.lev_reg hK hM hH hiso c h0 hj
  have hdreg := GlobalTheory.ThK.DescB.Nondeg.diffs_reg hK hM c
  have hrank : a + a' = d₁ + 2 := hH.rank
  let w0 := Classical.arbitrary (InfinitePlace F)
  have hJW : IsUnit (G.W.J.map τ).det :=
    isUnit_det_of_cartan G.W.J τ (B.emb w0).1 Complex.I Complex.I_ne_zero _ (hT.geo.hW.cartan w0)
  have hermW : ∀ k l, σ (G.W.J l k) = algebraMap F E (-1) * G.W.J k l := fun k l => by
    rw [hT.geo.hW.skew k l, map_neg, map_one, neg_one_mul]
  have hJsp : ∀ j < G.p, IsUnit (((sp j).J).map τ).det := fun j hj' =>
    isUnit_det_of_cartan (sp j).J τ (B.emb w0).1 Complex.I Complex.I_ne_zero _ ((hiso j hj').2.2.2.2.2.2.1 w0)
  have hermSp : ∀ j ≤ G.p, ∀ k l, σ ((sp j).J l k) = algebraMap F E (-1) * (sp j).J k l := fun j hj' k l => by
    rw [hsk j hj' k l, map_neg, map_one, neg_one_mul]
  suffices P : ∀ j, j < G.p → ∀ g ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j, ∀ x, x + 2 * (j + 1) = a →
      ∀ (ε : F) (herm : ∀ k l, σ ((sp j).J l k) = algebraMap F E ε * (sp j).J k l) (hJ : IsUnit ((sp j).J.map τ).det)
        (e : Fin (x + a') ≃ Fin (d₁ - 2 * j)), HasLocType hcm τ (sp j).J ε herm hJ e (chrW X.α τ) (chrW X.β τ) g by
    have hbig : 2 * (G.p + G.q) + 1 < (a - a') / 2 := hT.geo.eBig
    exact P i hi f hf (a - 2 * (i + 1)) (by omega) ε herm hJ e
  have hbig : 2 * (G.p + G.q) + 1 < (a - a') / 2 := hT.geo.eBig
  intro j
  induction j with
  | zero =>
    intro _ g hg x hx ε₁ herm₁ hJ₁ e₁
    have hzb : ((a : ℝ) / 2) = (((x + 2 : ℕ) : ℝ) / 2) := by
      rw [← hx] <;> push_cast <;> ring
    rw [lev_zero, hzb] at hg
    have eW : Fin (x + 2 + a') ≃ Fin (a + a') := finCongr (by omega)
    exact GlobalTheory.T.hecke_hyperbolic_plane_residue hK F E σ hcm X.α X.β v τ hgen hT.chars.heckeα hT.chars.heckeβ a' hT.chars.resα (a + a') (d₁ - 2 * 0) G.W (sp 0) H' (by omega) hH.xx hH.yy hH.xy hH.orth hH.gram
      (-1) hermW hJW ε₁ herm₁ hJ₁ x a' eW e₁ (finK σ G.W B.emb) (Diffs B G X om om' R Rf c) hdreg
      (fun f hf => GlobalTheory.T.matched_local_real_place_scaling hK F E σ B a a' G X om om' R Rf hM c v hv τ hcm (-1) hermW hJW (x + 2) (by omega) eW f hf) g hg
  | succ j ih =>
    intro hj1 g hg x hx ε₁ herm₁ hJ₁ e₁
    have hI := hiso j (by omega)
    have hzb : zb a j = (((x + 2 : ℕ) : ℝ) / 2) := by
      unfold zb; rw [← hx] <;> push_cast <;> ring
    rw [lev_succ, hzb] at hg
    have eW : Fin (x + 2 + a') ≃ Fin (d₁ - 2 * j) := finCongr (by omega)
    exact GlobalTheory.T.hecke_hyperbolic_plane_residue hK F E σ hcm X.α X.β v τ hgen hT.chars.heckeα hT.chars.heckeβ a' hT.chars.resα (d₁ - 2 * j) (d₁ - 2 * (j + 1)) (sp j) (sp (j + 1)) (pl j) hI.1 hI.2.1 hI.2.2.1
      hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2.1 (-1) (hermSp j (by omega)) (hJsp j (by omega)) ε₁ herm₁ hJ₁ x a' eW e₁
      (finK σ (sp j) B.emb) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j) (hreg j (by omega))
      (fun f hf => ih (by omega) f hf (x + 2) (by omega) (-1) (hermSp j (by omega)) (hJsp j (by omega)) eW) g hg

end GlobalTheory.LocTypeGood
