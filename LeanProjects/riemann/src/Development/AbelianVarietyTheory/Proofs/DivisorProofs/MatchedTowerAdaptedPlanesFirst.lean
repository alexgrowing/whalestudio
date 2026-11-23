import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTowerDescentAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.LiftConst

open GlobalTheory.ThK.SplitInv

namespace GlobalTheory.ThK.SplitAdm

open GlobalTheory.ThK.TowerInt GlobalTheory.ThK.CoinvFin GlobalTheory.SplitUnitLift

theorem smAdm_lift : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F (sp i).J)) (Fin a' × Fin (d₁ - 2 * i)),
        (∀ x : Matrix (Fin a') (Fin (d₁ - 2 * i)) E, ∃ y z : Fin a' × Fin (d₁ - 2 * i) → F,
          co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ om₁ : UA σ G.V'.J × UA σ (sp i).J →* Module.End ℂ ((Fin a' × Fin (d₁ - 2 * i) → AF F) → ℂ),
        IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F (sp i).J) co X.α (X.α / X.β) om₁ →
      ∀ Φ ∈ schA F (Fin a' × Fin (d₁ - 2 * i)), ∀ (μ : Measure (UA σ (sp i).J)) (𝓕 : Set (UA σ (sp i).J)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ (sp i).J) 𝓕 μ →
      ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T → SplitsFully E v → ∃ 𝒦 : Set (Subgroup (UA σ G.V'.J)), SmAdm (UAtSub σ G.V' (evFin F v)) (liftSpace (X := G.V') (W := sp i) om₁ Φ μ 𝓕 f v) 𝒦 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi f hf _ hdec
    co hco om₁ hom Φ hΦ μ 𝓕 hμ h𝓕
  have hT := hM.triple
  have hB := hT.base
  obtain ⟨hfc, hfr⟩ := GlobalTheory.ThK.DescB.Nondeg.lev_reg hKP hM hH' hiso c hb0 hbj i hi f hf

  have hHe : IsHecke F E (X.α / X.β) :=
    ⟨hT.chars.heckeα.1.div' hT.chars.heckeβ.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeα.2 x, hT.chars.heckeβ.2 x, div_one]⟩
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (a + a') := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, hT.chars.resα x, hT.chars.resβ x]
    split_ifs
    · simp
    · rcases neg_one_pow_eq_or ℂ a with e | e <;> simp [pow_add, e, div_neg]
  have hrk : a + a' = (d₁ - 2 * i) + 2 * (i + 1) := by
    have h1 := hH'.rank
    have h2 := (hiso i hi).1
    omega
  have hres₁ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (d₁ - 2 * i) := fun x => by
    rw [hres x, hrk, pow_add, pow_mul]
    simp
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hB, hT.geo.hV', hT.geo.hW, hT.geo.hM', hT.chars.heckeα, hHe, hT.chars.resα, hres, hT.weil'⟩

  obtain ⟨Z, r₁, s₁, hZ⟩ := GlobalTheory.ThK.SkewChain.skew_chain F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hV' d₁ H' i₀ i₁ sp pl
    G.p hH' hiso i hi
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.ModelEx.model_exists F E σ B hB a' _ G.V' (reJ (sp i) Z) _ _ _ _ hT.geo.hV' hZ
  obtain ⟨om₀, hom₀⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B hB a' _ G.V' (reJ (sp i) Z) _ _ _ _ hT.geo.hV' hZ M₀ hM₀
    X.α (X.α / X.β) hT.chars.heckeα hHe hT.chars.resα hres₁
  have hP₀ : IsPair B M₀ X.α (X.α / X.β) om₀ G.q (a' - G.q) r₁ s₁ :=
    ⟨hB, hT.geo.hV', hZ, hM₀, hT.chars.heckeα, hHe, hT.chars.resα, hres₁, hom₀⟩
  obtain ⟨M₁, om₂, -, -, hco₁, hP₂, -, -⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B a' _ G.V' (reJ (sp i) Z) M₀ _ _ om₀ _ _ _ _ hP₀ co hco
  subst hco₁
  have hP : IsPair B M₁ X.α (X.α / X.β) om₁ G.q (a' - G.q) r₁ s₁ :=
    ⟨hB, hT.geo.hV', hZ, hP₂.good, hT.chars.heckeα, hHe, hT.chars.resα, hres₁, hom⟩

  refine ⟨X.T, fun v hv hs => ?_⟩
  have hcm := hP.base.cm
  obtain ⟨τ⟩ := GlobalTheory.LinWAt.nonempty_emb_of_splitsFully hcm v hs
  have herm : ∀ k l, σ ((sp i).J l k) = algebraMap F E (-1) * (sp i).J k l := fun k l => by
    rw [map_neg, map_one, neg_one_mul]; exact hP.skew.skew k l
  have hJ : IsUnit ((sp i).J.map τ).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact isUnit_det_of_cartan (sp i).J τ (B.emb w).1 Complex.I Complex.I_ne_zero _ (hP.skew.cartan w)
  have hbig : 2 * (G.p + G.q) + 1 < (a - a') / 2 := hM.triple.geo.eBig
  have e : Fin (a - 2 * (i + 1) + a') ≃ Fin (d₁ - 2 * i) := finCongr (by omega)
  exact GlobalTheory.ThK.LiftAdm.smAdm_of_locType (W := reJ (sp i) Z) hKP hP f hfc hfr hdec μ 𝓕 hμ h𝓕 hΦ v τ herm hJ e _ _
    (GlobalTheory.ThK.LiftAdm.locType hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi v ⟨hv, hs⟩ τ hcm
      (-1) herm hJ e f hf)

end GlobalTheory.ThK.SplitAdm

end
