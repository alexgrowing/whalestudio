import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RegularEmbeddingsCoverBadEmbeddingLocus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankGrowthBoundSmallScale
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftsOfFour
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.BadEmb
section Abstract
variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)
end Abstract
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end General
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weights
set_option maxHeartbeats 1000000 in
theorem regular_embeddings_cover_bad_embedding_locus_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), Pb.comap π = grpHR fr → (∀ k, (H k).comap π = grpGHR fr k) → (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) → ∀ k : Fin 2, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 3 / 2 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
  intro hX hP hGD hQ hS hT hSA _ hDG hSz hFD hDg hSh
  first
    | have h4 := _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hX hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
    | have h4 := _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
  first
    | have ua0 := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hX hP hGD hQ hS hT hSA
    | have ua0 := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGD hQ hS hT hSA
  first
    | have sg := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hX hP
    | have sg := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP
  have h3 := _root_.GlobalTheory.T.size_bounds_for_family_alt hSz
  unfold _root_.GlobalTheory.CovTop.DeepGoodness _root_.GlobalTheory.CovTop.CoversCondition at hDG
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h3 h4 ⊢
  refine _root_.GlobalTheory.BadEmb.lifts_of_four_quantitative_conditions hDG _root_.GlobalTheory.T.weight_conditions_at_index' h3 h4 ?_
  clear hDG h3 h4
  intro eps Fm x hx ι p i PP _ _ _ _ b1 b2 b3 b4 hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  have g0 := (b1 hi Y hY).1
  have gm := (b1 hi Y hY).2.1
  have hL := (b2 hi).1
  have hp1 := (b2 hi).2.1
  have hq1 := (b2 hi).2.2.1
  have hf := (b2 hi).2.2.2.1
  have hj := (b2 hi).2.2.2.2.1
  have hn := (b2 hi).2.2.2.2.2.1
  have hs := (b2 hi).2.2.2.2.2.2.2.2
  have he := (b3 hi Y hY).2.2.2.2.2.2.1
  have hg := (b3 hi Y hY).2.2.2.2.2.2.2.1
  have hrk := b4 hi Y hY 2 one_le_two le_rfl
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hs1 := hs _ (Or.inr (Or.inr rfl))
  have ec : ((2 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) =
      cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1) := by push_cast; ring
  rw [ec] at hrk
  have g2 : Y.GoodAt (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    sg _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
      (fun τ => by
        rw [add_smul, ← add_assoc]
        exact antitone_add_hodge _ _ τ (hs1.1 τ) hc0)
      (fun τ => by
        rw [add_smul, ← add_assoc, gap_add_hodge _ hp1 hq1]
        exact le_add_of_le_of_nonneg (hs1.2 τ) hc0)
  have ua := ua0 _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 he hg fr
  have hr : (Y.rk (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤
      3 / 2 * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
    refine hrk.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact (add_le_add_right (min_le_left _ _) _).trans (by norm_num)
  exact embReg_deep hL hp1 hq1 hf hj Y hY.1 _ _ hn _ g0 gm g2 (3 / 2) (by norm_num) hr _ _
    (ua _ (Or.inl hPb)) (ua _ (Or.inr ⟨k, hH k⟩)) ρ χ lamb hρ
end GlobalTheory.BadEmb
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), Pb.comap π = grpHR fr → (∀ k, (H k).comap π = grpGHR fr k) → (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) → ∀ k : Fin 2, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 3 / 2 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
  first | exact @_root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt | exact _root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt | (intros; apply _root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt <;> assumption)
end
end
