import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinOrderIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeneratorsCompare

namespace GlobalTheory.RigPullExists

theorem exists_isRigPull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G)
    [IsMonHom f] (k N : ℤ)
    (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![N, -k])) {T : Over S}
    (σ : LB.Sec (LPow G Lr.L k T)) : ∃ σ₁ : LB.Sec (LPow G Lr.L N T), RigidNormaliserGenerators.IsRigPull G Lr f k N σ σ₁ := by
  have h1 := h.pull (snd T G).left
  rw [← fsum_comp] at h1
  obtain ⟨X0, hX0⟩ := h1.gen Lr.isLB (K' := Fin 2) ![(snd T G).left, (snd T G ≫ f).left] ![N, -k] (by
    congr 1
    funext i
    fin_cases i
    · exact (Category.comp_id _).symm
    · rfl)
  have ha : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hu : (ptSecT G (1 : T ⟶ G)).left ≫ (snd T G).left = T.hom ≫ eSec G := NormTheta.ptSec_snd
  have hu' : (ptSecT G (1 : T ⟶ G)).left ≫ (snd T G ≫ f).left = T.hom ≫ eSec G := by
    rw [Over.comp_left, ← Category.assoc, hu, Category.assoc]
    exact congrArg (T.hom ≫ ·) ha
  obtain ⟨α, hα, hn⟩ := exists_normalized_to Lr.isLB _ _ X0 hX0 (fst T G).left (ptSecT G (1 : T ⟶ G)).left
    NormTheta.ptSec_fst _ _ _ (NormTheta.rigT_isGen (T := T) Lr.rigGen (N - k)) (by
      simp only [fsum, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        hu, hu', ← Finsupp.single_add, sub_eq_add_neg])
  obtain ⟨σ₁, hσ⟩ := VVRank.exists_isTwistPull G (ψ := T ◁ f) (hm := whiskerLeft_snd _ _) Lr.isLB hα σ
  exact ⟨σ₁, α, hα, hn, hσ⟩

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F], letI := H.starRing; ∀ (a : 𝓞 E) (N : ℕ), a * star a = (N : 𝓞 E) → 0 < N → ∀ (k : ℕ) (σ : LB.Sec (LPow t.G P.U.LG.L (k : ℤ) (TF (R := V) F))), ∃ σ₁ : LB.Sec (LPow t.G P.U.LG.L ((k * N : ℕ) : ℤ) (TF (R := V) F)), RigidNormaliserGenerators.IsRigPull t.G P.U.LG (t.act.act a) (k : ℤ) ((k * N : ℕ) : ℤ) σ σ₁ := by
  intro V _ _ _ E _ _ _ H t P F _ _ a N hN _ k σ
  letI := H.starRing
  haveI := t.act.hom a
  refine exists_isRigPull P.U.LG (t.act.act a) _ _ ?_ σ
  rw [P.bundle]
  exact PullGenG.hasGen_pull t.PP t.cub t.act.toRingAct H.w0 a N hN (t.adj a) t.prim k

end GlobalTheory.RigPullExists
