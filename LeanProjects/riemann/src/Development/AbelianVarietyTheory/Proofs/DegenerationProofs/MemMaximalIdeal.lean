import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueCombOfIndependentSpecialFibre
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ModelBasis
open GlobalTheory.FieldBaseChange GlobalTheory.IntegralCombination GlobalTheory.ZH GlobalTheory.ZH.AdaptedSpan

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

theorem toGen_injective (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) : Function.Injective (toGen U k) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have h₁ : IsSchemeTheoreticallyDominant (jK V) := h.2
  have h₂ : QuasiCompact (jK V) := h.1
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) := inferInstance
  exact GlobalTheory.ConstFam.pullOver_injective_of_dominant _ _ _ _

theorem chart_sum {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of V)} {M : LB Y} {J : Type} [Fintype J]
    (c : J → V) (x : J → SecOver p M) (j : M.ι) :
    LB.Sec.f (∑ i, c i • x i : SecOver p M) j = ∑ i, resTop _ (scal p (c i)) * LB.Sec.f (x i) j :=
  map_sum (chartLin p M j) (fun i => c i • x i) _

open Classical in

theorem mem_maximalIdeal (hW : WeightIndepSt) (U : UnifPre (maximalIdeal V) D A G) {k : ℕ} {J : Type} [Fintype J]
    (σ : J → SecG U k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (hE : ∀ i, U.ExpandsAt 0 k (σ i) (f i)) (hz : ∀ i i₀, cls i ≠ cls i₀ → f i (cls i₀) = 0)
    (hB : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))) (c : J → V)
    (h : ∀ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (LB.Sec.f (∑ i, c i • σ i : SecG U k) j) = 0) (i₀ : J) :
    c i₀ ∈ maximalIdeal V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨g, hg⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 k (cls i₀) _).1
    (hW V _ D A G U 0 k _ _ h (expandsAt_sum U 0 k σ f hE c) (cls i₀))
  obtain ⟨a, ha, -⟩ := hB i₀ g
  let β : {i // cls i = cls i₀} → SecAb D.toPre k (cls i₀) := fun i => f i (cls i₀)
  have e₁ : (show SecAb D.toPre k (cls i₀) from g) = ∑ i, a i • β i :=
    SecOver.ext _ _ fun j => (ha j).trans (chart_sum a β j).symm
  have e₂ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) =
      ϖ ^ (0 + 1) • (show SecAb D.toPre k (cls i₀) from g) := SecOver.ext _ _ hg
  have e₃ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) = ∑ i : {i // cls i = cls i₀}, c i • β i := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
        (fun i _ => by rw [hz i i₀ i.2, smul_zero]), add_zero]
  have e₄ : (∑ i : {i // cls i = cls i₀}, c i • β i) = ∑ i, (ϖ ^ (0 + 1) * a i) • β i := by
    rw [← e₃, e₂, e₁, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have e₅ := (hB i₀ (∑ i : {i // cls i = cls i₀}, c i • β i : SecAb D.toPre k (cls i₀))).unique
    (y₁ := fun i => c i) (y₂ := fun i => ϖ ^ (0 + 1) * a i) (fun j => chart_sum _ β j)
    (fun j => by rw [e₄]; exact chart_sum _ β j)
  have e₆ : c i₀ = ϖ ^ (0 + 1) * a ⟨i₀, rfl⟩ := congrFun e₅ ⟨i₀, rfl⟩
  rw [e₆, zero_add, pow_one]
  exact Ideal.mul_mem_right _ _ hϖ.not_isUnit

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f → ∃ σ : Fin r → H0 U.LG.L k, (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧ IsBasisH σ := by
  intro hL V _ _ _ D Q A G _ _ U k hk r cls mu f ⟨⟨_, h₂, h₃, _⟩, h₅, h₆, h₇⟩
  have ex : ∀ i, ∃ σ : SecG U.toUnifPre k, ∀ e, U.ExpandsAt e k σ (f i) := fun i => by
    obtain ⟨s, hs⟩ := h₅ i
    exact GlobalTheory.IntegralExpansion.main hL.1 V D A G U k hk s (f i) hs
  choose σ hσ using ex
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨a, ha⟩ := AdaptedSpan.exists_comb hL.1.globalFns U hk σ cls f h₂ h₃ hσ h₅ h₆ h₇ (toGen U.toUnifPre k s)
  obtain ⟨d, b, hd, hb⟩ := exists_denom a
  have e : (d • (show SecG U.toUnifPre k from s)) = ∑ i, b i • σ i := toGen_injective U.toUnifPre k (by
    rw [map_smulₛₗ, map_sum, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul, hb])
  refine GlobalTheory.SaturatedSections.existsUnique_comb
    (A := fun j => Γ(G.left, (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))).U j))
    (fun j => GlobalTheory.SaturatedSections.cst G.hom _) hϖ
    (fun j x hx => GlobalTheory.SaturatedSections.eq_zero_of_cst_mul G.hom _ hϖ.ne_zero x hx) (fun i j => LB.Sec.f (σ i) j)
    (fun c y hy => mem_maximalIdeal hL.2.2.2.1.weightIndep U.toUnifPre σ cls f (fun i => hσ i 0)
      (fun i i₀ h => SecOver.ext _ _ fun j => h₆ i (cls i₀) (fun m hm => h (h₂ i₀ i ⟨m, hm⟩).symm) j) h₇ c
      fun j => ?_) s.f d b hd fun j => ?_
  · refine (GlobalTheory.ThickDiv.app_eq_zero_iff hϖ G 0 _ _).2 ⟨y j, ?_⟩
    rw [zero_add, pow_one]
    exact (chart_sum c σ j).trans (hy j).symm
  · exact (congrArg (fun t : SecG U.toUnifPre k => LB.Sec.f t j) e).trans (chart_sum b σ j)

end GlobalTheory.OneBasis.ModelBasis
end
