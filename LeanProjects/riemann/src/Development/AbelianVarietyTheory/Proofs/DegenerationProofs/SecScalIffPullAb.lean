import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH.AdaptedSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.PullbackValuation GlobalTheory.IntegralCombination

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

abbrev SecGen (U : UnifPre I D A G) (k : ℕ) : Type :=
  SecOver (R := FractionRing V) (pullback.snd G.hom (jK V))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))

def toGen (U : UnifPre I D A G) (k : ℕ) : SecG U k →ₛₗ[algebraMap V (FractionRing V)] SecGen U k :=
  pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) (pullback.condition : pullback.fst G.hom (jK V) ≫ G.hom = _)
    (fun _ => (Category.comp_id _).symm)

def famAt (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (α : D.X) :
    Fam D F k →ₗ[F] SecAbF D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secScal_iff_pullAb (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.X}
    (s : SecAbF D F k α) (g : SecAb D k α) (r : V) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s (D.famφB α) (DegPre.famε k) g (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ pullAb D F k α g = toF V F r • s :=
  secScal_iff (prB_over D F) (GC.famφ_eq D F α) D.P.isLB s g _ (toF V F)
    ((Over.w (DegPre.prB D F)).symm.trans (prB_over D F)) r

theorem expandsAt_sum (U : UnifPre I D A G) (e k : ℕ) {J : Type} [Fintype J] (σ : J → SecG U k)
    (f : J → ∀ α, SecAb D.toPre k α) (h : ∀ p, U.ExpandsAt e k (σ p) (f p)) (b : J → V) :
    U.ExpandsAt e k (∑ p, b p • σ p : SecG U k) (fun α => (∑ p, b p • f p α : SecAb D.toPre k α)) := by
  have E := (Fintype.equivFin J).symm
  have H := expandsAt_comb U e k (fun p => σ (E p)) (fun p => f (E p)) (fun p => h (E p)) (fun p => b (E p))
  rw [E.sum_comp (fun p => b p • σ p)] at H
  exact (congrArg (U.ExpandsAt e k _) (funext fun α => E.sum_comp (fun p => b p • f p α))).mp H

theorem expands_toGen (U : UnifPre I D A G) (k : ℕ) (τ : SecG U k) (g : ∀ α, SecAb D.toPre k α)
    (s : Fam D.toPre (FractionRing V) k) (hτ : ∀ e, U.ExpandsAt e k τ g)
    (hs : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α s) : U.Expands k (toGen U k τ) s := by
  refine ⟨1, one_ne_zero, τ, g, ?_, fun α => ?_, hτ⟩
  · exact (secScal_iff pullback.condition _ U.LG.isLB _ _ _ (algebraMap V (FractionRing V)) rfl 1).2
      (by rw [map_one, one_smul]; rfl)
  · exact (secScal_iff_pullAb _ _ (famAt D.toPre _ k α s) _ 1).2 (by rw [map_one, one_smul]; exact hs α)

open Classical in

theorem exists_comb (hG : GlobalFnsSt) (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k) {J : Type} [Fintype J]
    (σ : J → SecG U.toUnifPre k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (h₂ : ∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') (h₃ : ∀ α, ∃ i m, α = cls i + k • m)
    (h₄ : ∀ i e, U.toUnifPre.ExpandsAt e k (σ i) (f i))
    (h₅ : ∀ i, ∃ s : Fam D.toPre (FractionRing V) k, FamOf D.toPre _ (f i) s)
    (h₆ : ∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, LB.Sec.f (f i α) j = 0)
    (h₇ : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀)))
    (s : SecGen U.toUnifPre k) : ∃ a : J → FractionRing V, s = ∑ i, a i • toGen U.toUnifPre k (σ i) := by
  obtain ⟨F, ⟨r, hr, τ, g, hτ, hg, hE⟩, -⟩ := (U.expand k hk).1 s
  have hτ' : toGen U.toUnifPre k τ = algebraMap V (FractionRing V) r • s :=
    (secScal_iff pullback.condition _ U.LG.isLB s τ _ (algebraMap V (FractionRing V)) rfl r).1 hτ
  have hg' : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α (toF V (FractionRing V) r • F) := fun α => by
    rw [map_smul]; exact (secScal_iff_pullAb _ _ _ _ r).1 (hg α)
  choose t ht using h₅
  have ht' : ∀ i α, pullAb D.toPre _ k α (f i α) = famAt D.toPre _ k α (t i) := fun i α => by
    have := (secScal_iff_pullAb _ _ (famAt D.toPre _ k α (t i)) (f i α) 1).1 (by
      have e : scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by
        unfold scal; rw [map_one, map_one]
      rw [e]; exact ht i α)
    rwa [map_one, one_smul] at this
  have hb : ∀ c : D.toPre.X, ∃ b : J → V, (∃ i₀, cls i₀ = c) →
      (show SecAb D.toPre k c from g c) = ∑ i, (if cls i = c then b i else 0) • f i c := fun c => by
    by_cases hc : ∃ i₀, cls i₀ = c
    · obtain ⟨i₀, rfl⟩ := hc
      obtain ⟨a, ha, -⟩ := h₇ i₀ (g (cls i₀))
      refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun _ => ?_⟩
      have e : (show SecAb D.toPre k (cls i₀) from g (cls i₀)) =
          ∑ i : {i // cls i = cls i₀}, a i • f i (cls i₀) :=
        SecOver.ext _ _ fun j => (ha j).trans
          (map_sum (chartLin D.toPre.P.A.hom _ j) (fun i : {i // cls i = cls i₀} => a i • f i (cls i₀)) _).symm
      rw [e, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
        Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
          (fun i _ => by rw [if_neg i.2, zero_smul]), add_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [if_pos i.2]; beta_reduce; rw [dif_pos i.2]
    · exact ⟨0, fun h => absurd h hc⟩
  choose b hb using hb
  have key : toF V (FractionRing V) r • F = ∑ i, toF V (FractionRing V) (b (cls i) i) • t i := by
    refine fam_ext fun α j => ?_
    obtain ⟨i₀, m, rfl⟩ := h₃ α
    refine congrArg (LB.Sec.f · j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨m, rfl⟩ ?_)
    refine (hg' _).symm.trans (Eq.trans ?_ (map_sum (famAt D.toPre _ k (cls i₀)) _ _).symm)
    refine (congrArg (pullAb D.toPre _ k (cls i₀)) (hb _ ⟨i₀, rfl⟩)).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, ← ht']
    split_ifs with h
    · rw [h]
    · have z : f i (cls i₀) = 0 := SecOver.ext _ _ (h₆ i _ fun m e => h (h₂ i₀ i ⟨m, e⟩).symm)
      rw [z, map_zero (pullAb D.toPre _ k (cls i₀)), smul_zero, smul_zero]
  have E₁ := expands_toGen U.toUnifPre k τ g _ hE hg'
  have E₂ := expands_toGen U.toUnifPre k _ _ (∑ i, toF V (FractionRing V) (b (cls i) i) • t i)
    (fun e => expandsAt_sum U.toUnifPre e k σ f (fun i => h₄ i e) (fun i => b (cls i) i)) (fun α => by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, map_smul, ← ht'])
  rw [key] at E₁
  have e : toGen U.toUnifPre k τ = toGen U.toUnifPre k (∑ i, b (cls i) i • σ i) :=
    ((U.expand k hk).2 _).unique E₁ E₂
  have hr' : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  refine ⟨fun i => (algebraMap V (FractionRing V) r)⁻¹ * algebraMap V _ (b (cls i) i), ?_⟩
  rw [hτ', map_sum] at e
  rw [← inv_smul_smul₀ hr' s, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul]

end GlobalTheory.ZH.AdaptedSpan
