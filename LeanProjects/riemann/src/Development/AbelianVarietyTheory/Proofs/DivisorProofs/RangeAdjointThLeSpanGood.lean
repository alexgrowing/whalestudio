import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjGood

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ E] (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by rw [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ v y, inner ℂ (j (e v)) y = inner ℂ (j v) (U y) := fun v y => by
    have : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v) ∘ₗ U := ext_of_span hsp fun w => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    exact LinearMap.congr_fun this y
  have h3 : LinearMap.adjoint U = U := ext_of_span hsp fun v => by
    refine ext_inner_right ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_left, hU, h2]
  have h4 : LinearMap.range U ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
    rw [LinearMap.range_eq_map, ← hsp, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  refine le_trans ?_ h4
  rw [← h1, LinearMap.adjoint_comp, h3]
  exact LinearMap.range_comp_le_range _ _

theorem model_good_span {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
    (hj : ∀ x, M.e (j x) = P.extL x)
    {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

theorem proj_rows_core {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hC : Core R F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem range_adjoint_Th_le_span_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).goodF A.X : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hG t
  exact model_good_span (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
    (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr
    R.gE (hG t) fun y => proj_rows_core hC _

end GlobalTheory.AdjGood

end
