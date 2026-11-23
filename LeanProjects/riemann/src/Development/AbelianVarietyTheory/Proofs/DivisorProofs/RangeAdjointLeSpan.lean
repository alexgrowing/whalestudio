import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjSpanLift

open GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem range_adjoint_le_span [FiniteDimensional ℂ H] [FiniteDimensional ℂ E]
    (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by simp only [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ w y, inner ℂ (U y) (j w) = inner ℂ y (U (j w)) := fun w y => by
    have : innerₛₗ ℂ (j w) ∘ₗ U = innerₛₗ ℂ (U (j w)) := ext_of_span hsp fun v => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    have h := LinearMap.congr_fun this y
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at h
    rw [← inner_conj_symm, h, inner_conj_symm]
  have h3 : ∀ y, U y ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := fun y => by
    have hy : y ∈ Submodule.span ℂ (Set.range j) := hsp ▸ Submodule.mem_top
    refine (Submodule.span_le (p := (Submodule.span ℂ (j '' (LinearMap.range e : Set V))).comap U)).2 ?_ hy
    rintro _ ⟨v, rfl⟩
    show U (j v) ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V))
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  rintro _ ⟨u, rfl⟩
  have h4 : innerₛₗ ℂ (U (LinearMap.adjoint Θ u)) = innerₛₗ ℂ (LinearMap.adjoint Θ u) := ext_of_span hsp fun w => by
    simp only [innerₛₗ_apply_apply]
    rw [h2, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hU, hΘ]
  rw [← (ext_inner_right ℂ fun w => LinearMap.congr_fun h4 w : U (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u)]
  exact h3 _

end Linear

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_good_span {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ
      (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

end Pres

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem proj_lifts_core {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hC : Core R F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_
    rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem range_adjoint_lift_le (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hOk : A.fam.Ok s) (hC : Core R F)
    (hG : ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))) (i : Fin D.R.m) (t : T) :
    LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤
      Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).goodF A.X : Set (A.fam.L i t).S.Forms)) :=
  model_good_span (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
    (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t)
    (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
    (R.gW i (sg0 D A)) (hG i t) fun y => proj_lifts_core hC hOk i t y

end GlobalTheory.AdjSpanLift

end
