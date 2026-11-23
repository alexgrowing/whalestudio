import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjInner

theorem inner_eq_integral {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (c : ℂ)
    (h : ∀ x y, inner ℂ x y = c * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    inner ℂ x y = c * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hd : ∀ z : H, ∃ a, IsMultIP M μ 𝓕 (e z) (e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add] at hs ht
  rw [map_smul] at ht
  have h1 := (ipM_spec M μ 𝓕 _ _ ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩ v v).2
  rw [h, h1, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

theorem conj_integral {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℂ) (hq : starRingEnd ℂ q = q) {a b a' b' : X → ℂ}
    (ha : ∀ g, a g = starRingEnd ℂ (a' g)) (hb : ∀ g, b g = starRingEnd ℂ (b' g)) :
    q * ∫ g, star (a g) * b g ∂μ = starRingEnd ℂ (q * ∫ g, star (a' g) * b' g ∂μ) := by
  rw [map_mul, hq, ← integral_conj]
  congr 2
  funext g
  rw [ha, hb, map_mul]
  rfl

theorem inner_conj_of_span {L W H H' : Type} [Field L] [AddCommGroup W] [Module L W] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : L →+* ℂ) (j : W →ₛₗ[σ] H)
    (j' : W →ₛₗ[(starRingEnd ℂ).comp σ] H') (s : Set W) (hs : Submodule.span L s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ) (x y : W) :
    ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ := by
  have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add, map_add, inner_add_right, inner_add_right, map_add, h1, h2]
    | smul a y _ h1 =>
      rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]
  | zero => simp
  | add x z _ _ h1 h2 => rw [map_add, map_add, inner_add_left, inner_add_left, map_add, h1, h2]
  | smul a x _ h1 =>
    rw [map_smulₛₗ, map_smulₛₗ, inner_smul_left, inner_smul_left, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]

theorem dim_conj {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt W ((starRingEnd ℂ).comp σ) ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  refine Finset.prod_congr rfl fun ρ _ => ?_
  unfold kapAt
  rw [GlobalTheory.ConjEval.lab_conj]

theorem dim_real {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _

set_option maxHeartbeats 1000000 in

theorem inner_conj_of_values {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (he : R.models_HW) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) {v : (R.MW i σ).Vec} {v' : (R.MW i ((starRingEnd ℂ).comp σ)).Vec} (hv : IsUnitV v) (hv' : IsUnitV v')
    {x y : (R.HW i σ).H} {x' y' : (R.HW i ((starRingEnd ℂ).comp σ)).H}
    (hx : ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ v' x' g))
    (hy : ∀ g, evAt R i σ v y g = starRingEnd ℂ (evAt R i _ v' y' g)) :
    ⟪x, y⟫_ℂ = starRingEnd ℂ ⟪x', y'⟫_ℂ := by
  have h1 := inner_eq_integral (R.MW i σ) (R.νW i) (R.fdW i) (R.HW i σ).e _ (he i σ).2.2 v hv x y
  have h2 := inner_eq_integral (R.MW i _) (R.νW i) (R.fdW i) (R.HW i _).e _ (he i _).2.2 v' hv' x' y'
  rw [dim_conj] at h2
  exact h1.trans ((conj_integral _ _ (dim_real _ σ) hx hy).trans (congrArg (starRingEnd ℂ) h2).symm)

set_option maxHeartbeats 1000000 in

theorem inner_reading_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i hE hB hT σ hσ
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := (hT i σ hσ hV).1 (hB i σ hσ hV)
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := fw.evaluates hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R hC.models.HW i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

end GlobalTheory.ConjInner
