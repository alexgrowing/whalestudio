import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingConjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

set_option maxHeartbeats 1000000 in

theorem exists_lift_act {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (hchi : ∀ k, Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧
      ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun x v h => ?_⟩
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dif_pos hk]
  simp only [hchi, inv_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem exists_act_eq (hθ : IsInfFam R.θ) (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (y : (R.HW i σ).H) :
    ∃ z, (R.HW i σ).e z = actW R i σ g ((R.HW i σ).e y) := by
  have h1 : (R.HW i σ).e y ∈ R.Wall i σ := (he i σ).2.1 ▸ LinearMap.mem_range_self _ y
  have h2 : actW R i σ g ((R.HW i σ).e y) ∈ R.Wall i σ :=
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) _ h1 _ fun _ => rfl
  rw [← (he i σ).2.1] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {k : GA D (Wc D i)} (hk : ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k))
    {x y : (R.HW i σ).H} {c : ℂ} (h : ∀ h, evAt R i σ v x h = c * evAt R i σ v y (h * k)) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  obtain ⟨z, hz⟩ := exists_act_eq R hθ he i σ g y
  have h4 : (R.HW i σ).e (c • z) = c • actW R i σ g ((R.HW i σ).e y) := by
    rw [← hz]; exact (R.HW i σ).e.map_smul _ _
  have h3 : x = c • z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e (c • z) v h'
    rw [h4]
    exact (h h').trans (congrArg (c * ·) (hk _ v h').symm)
  exact (congrArg (R.HW i σ).e h3).trans h4

theorem chiTop_eq {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end Model

set_option maxHeartbeats 1000000 in

theorem reading_equiv_of_not_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hj : JEvBarAt T R κ i σ hV
  swap
  · rw [top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV hj]
    simp
  obtain ⟨v, hv, h5⟩ := jTop_bar T R κ v₀ hσ hV hj
  have hE := hq _ (good_resC T hσ) hV
  have hchi : ChiIs R i (chiTop R i) := chiTop_eq R fun g' => by
    obtain ⟨k, hk⟩ := hl g'
    obtain ⟨-, y, hy, -⟩ := hE g' k hk 0 (zero_mem _)
    exact ⟨_, by rw [chiC, Units.coe_prod]; exact hy⟩
  obtain ⟨k, hk1, hk2⟩ := exists_lift_act R σ (hl g) (GlobalTheory.TiedUnif.levChi_flag_datWp i)
  obtain ⟨-, y, hy, h2⟩ := hE g k hk1 f f.2
  have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
    D.what₂.embLL.injective ((hchi g).trans (by rw [chiC, Units.coe_prod]; exact hy.symm))
  refine equiv_of_values R hθ he hv hk2 fun h => ?_
  rw [h5, h5]
  show starRingEnd ℂ _ = _ * starRingEnd ℂ _
  rw [hρ, GlobalTheory.TiedUnif.phiC_eq_phiAt, GlobalTheory.TiedUnif.phiC_eq_phiAt, h2, mul_left_comm, hy', map_mul]
  exact congrArg (· * _) (Complex.conj_conj _)

end GlobalTheory.ReadingConjEquiv

end
