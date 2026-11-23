import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModelStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

theorem reading_actG (F : Face D A) (hc : R.Char F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (hinj : EvInj T R v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0)) (g : G) (f : Cu T κw i) :
    ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧
      fw.jK i (sg0 D A) f₁ =
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) := by
  have ht := GlobalTheory.T.lift_equivariance_weil_model R F hc i
  have hk := ht.1 g
  obtain ⟨k, hk⟩ := hk
  have hq := hE g k hk (f : T.R ((i : ℕ) + 1)) f.2
  refine ⟨⟨_, hq.1⟩, rfl, hinj i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (funext fun h => ?_)⟩
  have h1 := ev_base T R κw v₀ fw i hev O ⟨_, hq.1⟩ h
  have h2 := ev_base T R κw v₀ fw i hev O f (h * k)
  have h3 := (ht.2 (sg0 D A)).1 g k hk (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h
  have h4 := (hq.2 h).trans (congrArg (· * _) (hc.grp.chiW i g).symm)
  have h5 := alg_step h1 h4 (h3.trans h2)
  refine h5.trans ?_
  exact (congrFun (congrArg (fun y => y (v₀ i (sg0 D A))) (map_smul (R.HW i (sg0 D A)).e _ _)) h).symm

theorem base_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) :=
  fun T _ R F κw v₀ hc fw i hev hinj O hE g f => reading_actG T R κw v₀ F hc fw i hev hinj O hE g f

end GlobalTheory.GalLift.BaseEquiv

end
