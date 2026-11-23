import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftUniqueAndBaseDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateLift_unique_and_baseDatum : (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field
    Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁'
    : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j'
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L
    i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) →
    ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D
    i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP
    : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω'
    : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D
    i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io'
    : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP'
    : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext
    ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T
    : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁
    : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i
    A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i
    A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ
    : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW
    i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A :=
    A) σ g • R.gW i σ g y) v) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R
    : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) +
    1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i
    σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O
    i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f
    : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ)
    : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f)) ∧ (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra
    T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O
    i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i
    (sg0 D
    A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n
    : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O
    i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k
    : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D
    A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k))) := by
  first | exact @GlobalTheory.GalLift.lift_and_base_five | exact GlobalTheory.GalLift.lift_and_base_five | (intros; apply GlobalTheory.GalLift.lift_and_base_five <;> assumption)
