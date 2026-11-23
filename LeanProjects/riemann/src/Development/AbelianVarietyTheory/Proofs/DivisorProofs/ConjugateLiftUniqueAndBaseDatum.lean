import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem act_eq_translation_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i
  exact ⟨fun g => Transl.lifts R i hC.lev (R.eG g), fun σ =>
    ⟨Transl.transl R i hC.models.HW hC.models.gW σ, Transl.proj R i hC.models.gW σ⟩⟩

end GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

set_option maxHeartbeats 2000000 in
theorem isConjForms_base_five {F : Face D A} (hC : GlobalTheory.Core5 R F) {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) :
    IsConjForms R i (sg0 D A) (c0L i) (R.cV i) (along (realisation_embedding_eq_baseEmbedding R) (c0L i)) (R.HV i A.μ0)
      (along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0)) := by
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, hp, -⟩ := h1
  have hχ := GlobalTheory.ConjForms.levChar_mem R hC.lev hC.grp.chiW i
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      ∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v) := fun γ =>
    (GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ⟩
  refine ⟨hC.models.cV i, (hT.mapL i).1, (hT.mapL i).2.1, (hT.mapL i).2.2, fun a b => ?_,
    ⟨_, fun k => (hχ k).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩, hC.models.HV i A.μ0⟩,
    fun x h => ?_⟩
  · exact (pair_val (R.B.L i A.μ0).pres (c0L i) e he (fun v w => pairVr (labLL D) (lamV D i) (gramV D i) v w) hp _ _).trans
      (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _)
  · exact (ext_val (R.B.L i A.μ0).pres (c0L i) e he hact hχ _ h).imp fun v hv =>
      ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv, (congrFun (hC.models.jV i A.μ0 x) h).trans hv⟩
set_option maxHeartbeats 2000000 in
theorem isConjLift_base_five {F : Face D A} (hC : GlobalTheory.Core5 R F) :
    IsConjLift R i (sg0 D A) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) (R.HV i A.μ0) (R.thG i A.μ0) := by
  have h1 := hC.thP.thF i A.μ0
  obtain ⟨thP, h2, h3⟩ := h1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (R.toLevCh.mu A.μ0 ((i : ℕ) + 1))
      (R.toLevCh.mu A.μ0 ((i : ℕ) + 1) * R.eta⁻¹) (R.ωP i A.μ0) := hC.thP.ωP i A.μ0
  rw [mu_base R hC.lev] at hω
  have hio := hC.thP.ioP i A.μ0
  rw [← deltaConj_base R i] at hio
  refine ⟨R.ωP i A.μ0, R.vacP i, R.vP i A.μ0, onb (R.MW i (sg0 D A)), R.ioP i, thP, hω,
    isThPVecOf_empty (places_base R hC.lev) _ (hC.thP.vP i A.μ0),
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ τ _ (hC.models.order i τ), hC.thP.pt_theta i A.μ0, hio, h2, fun x v => ?_⟩
  exact (congrArg (fun w : MMap (R.MW i (sg0 D A)) => w fun ρ => v ρ) (hC.thP.thG i A.μ0 x)).trans
    (congrArg (R.eWf i (sg0 D A)) (h3 x v))

theorem isConjDatum_base_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁ : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i gramR c0R c0L hT hV
  have hg := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hC fw i (sg0 D A)).1 fun x _ => (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _).symm
  have h1 := fw.chiR i (sg0 D A) hg
  have h2 := h1.2.2.2.2 (congrArg (·.comp (algebraMap T.Q.c.F D.what₂.LL)) (realisation_embedding_eq_baseEmbedding R).symm)
  exact ⟨along (realisation_embedding_eq_baseEmbedding R) (c0L i), along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0),
    ⟨Eq.subst (motive := ChiAt R i (sg0 D A)) h2 h1, isEtaConj_base R hC.lev hV, isConjForms_base_five R i hC hT,
      isConjLift_base_five R i hC⟩, fun _ => rfl⟩

end GlobalTheory.GalLift.BaseDatum

namespace GlobalTheory.GalLift.BaseEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem reading_actG_five (F : Face D A) (hc : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (hinj : EvInj T R v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0)) (g : G) (f : Cu T κw i) :
    ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧
      fw.jK i (sg0 D A) f₁ =
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) := by
  have ht := GlobalTheory.GalLift.act_eq_translation_five R F hc i
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

theorem base_equiv_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) :=
  fun T _ R F κw v₀ hc fw i hev hinj O hE g f => reading_actG_five T R κw v₀ F hc fw i hev hinj O hE g f

end GlobalTheory.GalLift.BaseEquiv

namespace GlobalTheory.GalLift.BaseId

theorem base_identity_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hch fw i hev hinj O ph hpins hone h hreps
  have hrk : (Vc D i).rank = (κw i).n :=
    (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans (fw.kap i (D.eTau.symm 1)).2.2.symm
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpf : T.Q.PinField := fw.laws.toLawsM.pins.2.2.1
  have hres : res T (sg0 D A) = (O i).s0 :=
    (congrArg (res T) hs).trans ((res_embLL T fw.alg_eq hpf).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm)
  have hgood : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq hpf
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) hres).trans (O i).hV
  have hfield : ∀ b, inC (O i).c' ((O i).jL b) = D.what₂.embLL b := fun b => RingHom.congr_fun hpins.2.lift.field b
  refine (tie_baseChange (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') (Wc D i) (O i).dict (O i).mu
    (xiR D) (wtA (κw i)) hone.2.1 ()).imp fun z hz => ⟨hz.1, hz.2.elim fun ze hze => hze.1.elim fun ze' hze' => ?_⟩
  have hze'' : D.what₂.embLL ze' = ze := hze'
  refine ⟨ze', hze.2.1.imp fun m hm => ⟨hm.1, D.what₂.embLL.injective
    ((map_pow _ _ _).trans ((congrArg (· ^ m) hze'').trans (hm.2.trans (map_one _).symm)))⟩, fun x₀ => ?_⟩
  refine hreps.elim fun J' hJ => (hJ.2.1 x₀).elim fun x hx => ?_
  refine (hze.2.2 x ((hJ.2.2.2 x).2 ⟨x₀, hx⟩)).elim fun f' h1 => h1.elim fun m h1 => h1.elim fun as h1 => h1.elim fun fs h1 => ?_
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' (as k) := fun k => hpins.1.le (as k).2
  have has' : (fun k => (O i).jL (has k).choose) = as := funext fun k =>
    (inC (O i).c').injective ((hfield _).trans (has k).choose_spec)
  have hfs : ∀ k, fs k ∈ T.cuspA ((i : ℕ) + 1) (wtA (κw i)) (κw i).n := fun k => hrk ▸ h1.2.2.1 k
  refine ⟨m, fun k => (has k).choose, fun k => ⟨fs k, hfs k⟩, ⟨x, f', hx, h1.1, h1.2.1, ?_⟩, fun f₁ hf₁ => ?_⟩
  · exact (congrArg (fun b => IsBC (O i).hle f' b fs) has').mpr h1.2.2.2.1
  have hHW := hch.models.HW i (sg0 D A)
  have hy : R.thF i A.μ0 (jVx R i A.μ0 x₀) ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    hHW.2.1.ge (hch.thP.thF_mem i A.μ0 _)
  refine hy.elim fun y hy => ?_
  refine proj_model (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).e hHW.1
    (fun g => Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) _ (fun g => R.gW i (sg0 D A) g)
    (hch.models.gW i (sg0 D A)) ph y _ _
    ((hch.thP.thG i A.μ0 (jVx R i A.μ0 x₀)).trans (congrArg (postOn _ (R.eWf i (sg0 D A))) hy.symm)) ?_
  refine eq_of_reps (R.HW i (sg0 D A)).e hHW.2.1 (v₀ i (sg0 D A)) (hinj i _ hgood) ph y _ _ fun q => ?_
  have h2 : (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) q.out = (O i).thAd () x q :=
    (congrArg (fun S : MMap (R.MW i (sg0 D A)) => S (v₀ i (sg0 D A)) q.out) hy).trans
      (congrFun (hJ.2.2.1 _ x hx) q).symm
  refine (congrArg (ph * ·) h2).trans ((h1.2.2.2.2 q).trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) ?_ ?_))
  · exact (congrArg₂ (· * ·) hze'' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm
  · refine (phi_cE T R O i (wtA (κw i)) (actG (O i) z (fs k)) q.out).trans ?_
    refine Eq.symm ((congrFun (hev i _ hgood hV (f₁ k)) q.out).trans ?_)
    exact congrFun ((phiC_congr T hres hV (O i).hV _ _).trans
      (congrArg (phiC T (O i).hV (wtA (κw i))) (hf₁ k))) q.out

end GlobalTheory.GalLift.BaseId

namespace GlobalTheory.ConjLiftUnique

set_option maxHeartbeats 1600000 in

theorem lift_unique_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j' : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω' : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io' : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP' : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j c' c₁' H' j' hj hj' ω f₀ f B io thP ω' f₀' f'
    B' io' thP' hL hL'
  have hθ : IsInfFam R.θ := hC.models.inf
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have hV := fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hC.models.BV i τ)
  have h1 := vec_unique (D.sp.V_sig _) (D.sp.W_sig _) hV hc sdV sdW hL.2.1.vec hL'.2.1.vec
  obtain ⟨a, ha, rfl⟩ := h1
  have h2 := exists_isometry (bVV D.what₂.LL (lamV D i)) hj.coef hj'.coef c₁ c₁' hj.indep hj.span hj'.indep hj'.span
    (fun a b => (hj'.pair a b).trans (hj.pair a b).symm) (fun γ hγ => by
      have hγ' := hγ
      unfold GQ HFinIn at hγ'
      obtain ⟨g, -, hg⟩ := hγ'
      exact ⟨_, hj.act ⟨γ, hγ⟩ g hg.symm, hj'.act ⟨γ, hγ⟩ g hg.symm⟩)
  obtain ⟨Φ, p1, p2, p3⟩ := h2
  have hv := hL.2.1.vec
  have hv2 := hv.2
  obtain ⟨e, -, h5⟩ := hv2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hL.1.std hθ h5 hv.1.2.theta
  have h3 := io_unique hL.1 hL'.1 hθ (D.sp.V_sig _) (D.sp.W_sig _) hV hlow.1 hlow.2 hj.coef Φ p2 p3 hf
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv hf) ha hL.2.1.onb hL'.2.1.onb hL.2.2.1 hL'.2.2.1
  obtain ⟨κ, hκ, hk⟩ := h3
  have hinj := rescale_inj (bVV D.what₂.LL (lamV D i)) D.what₂.embLL (c0L i) (hT.mapL i).2.1
  have hb : ∀ x h, H'.e (j' x) h = Φ (H.e (j x) h) := fun x h => by
    have b1 := hj.base x h
    have b2 := hj'.base x h
    obtain ⟨v, q1, q2⟩ := b1
    obtain ⟨v', q1', q2'⟩ := b2
    have q3 : v = v' := hinj (q1.symm.trans q1')
    exact q2'.trans ((congrArg c₁' q3.symm).trans ((p1 v).symm.trans (congrArg Φ q2.symm)))
  exact ⟨κ, hκ, fun x v => thetaP_eq (fun p y => (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hL.1.std _ _ _ _ ω ω' hL.1 hL'.1 p _
    (hL'.2.1.theta y)).symm) Φ hk hL.2.2.2 hL'.2.2.2 _ _
    (fun h => (congrArg (c'.ρ h⁻¹) (hb x _)).trans (p3 _ _).symm) v⟩

end GlobalTheory.ConjLiftUnique

namespace GlobalTheory.GalLift

theorem lift_and_base_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
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
    A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k))) :=
  ⟨GlobalTheory.ConjLiftUnique.lift_unique_five, GlobalTheory.GalLift.BaseDatum.isConjDatum_base_five, GlobalTheory.GalLift.act_eq_translation_five,
    GlobalTheory.GalLift.BaseEquiv.base_equiv_five, GlobalTheory.GalLift.BaseId.base_identity_five⟩

end GlobalTheory.GalLift

end
