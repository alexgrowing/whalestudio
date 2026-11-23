import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩

set_option maxHeartbeats 2000000 in
theorem isConjForms_base {F : Face D A} (hC : R.Char F) {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) :
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

theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl

set_option maxHeartbeats 2000000 in
theorem isConjLift_base {F : Face D A} (hC : R.Char F) :
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

theorem isConjDatum_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁ : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i gramR c0R c0L hT hV
  have hg := (overK_iff_good T R F κw v₀ hC fw i (sg0 D A)).1 fun x _ => (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _).symm
  have h1 := fw.chiR i (sg0 D A) hg
  have h2 := h1.2.2.2.2 (congrArg (·.comp (algebraMap T.Q.c.F D.what₂.LL)) (realisation_embedding_eq_baseEmbedding R).symm)
  exact ⟨along (realisation_embedding_eq_baseEmbedding R) (c0L i), along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0),
    ⟨Eq.subst (motive := ChiAt R i (sg0 D A)) h2 h1, isEtaConj_base R hC.lev hV, isConjForms_base R i hC hT,
      isConjLift_base R i hC⟩, fun _ => rfl⟩

end GlobalTheory.GalLift.BaseDatum

end
