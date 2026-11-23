import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped Matrix TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumIdentity

theorem sub_orthProj_perp_mem {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hH : (H.map v0.embedding).PosDef) (N : Submodule K (Fin n → K)) (x : Fin n → K) :
    x - orthProj H (perpOf H N) x ∈ N := by
  have hd : ∀ Z : Submodule K (Fin n → K), Hᴴ = H ∧ IsUnit ((subE Z)ᴴ * H * subE Z).det := fun Z =>
    have k := orthogonal_projection_exists K v0 h0 _ _ H hH (subE Z) (subspace_image_spec K n Z).1
    ⟨k.1, k.2.2.1⟩
  have h1 : ∀ u y : Fin n → K, hform H u y = star u ⬝ᵥ H.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc,
      mul_comm, mul_left_comm]
  have hs : ∀ u y : Fin n → K, hform H u y = 0 → hform H y u = 0 := fun u y e => by
    rw [h1] at e ⊢
    have := congrArg star e
    rwa [star_zero, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, (hd N).1, ← Matrix.dotProduct_mulVec] at this
  set y := x - orthProj H (perpOf H N) x
  have hy : y ∈ perpOf H (perpOf H N) := sub_orthProj_mem_perpOf H _ (hd _).2 x
  have hq : orthProj H N y ∈ N := orthProj_mem H N y
  have hw : y - orthProj H N y ∈ perpOf H N := sub_orthProj_mem_perpOf H _ (hd _).2 y
  have hw' : y - orthProj H N y ∈ perpOf H (perpOf H N) :=
    Submodule.sub_mem _ hy fun z hz => hs _ _ (hz _ hq)
  obtain ⟨a, ha⟩ := (subspace_image_spec K n (perpOf H N)).2.ge hw
  have h2 : ((subE (perpOf H N))ᴴ * H * subE (perpOf H N)).mulVec a = 0 := by
    funext i
    have := hw' _ ((subspace_image_spec K n (perpOf H N)).2.le ⟨Pi.single i 1, rfl⟩)
    rw [← ha, h1, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h3 : a = 0 := by
    rw [← Matrix.one_mulVec a, ← Matrix.nonsing_inv_mul _ (hd (perpOf H N)).2, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  rw [h3, map_zero] at ha
  exact sub_eq_zero.1 ha.symm ▸ hq

theorem lvlE_lvlOp {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) (S : CSD K)
    (hH : (S.H.map v0.embedding).PosDef) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (hr : S.ActGood r)
    (U : Subgroup G) (ψ : U →* Kˣ) (a : MonoidAlgebra K G) (ha : ∀ b, b * a = a * b) (x : Fin (S.lvlDim r U ψ) → K) :
    S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec ((S.lvlOp r U ψ a).mulVec x)) =
      ∑ g, a.coeff g • r g (S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec x)) := by
  rw [Matrix.mulVec_mulVec, (level_operator_spec K v0 h0 S hH G r hr U ψ a (ha _).symm).1, ← Matrix.mulVec_mulVec, CSD.gaMat,
    Matrix.sum_mulVec, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec K S G r g _))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.TraceIncl in

theorem classSum_eOp {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} (h : HidaSetting R i t) {θ} (hθ : OnTies.IsClassSum R i t U ψ ph θ)
    (c : G → D.what₂.LL) {x y : Fin (OnTies.srcDim A i t U ψ) → D.what₂.LL}
    (e : srcForm A i t U ψ y = ∑ g, c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) : θ y = (R.FW i).eOp c (θ x) := by
  rcases subsingleton_or_nontrivial (Fin (R.nW i) → D.what₂.LL) with hs | hs
  · exact Subsingleton.elim _ _
  refine h.eq_of_adForm fun v => ?_
  have e0 : adForm R i ((R.FW i).eOp c (θ x)) = ∑ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) := by
    unfold adForm
    rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e4 : ∀ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) (fun ρ => v ρ) =
      ph • (clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x))) v := fun g => by
    have e1 : adForm R i ((R.FW i).ρ g (θ x)) (fun ρ => v ρ) = sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (adForm R i (θ x) fun ρ => v ρ) :=
      DFunLike.congr_fun ((h.unif i _).2.2 g (θ x)) _
    have e2 : clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
          (clSum (presV R i t) (kern R i t) (srcForm A i t U ψ x) v) :=
      congrFun (h.clSum_equiv g (srcForm A i t U ψ x)) v
    have e3 : sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) = D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) :=
      congrArg (fun s : D.what₂.LL →+* ℂ => s _) (sign_at_base_place_eq_embedding R)
    have e5 : clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        D.what₂.embLL (c g) • clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
      congrFun (LinearMap.map_smulₛₗ _ _ _) v
    have e6 : D.what₂.embLL (c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) * D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) =
        D.what₂.embLL (c g) := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [e5, e2, adForm_smul, MultilinearMap.smul_apply, e1, e3, h.adForm_theta hθ, smul_smul, e6, LinearMap.map_smul, smul_comm]
  have e7 : clSum (presV R i t) (kern R i t) (srcForm A i t U ψ y) v =
      ∑ g, clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
    (congrArg (fun f => clSum (presV R i t) (kern R i t) f v) e).trans
      ((congrFun (map_sum (clSum (presV R i t) (kern R i t)) _ _) v).trans (Finset.sum_apply _ _ _))
  refine (h.adForm_theta hθ y v).trans (((congrArg (fun F => ph • F) e7).trans Finset.smul_sum).trans (Eq.symm ?_))
  exact (DFunLike.congr_fun e0 _).trans ((MultilinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun g _ => e4 g))

section Comparison₂

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem identity_of_tie (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hS : GlobalTheory.TraceIncl.HidaSetting R ι (R.mu v)) {s : ℕ} (hOk : A.fam.Ok s) (hr : ClassSumRational R ι (R.mu v) U ψ ph) :
    O.θ' v i ∘ₗ O.eX v i = O.e i ∘ₗ O.θ' v i ∧
      ∀ x ∈ LinearMap.range (O.eX v i), x - O.pr v i x ∈ LinearMap.ker (O.θ' v i) := by
  have hθy : ∀ x, (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap) (y x) = toForms h fw ι z (O.θ' v i x) := fun x =>
    congrArg (fun a => toForms h fw ι z (O.θ' v i a)) (y.symm_apply_apply x)
  refine ⟨LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_, fun x _ => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, t.e_eOp, ← hθy, ← hθy]
    refine classSum_eOp hS (t.θ'_eq hr) _ ?_
    refine (congrArg (srcForm A ι (R.mu v) U ψ) (LinearMap.congr_fun t.eX_eq x)).trans ?_
    exact lvlE_lvlOp hOk.conj (A.MtCSD ι (R.mu v)) ((hOk.lifts ι (R.mu v)).hpos _) (A.leftGroupActionLift ι (R.mu v)) hS.act U ψ _
      (idempotent_central _ _ A.X hOk.irr).2 (y x)
  · have hpos : (((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ).map A.v0.embedding).PosDef :=
      BlockDat.lf_lvlH_pos (B := A.fam.L ι (R.mu v)) (ℓ := ⟨A.X, U, ψ⟩) ⟨hOk.conj, hOk.irr, hOk.lifts ι (R.mu v)⟩ A.v0
    obtain ⟨a, ha, e⟩ := sub_orthProj_perp_mem hOk.conj hpos ((LinearMap.ker (O.θ' v i)).map y.toLinearMap) (y x)
    have e' : y a = y (x - O.pr v i x) :=
      e.trans ((congrArg (fun b => y x - b) (LinearMap.congr_fun t.pr_eq x).symm).trans (y.map_sub _ _).symm)
    exact y.injective e' ▸ ha

end Comparison₂

attribute [local instance] GlobalTheory.BigOn.runAlg' in

theorem leafIdentity_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → TwistedRational R F (fun _ => 1) → LeafIdentity O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO s hOk hC hU hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1 →
      O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j) := fun v j hr =>
    identity_of_tie (T := (r.used v).full) (inst := inst) (R := R) (ht v j).1
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩ hOk hr
  exact fun w hw => ⟨fun j => key w j (hrat w hw j), fun j => key _ j (by rw [hC.tup.mu_conj w]; exact hrat w hw j)⟩

end GlobalTheory.ClassSumIdentity
