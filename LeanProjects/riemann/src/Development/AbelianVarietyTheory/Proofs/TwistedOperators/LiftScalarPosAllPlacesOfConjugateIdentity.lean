import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.PosScalRed

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

private theorem eq_zero_of_semilinear_eq_zero_of_linearIndependent {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (f : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => f (b k)) (z : V)
    (hz : f z = 0) : z = 0 := by
  classical
  have hsum : Finsupp.linearCombination ℂ (fun k => f (b k)) ((b.repr z).mapRange σ (map_zero σ)) = f z := by
    conv_rhs => rw [← b.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by intros; simp), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
  have h0 := linearIndependent_iff.mp hli _ (hsum.trans hz)
  have hc : b.repr z = 0 := by
    ext k
    have := congrArg (fun g => g k) h0
    simpa using this
  exact b.repr.map_eq_zero_iff.mp hc

theorem jL_eq_zero (hK : X.KFormL) (j : Bs.J) (t : Bs.Tup) (z : A.FL j t) (hz : X.jL j t z = 0) : z = 0 := by
  obtain ⟨hli, -⟩ := hK j t
  exact eq_zero_of_semilinear_eq_zero_of_linearIndependent _ (X.jL j t) _ hli z hz

private theorem exists_rational_solution_of_semilinear {K E : Type*} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {d N : ℕ}
    (f : (Fin d → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (ψ : Fin N → Module.Dual ℂ E)
    (hψ : ∀ e, (∀ i, ψ i e = 0) → e = 0) (hA : ∀ i l, ψ i (f (Pi.single l 1)) ∈ Set.range σ)
    (y : Fin d → ℂ) (hy : ∀ i, ψ i (f y) ∈ Set.range σ) : ∀ l, y l ∈ Set.range σ := by
  classical
  choose a ha using hA
  choose c hc using hy
  have key : ∀ (z : Fin d → ℂ) (i : Fin N), ψ i (f z) = ∑ l, σ (a i l) * z l := by
    intro z i
    have hz : z = ∑ l, z l • Pi.single l (1 : ℂ) := by
      ext m; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hz]
    simp only [map_sum, map_smul, ← ha, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hinj : LinearMap.ker (Matrix.of a).mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h1 : f (fun l => σ (z l)) = 0 := by
      apply hψ
      intro i
      rw [key]
      have hzi := congrFun hz i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hzi
      calc ∑ l, σ (a i l) * σ (z l) = σ (∑ l, a i l * z l) := by simp [map_sum, map_mul]
        _ = 0 := by rw [hzi, map_zero]
    have h2 := hf (h1.trans (map_zero f).symm)
    funext l
    have := congrFun h2 l
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.of a).mulVecLin hinj
  have hg' : ∀ z, g ((Matrix.of a).mulVec z) = z := fun z => by
    have := congrArg (fun F => F z) hg
    simpa using this
  have hBA : LinearMap.toMatrix' g * Matrix.of a = 1 := by
    ext i j
    have := congrFun (hg' (Pi.single j 1)) i
    rw [← LinearMap.toMatrix'_mulVec g] at this
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply] using this
  have hAy : ((Matrix.of a).map σ).mulVec y = fun i => σ (c i) := by
    funext i
    rw [hc i, key]
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hy' : y = ((LinearMap.toMatrix' g).map σ).mulVec (fun i => σ (c i)) := by
    rw [← hAy, Matrix.mulVec_mulVec, ← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.one_mulVec]
  intro l
  refine ⟨((LinearMap.toMatrix' g).mulVec c) l, ?_⟩
  rw [hy']
  simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem liftMat_inj (hK : X.KFormL) (hZ : X.CrdZL cr b) (hT : Formalism.IndefR.Rat.LiftTestB X b) (hKF : X.KForm b)
    (hEW : X.EWnorm b) (hnP : 0 < X.nP b) (j : Bs.J) (t : Bs.Tup) (hinjL : Function.Injective (cr.toL X.zs b j t))
    (hcol : ∀ k, X.tC cr b j t (Pi.single k 1) ∈ LinearMap.range (X.w0C b j))
    (x : Fin ((lv (fc X.zs) b).dZ j t) → K) (hx : (X.liftMat cr b j t).mulVec x = 0) : x = 0 := by
  classical
  have hw0 : Function.Injective (X.w0C b j) := by
    have h1 : Function.Injective (X.wC b j Bs.v0) := Formalism.IndefR.Rat.lin_injective _ (hKF j Bs.v0).1
    have h2 : Function.Injective (X.eW b j) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have he := hEW j u u
      rw [hu, inner_zero_left] at he
      have hnP' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnP.ne'
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hnP'
      · exact inner_self_eq_zero.mp h
    intro u u' h
    exact h1 (h2 h)
  obtain ⟨N, ψ, hψ, hψθ, hψw⟩ := hT j
  have hcolM : ∀ k, X.w0C b j (fun l => X.liftMatC cr b j t l k) = X.tC cr b j t (Pi.single k 1) := by
    intro k
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hcol k)
    show X.w0C b j (solve (X.w0C b j) (X.tC cr b j t (Pi.single k 1))) = _
    unfold solve
    rw [dif_pos ⟨y, hy⟩]
    exact (⟨y, hy⟩ : ∃ y, X.w0C b j y = X.tC cr b j t (Pi.single k 1)).choose_spec
  have htC : ∀ z : Fin ((lv (fc X.zs) b).dZ j t) → K,
      X.tC cr b j t (cpt Bs.v0.embedding z) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) := by
    intro z
    rw [CxData.tC_eq, CxData.jL_toL]
  have hrat : ∀ l k, X.liftMatC cr b j t l k ∈ Set.range Bs.v0.embedding := by
    intro l k
    refine exists_rational_solution_of_semilinear _ (X.w0C b j) hw0 ψ hψ (fun i l => hψw i l) (fun l => X.liftMatC cr b j t l k) (fun i => ?_) l
    rw [hcolM k]
    have e1 : (Pi.single k (1 : ℂ) : Fin ((lv (fc X.zs) b).dZ j t) → ℂ) = cpt Bs.v0.embedding (Pi.single k (1 : K)) := by
      ext m; simp [cpt, Pi.single_apply]
    rw [e1, htC]
    exact hψθ t i _
  have hmap : (X.liftMat cr b j t).map Bs.v0.embedding = X.liftMatC cr b j t := by
    ext l k
    simp only [Matrix.map_apply, CxData.liftMat, kMat]
    unfold kOf
    have hr : ∃ a, Bs.v0.embedding a = X.liftMatC cr b j t l k := hrat l k
    rw [dif_pos hr]
    exact hr.choose_spec
  have hlin : ∀ z, X.tC cr b j t z = X.w0C b j ((X.liftMatC cr b j t).mulVec z) := by
    have : X.tC cr b j t = (X.w0C b j).comp (X.liftMatC cr b j t).mulVecLin := by
      refine LinearMap.pi_ext fun k c => ?_
      have hs : (Pi.single k c : Fin ((lv (fc X.zs) b).dZ j t) → ℂ) = c • Pi.single k (1 : ℂ) := by
        ext m; simp [Pi.single_apply]
      rw [hs, map_smul, map_smul, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ← hcolM k]
      rfl
    intro z
    rw [this]
    rfl
  have hT0 : X.tC cr b j t (cpt Bs.v0.embedding x) = 0 := by
    rw [hlin]
    have : (X.liftMatC cr b j t).mulVec (cpt Bs.v0.embedding x) =
        cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x) := by
      rw [← hmap]
      ext l
      simp [cpt, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    rw [this, hx]
    have h0 : cpt Bs.v0.embedding (0 : Fin (X.dW b j) → K) = 0 := by ext m; simp [cpt]
    rw [h0, map_zero]
  have hjz : X.jL j t (cr.toL X.zs b j t x) = 0 := by
    have hmem : X.jL j t (cr.toL X.zs b j t x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)) :=
      hZ j t x
    refine Formalism.IndefR.Cx.eq_zero_of_range_adjoint (X.θ' j t) hmem ?_
    rw [← htC]
    exact hT0
  have htoL : cr.toL X.zs b j t x = 0 := jL_eq_zero X hK j t _ hjz
  exact hinjL (htoL.trans (map_zero _).symm)

omit [StarRing K] in

theorem pos_of_inner {n : ℕ} (Y : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) (hw : w ≠ 0) (l : ℝ)
    (h : ⟪w, w⟫_ℂ = ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) Y v x x) : 0 < l := by
  have hm : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) Y v x x =
      ((∑ i, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) Y v x i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Formalism.HermitianLatticesTheory.majAt]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | rw [Complex.star_def, Complex.conj_mul']
    | simp [Complex.star_def, Complex.conj_mul']
  have hw2 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hw2, hm, ← Complex.ofReal_mul, Complex.ofReal_inj] at h
  have hpos : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.mpr hw; positivity
  have hs0 : 0 ≤ ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) Y v x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  by_contra hl
  push_neg at hl
  have := mul_nonpos_of_nonpos_of_nonneg hl hs0
  linarith

private theorem mem_iInf_ker_of_eigen {K W G : Type*} [Field K] [AddCommGroup W] [Module ℂ W] [Group G]
    (gW : Representation ℂ G W) (P : Subgroup G) (ψ : P →* Kˣ) (σ : K →+* ℂ) (w : W)
    (hw : ∀ h : P, gW (h : G) w = σ ((ψ h : Kˣ) : K) • w) :
    w ∈ ⨅ h : P, LinearMap.ker (gW (h : G) - σ ((ψ h : Kˣ) : K) • LinearMap.id) := by
  rw [Submodule.mem_iInf]
  intro h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact hw h

end General

set_option maxHeartbeats 1000000 in

theorem posScal_of_galD : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → R.PGEquiv F → R.PPos := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hE hpos0 hGal hU hT hGE
  obtain ⟨hkap, hlam0⟩ := hpos0
  refine ⟨hkap, fun i t p v => ?_⟩
  by_cases hv : v = A3.A.v0
  · subst hv
    exact hlam0 i t p
  rw [hC.scal.tup i t p v hv]
  by_cases hP : R.PartAt F i p v
  swap
  · rw [hC.scal.abs i p v hv hP]
    exact Real.exp_pos _
  obtain ⟨x, hxW, hxm⟩ := hP
  have key := hGal i v hv p x hxW x
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hxm
    simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_zero]
  have hirr := hOk.ok2.irr
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hE).1
  have hcol : ∀ k, (R.toCx3 F).tC F.cr false i A3.A.μ0 (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).w0C false i) := by
    intro k
    rw [GlobalTheory.WType.range_w0C_type R F hOk hC hE hU i]
    have e1 : (R.toCx3 F).tC F.cr false i A3.A.μ0 (Pi.single k 1) = (R.toCx3 F).θ' i A3.A.μ0
        ((R.toCx3 F).jL i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1))) := by
      have hs : (Pi.single k (1 : ℂ) : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → ℂ) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        ext m; simp [cpt, Pi.single_apply]
      rw [hs, CxData.tC_eq, CxData.jL_toL]
      rfl
    rw [e1]
    refine ⟨?_, ?_⟩
    · have h1 := (GlobalTheory.T.goodProjector_unitaryFormsModel_laws R.toRealDat F.lv2 hcore hirr i).2.2.2 A3.A.μ0
        (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).jL i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1))))
      have h2 : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i A3.A.μ0
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).jL i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1)))) ∈
            LinearMap.range (GlobalTheory.Hk3.eH R.toRealDat i) :=
        Submodule.smul_mem _ _ ⟨_, h1⟩
      exact h2
    · rw [typeSubspace]
      refine mem_iInf_ker_of_eigen _ _ _ _ _ fun h => ?_
      have hop : A3.fam3.amb3.opL i A3.A.μ0 (Sum.inr (h : G)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1)) =
          ((F.ψ0⁻¹ h : D.what₂.LLˣ) : D.what₂.LL) • F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1) := by
        have e := Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0)
          ((R.toCx3 F).zs.Zl i A3.A.μ0)
        have m : (A3.A.fam.L i A3.A.μ0).toF (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) (Pi.single k 1) ∈
            LinearMap.range ((A3.A.fam.L i A3.A.μ0).toF (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0)) :=
          ⟨_, rfl⟩
        rw [e] at m
        have m2 := m.2
        rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at m2
        exact Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hirr F.P0 F.ψ0⁻¹ h _ m2
      refine (hGE.2 i A3.A.μ0 (h : G) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 (Pi.single k 1))).symm.trans ?_
      rw [hop, map_smulₛₗ, map_smul]
      rfl
  have hinjL : Function.Injective (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0) :=
    Formalism.L2.DIV.BlockDat.toF_injective _ _ _
  have hM : (R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x ≠ 0 := fun h0 =>
    hx0 (liftMat_inj (R.toCx3 F) F.cr false (RealDat3.kFormL_of (RealDat3.characterisation_of_weak hC hE).models)
      (lift_coordinates_in_subspaces _ false) hT (RealDat3.kForm_of hU false) (RealDat3.ewNorm false)
      (Formalism.IndefR.Links.RealDat.nP_pos false) i A3.A.μ0 hinjL hcol x h0)
  have hw : (R.toCx3 F).wC false i v (cpt v.embedding ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ≠ 0 := by
    intro h0
    have h1 := Formalism.IndefR.Rat.lin_injective _ ((RealDat3.kForm_of hU false) i v).1 (h0.trans (map_zero _).symm)
    apply hM
    funext l
    have := congrFun h1 l
    simpa [cpt] using this
  exact pos_of_inner _ v x _ hw _ key

end GlobalTheory.PosScalRed
