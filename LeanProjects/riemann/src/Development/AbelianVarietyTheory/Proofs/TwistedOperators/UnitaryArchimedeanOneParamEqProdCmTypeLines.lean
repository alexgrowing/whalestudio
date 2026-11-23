import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ConjLineSplit

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (conjU continuous_conjU)
open GlobalTheory.ConjUTransport (conjUInv conjEquiv continuous_conjUInv)

theorem exists_lie_eq_exp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous M)
    (h0 : M 0 = 1) (hm : ∀ s t, M (s + t) = M s * M t) (hU : ∀ t, (M t)ᴴ * H * M t = H) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * H + H * Y = 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • Y) = M t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨Y, hY⟩ := GlobalTheory.banach_oneParamGroup_eq_exp M hc h0 hm
  refine ⟨Y, ?_, hY⟩
  have hd : HasDerivAt M Y 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul, funext hY] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by rw [Matrix.conjTranspose_smul]; simp }
  have hT : HasDerivAt (fun t => (M t)ᴴ) Yᴴ 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const H).fun_mul hd
  rw [funext hU] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) H)
  rwa [h0, Matrix.conjTranspose_one, mul_one, one_mul] at huniq

variable {D : D7}

theorem finTens_eq_zero {z : AE D} (h : ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 → u • z = 0) :
    GlobalTheory.LFun.finTens D.host.F D.host.E z = 0 := by
  let e : AF D.host.F := ((0, 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
  have he : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F e = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := congrArg (GlobalTheory.LFun.finTens D.host.F D.host.E) (h e he)
  rw [Algebra.smul_def, map_mul, map_zero] at h1
  have h2 : GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) e) = 1 := rfl
  rwa [h2, one_mul] at h1

theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig) u z

theorem smul_cA_sub (u : AF D.host.F) {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) (i j : Fin n) :
    (u • (A.map (cA D) - 1)) i j = cA D ((u • (A - 1)) i j) := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, cA_smul, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem conjU_mem_UAt_iff (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram) (g : GA D W) :
    conjU W 1 hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) ↔ g ∈ GinfC W := by
  have hone : ∀ a b : Fin W.rank, GlobalTheory.LFun.finTens D.host.F D.host.E ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) a b) =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    show finHom W g = 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : GlobalTheory.LFun.finTens D.host.F D.host.E ((Formalism.L2.Theta.mt W g - 1) a b) = 0 := by
      refine finTens_eq_zero fun u hu => ?_
      have h2 : (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0 := congrFun (congrFun (h u hu) a) b
      rw [smul_cA_sub] at h2
      have h3 := congrArg (cA D) h2
      rw [Formalism.L2.Theta.cA_cA, map_zero] at h3
      exact h3
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero] at h1
    exact h1
  · intro hg u hu
    have hf : finHom W g = 1 := hg
    refine Matrix.ext fun a b => ?_
    show (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0
    rw [smul_cA_sub, Matrix.smul_apply, GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu, map_zero]
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero]
    exact congrArg (fun k : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf

theorem ext_of_infMat {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g h : GA D W} (hg : g ∈ GinfC W) (hh : h ∈ GinfC W)
    (e : ∀ τ, infMat D.sp.cm.sig W.gram (θ τ) g = infMat D.sp.cm.sig W.gram (θ τ) h) : g = h := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have a : (finHom W g).1 = (finHom W h).1 := by
    rw [show finHom W g = 1 from hg, show finHom W h = 1 from hh]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)))
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun a i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (e τ) i) j

open Classical in

theorem infMat_prod {θ : InfFam D} (W : HSp D) (m : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : D.what₂.Tau → GA D W) (hx : ∀ τ, IsAtTau θ W τ (m τ) (x τ)) (τ : D.what₂.Tau) (l : List D.what₂.Tau)
    (hl : l.Nodup) : infMat D.sp.cm.sig W.gram (θ τ) (l.map x).prod = if τ ∈ l then m τ else 1 := by
  induction l with
  | nil => simpa using GlobalTheory.PointAtPlaceHom.infMat_one W (θ τ)
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, ih hl.2]
    by_cases c : τ = a
    · subst c
      rw [(hx τ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hx a).2.2 τ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem exists_eq_prod_oneP {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (g : ℝ → GA D W) (hc : Continuous g)
    (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (hg : ∀ t, g t ∈ GinfC W) :
    ∃ Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, Y τ ∈ lieAt W τ) ∧
      ∀ t, g t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => oneP θ W τ (Y τ) t).prod := by
  have h1 : Continuous (matHom W) := continuous_subtype_val
  choose Y hY hexp using fun τ => exists_lie_eq_exp (gramAt D W τ) (fun t => infMat D.sp.cm.sig W.gram (θ τ) (g t))
    (continuous_matrix fun i j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp
      ((Units.continuous_val.comp (h1.comp hc)).matrix_elem i j))
    (by rw [h0, GlobalTheory.PointAtPlaceHom.infMat_one]) (fun s t => by rw [hm, GlobalTheory.PointAtPlaceHom.infMat_mul])
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W (g t) τ)
  refine ⟨Y, hY, fun t => ext_of_infMat hθ W (hg t) ?_ fun τ => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ _
  · rw [infMat_prod W _ _ (fun τ' => GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hY τ') t) τ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ τ)), hexp]

theorem line_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  intro D θ hθ W Wd hJ γ hγ
  let φ := conjEquiv W 1 one_ne_zero hJ
  obtain ⟨Y, hY, hprod⟩ := exists_eq_prod_oneP hθ W (fun t => φ.symm (γ (Multiplicative.ofAdd t)))
    ((continuous_conjUInv W 1 one_ne_zero hJ).comp (hγ.1.comp continuous_ofAdd))
    (by rw [ofAdd_zero, map_one, map_one]) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    (fun t => (conjU_mem_UAt_iff W Wd hJ _).1 (by
      have e : conjU W 1 hJ (φ.symm (γ (Multiplicative.ofAdd t))) = γ (Multiplicative.ofAdd t) := φ.apply_symm_apply _
      rw [e]
      exact hγ.2 _))
  let p : D.what₂.Tau → (Multiplicative ℝ →* GA D W) := fun τ =>
    { toFun := fun t => oneP θ W τ (Y τ) (Multiplicative.toAdd t)
      map_one' := GlobalTheory.Mem.Lift.oneP_zero hθ
      map_mul' := fun s t => GlobalTheory.Mem.Lift.oneP_add hθ (hY τ) _ _ }
  refine ⟨Y, fun τ => φ.toMonoidHom.comp (p τ), hY, fun τ => ⟨?_, fun t => ?_⟩, fun τ t => rfl, fun t => ?_⟩
  · exact (continuous_conjU W 1 hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ (hY τ)).comp continuous_toAdd)
  · exact (conjU_mem_UAt_iff W Wd hJ _).2 (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)
  · have e := congrArg φ (hprod (Multiplicative.toAdd t))
    rw [φ.apply_symm_apply, map_list_prod, List.map_map] at e
    exact e

end GlobalTheory.ConjLineSplit

end
