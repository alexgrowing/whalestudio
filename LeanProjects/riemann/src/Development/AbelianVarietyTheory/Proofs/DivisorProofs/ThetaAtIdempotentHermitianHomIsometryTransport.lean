import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.MixModel
open scoped TensorProduct

namespace GlobalTheory.ThetaAtMove

variable {D : D7}

section Generic

variable {S T S' T' : HSp D}

private def rd (φ : WO S T ≃+ WO S' T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ φ.symm.toEquiv

private theorem rd_apply (φ : WO S T ≃+ WO S' T') (f : WO S T → ℂ) (w : WO S' T') : rd φ f w = f (φ.symm w) := rfl

private theorem rd_symm_apply (φ : WO S T ≃+ WO S' T') (g : WO S' T' → ℂ) (t : WO S T) : (rd φ).symm g t = g (φ t) := rfl

private theorem rd_symm_rd (φ : WO S T ≃+ WO S' T') (g : WO S T → ℂ) : rd φ.symm (rd φ g) = g := by
  funext w; simp [rd_apply]

private theorem rd_rd_symm (φ : WO S T ≃+ WO S' T') (g : WO S' T' → ℂ) : rd φ (rd φ.symm g) = g := by
  funext w; simp [rd_apply]

private theorem heisO_move (ψ : AddChar (AF D.host.F) ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (w₀ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S' T' (φ w₀) (rd φ f) = rd φ (heisO ψ S T w₀ f) := by
  funext w
  simp only [heisO, rd_apply, symplOH, map_add, AddEquiv.symm_apply_apply]
  rw [← hB (φ.symm w) w₀, AddEquiv.apply_symm_apply]

private theorem placeModel_move (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T))
    (Λ' : AddSubgroup (WO S' T')) (c : ℂ) (f₀ : WO S T → ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (hH : ∀ a x, IsHalf a (φ x) ↔ IsHalf a x)
    (hΛ : ∀ x, φ x ∈ Λ' ↔ x ∈ Λ) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm) :
    IsPlaceModel ψ (symplO S' T') (heisO ψ S' T') e Λ' c (rd φ f₀)
      ((rd φ).toLinearMap ∘ₗ Tm ∘ₗ (rd φ).symm.toLinearMap) := by
  have hSB : ∀ Φ', IsSBHalf e Λ' Φ' → IsSBHalf e Λ ((rd φ).symm Φ') := by
    rintro Φ' ⟨h1, k, hk, h2, h3⟩
    refine ⟨fun t ht => (hH e t).1 (h1 _ ht), k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
    · simp only [rd_symm_apply, map_add, map_nsmul]
      exact h2 _ ((hΛ u).2 hu) ((hH e u).2 hue) _
    · have := h3 _ ht
      change k • φ t ∈ Λ' at this
      rw [← map_nsmul] at this
      exact (hΛ _).1 this
  refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
  · have e1 : (rd φ).symm (fun t => Φ' (t + x)) = fun t => (rd φ).symm Φ' (t + φ.symm x) := by
      funext t; simp only [rd_symm_apply, map_add, AddEquiv.apply_symm_apply]
    have hx' : IsHalf e (φ.symm x) := (hH e _).1 (by rwa [AddEquiv.apply_symm_apply])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.trans _ (hSB Φ' hΦ) _ hx', ← heisO_move ψ φ hB, AddEquiv.apply_symm_apply]
  · have e1 : (rd φ).symm (fun t => ψ (symplO S' T' t y) * Φ' t) =
        fun t => ψ (symplO S T t (φ.symm y)) * (rd φ).symm Φ' t := by
      funext t; simp only [rd_symm_apply]; rw [← hB, AddEquiv.apply_symm_apply]
    have hy' : IsHalf (cA D e) (φ.symm y) := (hH _ _).1 (by rwa [AddEquiv.apply_symm_apply])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.modul _ (hSB Φ' hΦ) _ hy', ← heisO_move ψ φ hB, AddEquiv.apply_symm_apply]
  · have e1 : (rd φ).symm (c • halfInd e Λ') = c • halfInd e Λ := by
      funext t
      simp only [rd_symm_apply, Pi.smul_apply, halfInd]
      congr 1
      have key := and_congr (hΛ t) (hH e t)
      by_cases h : t ∈ Λ ∧ IsHalf e t
      · rw [if_pos (key.2 h), if_pos h]
      · rw [if_neg (fun h' => h (key.1 h')), if_neg h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.vac]

private theorem thetaAt_move (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T))
    (Λ' : AddSubgroup (WO S' T')) (c : ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (hH : ∀ a x, IsHalf a (φ x) ↔ IsHalf a x)
    (hΛ : ∀ x, φ x ∈ Λ' ↔ x ∈ Λ) (f₀ Φ f : WO S T → ℂ)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) :
    IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e Λ' c (rd φ f₀) (rd φ Φ) (rd φ f) := by
  have hB' : ∀ x y, symplO S T (φ.symm x) (φ.symm y) = symplO S' T' x y := fun x y => by
    rw [← hB, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hH' : ∀ a x, IsHalf a (φ.symm x) ↔ IsHalf a x := fun a x => by
    rw [← hH, AddEquiv.apply_symm_apply]
  have hΛ' : ∀ x, φ.symm x ∈ Λ ↔ x ∈ Λ' := fun x => by
    rw [← hΛ, AddEquiv.apply_symm_apply]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  refine ⟨⟨_, placeModel_move ψ e Λ Λ' c f₀ φ hB hH hΛ hTm⟩, fun Tn hTn => ?_⟩
  have h2 := placeModel_move ψ e Λ' Λ c (rd φ f₀) φ.symm hB' hH' hΛ' hTn
  rw [rd_symm_rd] at h2
  have h3 := hall _ h2
  rw [h3]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have e1 : (rd φ.symm).symm Φ = rd φ Φ := rfl
  rw [e1, rd_rd_symm]

end Generic

section Concrete

open GlobalTheory.Mem.Isom GlobalTheory.TriMove

variable {S S' T T' : HSp D}

private def sgnIso (ε : Bool) (I : IsoMat S S') : IsoMat (GlobalTheory.Grid.sgn ε S) (GlobalTheory.Grid.sgn ε S') where
  P := I.P
  Q := I.Q
  PQ := I.PQ
  QP := I.QP
  gram := by
    cases ε
    · exact I.gram
    · show Formalism.UG.cT _ I.P * (-S'.gram) * I.P = -S.gram
      rw [Matrix.mul_neg, Matrix.neg_mul, I.gram]

private theorem aP_eq_rat (I : IsoMat S S') : I.aP = rat I.P := rfl

private theorem aQ_eq (I : IsoMat S S') : I.aQ = rat I.Q := rfl

private theorem gram_mul_Q (I : IsoMat S S') : S.gram * I.Q = Matrix.conjTranspose I.P * S'.gram := by
  have h : Matrix.conjTranspose I.P * S'.gram * I.P = S.gram := I.gram
  rw [← h]
  simp only [Matrix.mul_assoc, I.PQ, Matrix.mul_one]

private theorem ginv_mul_Qh (I : IsoMat S S') : S'.gram⁻¹ * Matrix.conjTranspose I.Q = I.P * S.gram⁻¹ := by
  have h2 : S'.gram * I.P = Matrix.conjTranspose I.Q * S.gram := gram_mul_Q I.symm
  calc S'.gram⁻¹ * Matrix.conjTranspose I.Q = S'.gram⁻¹ * (Matrix.conjTranspose I.Q * S.gram) * S.gram⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det S), Matrix.mul_one]
    _ = S'.gram⁻¹ * (S'.gram * I.P) * S.gram⁻¹ := by rw [h2]
    _ = I.P * S.gram⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S'), Matrix.one_mul]

private theorem symplO_eq' (S T : HSp D) (x y : WO S T) :
    symplO S T x y = Algebra.trace (AF D.host.F) (AE D) (HMul.hMul (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T y) x).trace := by
  unfold symplO GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj hO
  congr 1
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, giA, gA, adj, rat, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

private theorem symplO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    symplO S' T' (homMap IS IT x) (homMap IS IT y) = symplO S T x y := by
  have hA : giA S' ⬝ adj IS.aQ = IS.aP ⬝ giA S := by
    rw [aQ_eq, aP_eq_rat, giA, giA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ginv_mul_Qh]
  have hB : adj IT.aP ⬝ gA T' ⬝ IT.aP = gA T := by
    rw [aP_eq_rat, gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul]
    congr 1
    exact IT.gram
  have hA' : ∀ {k : ℕ} (M : Mx D S.rank k), giA S' ⬝ (adj IS.aQ ⬝ M) = IS.aP ⬝ (giA S ⬝ M) := by
    intro k M; rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hB' : ∀ {k : ℕ} (M : Mx D T.rank k), adj IT.aP ⬝ (gA T' ⬝ (IT.aP ⬝ M)) = gA T ⬝ M := by
    intro k M; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB]
  rw [symplO_eq', symplO_eq', homMap_apply, homMap_apply]
  congr 1
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul]
  congr 1
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc, hA', hB']
  rw [Matrix.trace_mul_comm IS.aP]
  simp only [Matrix.mul_assoc, IS.aQ_aP, Matrix.mul_one]

private theorem isHalf_homMap (IS : IsoMat S S') (IT : IsoMat T T') (a : AE D) (x : WO S T) :
    IsHalf a (homMap IS IT x) ↔ IsHalf a x := by
  have key : ∀ {m n : ℕ} (u : Mx D m n), IsHalf a u ↔ a • u = u := fun u =>
    ⟨fun h => by ext i j; exact h i j, fun h i j => congrFun (congrFun h i) j⟩
  have e : a • homMap IS IT x = homMap IS IT (a • x) := by
    rw [homMap_apply, homMap_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [key, key, e, (homMap IS IT).injective.eq_iff]

private theorem latMove_symm (I : IsoMat S S') (L : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    latMove I.symm (latMove I L) = L := by
  rw [latMove, latMove, ← Submodule.map_comp]
  refine (congrArg (fun g => Submodule.map g L) ?_).trans (Submodule.map_id L)
  apply LinearMap.ext
  intro v
  show Matrix.mulVec I.Q (Matrix.mulVec I.P v) = v
  rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]

private theorem homMap_symm_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS.symm IT.symm (homMap IS IT x) = x :=
  (homMap IS IT).symm_apply_apply x

private theorem homMap_gen (IS : IsoMat S S') (IT : IsoMat T T') (x : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    homMap IS IT (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * (Matrix.mulVec IT.P t) i * ∑ k, star ((Matrix.mulVec IS.P s) k) * S'.gram k j) := by
  have e : ∀ {U V : HSp D} (t : Fin V.rank → D.host.E) (s : Fin U.rank → D.host.E),
      (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * U.gram k j) : WO U V) =
        GlobalTheory.AdjLatO.tensM x ((a • Matrix.vecMulVec t (star s)) * U.gram) := by
    intro U V t s
    ext i j
    simp only [GlobalTheory.AdjLatO.tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [e, e, homMap_apply, aP_eq_rat, aQ_eq, GlobalTheory.AdjLatO.rat_mul_tensM, GlobalTheory.AdjLatO.tensM_mul_rat]
  congr 1
  simp only [Matrix.mul_assoc, gram_mul_Q IS]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private theorem homMap_mem_latO (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO S T)
    (hx : x ∈ latO S T (LS : Set _) (LT : Set _) P) :
    homMap IS IT x ∈ latO S' T' (latMove IS LS : Set _) (latMove IT LT : Set _) P := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, hP, a, ha, Matrix.mulVec IS.P s, ⟨s, hs, rfl⟩, Matrix.mulVec IT.P t, ⟨t, ht, rfl⟩, homMap_gen IS IT _ a s t⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

private theorem homMap_mem_latO_iff (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO S T) :
    homMap IS IT x ∈ latO S' T' (latMove IS LS : Set _) (latMove IT LT : Set _) P ↔
      x ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine ⟨fun hx => ?_, homMap_mem_latO IS IT LS LT P x⟩
  have h := homMap_mem_latO IS.symm IT.symm _ _ P _ hx
  rwa [latMove_symm, latMove_symm, homMap_symm_homMap] at h

theorem _root_.GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (e : AE D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ Φ f : WO S T → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.sgn ε S) T) (heisO ψ (GlobalTheory.Grid.sgn ε S) T) e (latO (GlobalTheory.Grid.sgn ε S) T LS LT fun _ => True) 1 f₀ Φ f →
  IsThetaAt ψ (symplO (GlobalTheory.Grid.sgn ε S') T') (heisO ψ (GlobalTheory.Grid.sgn ε S') T') e (latO (GlobalTheory.Grid.sgn ε S') T' (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) fun _ => True) 1 (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f₀) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT Φ) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  intro D ψ ε S S' T T' IS IT e LS LT f₀ Φ f h
  exact thetaAt_move ψ e _ _ 1 (homMap (sgnIso ε IS) IT) (symplO_homMap _ _) (isHalf_homMap _ _)
    (homMap_mem_latO_iff (sgnIso ε IS) IT LS LT _) f₀ Φ f h

end Concrete

end GlobalTheory.ThetaAtMove

end
