import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinBumpAdj

variable {D : D7}

theorem infPart_conj_eq_zero {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  rw [e, h, map_zero]

theorem adj_fin {m n : ℕ} {x : Mx D m n} (h : x.map (infPart D) = 0) : (adj x).map (infPart D) = 0 := by
  funext i j
  exact infPart_conj_eq_zero (a := x j i) (congrFun (congrFun h j) i)

theorem smul_fin {m n : ℕ} (c : AE D) {x : Mx D m n} (h : x.map (infPart D) = 0) : (c • x).map (infPart D) = 0 := by
  funext i j
  show infPart D (c * x i j) = 0
  rw [map_mul, show infPart D (x i j) = 0 from congrFun (congrFun h i) j, mul_zero]

theorem continuous_smul_mx {X : Type} [TopologicalSpace X] {m n : ℕ} (c : AE D) {f : X → Mx D m n} (hf : Continuous f) :
    Continuous fun x => c • f x :=
  continuous_matrix fun i j => continuous_const.mul (hf.matrix_elem i j)

variable (S : HSp D) (σ : ℕ)

def adjMap : Mx D S.rank σ →+ Mx D σ S.rank where
  toFun y := incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add]

def adjInv (η : Mx D σ S.rank) : Mx D S.rank σ := incA D D.host.xi0 • (giA S ⬝ adj η)

theorem adjMap_apply (y : Mx D S.rank σ) : adjMap S σ y = incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) := rfl

theorem adjInv_adjMap (y : Mx D S.rank σ) : adjInv S σ (adjMap S σ y) = y := by
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, giA_gA_cancel, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul]

theorem adjMap_adjInv (η : Mx D σ S.rank) : adjMap S σ (adjInv S σ η) = η := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    have h1 := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
    rw [map_mul, map_one, GlobalTheory.DualPairCheck.cA_cA] at h1
    rw [mul_comm, h1]
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_giA, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one, smul_smul, h, one_smul]

theorem continuous_adjMap : Continuous (adjMap S σ) :=
  continuous_smul_mx _ (f := fun y : Mx D S.rank σ => (adj y ⬝ gA S : Mx D σ S.rank))
    (continuous_adj.matrix_mul continuous_const)

theorem continuous_adjInv : Continuous (adjInv S σ) :=
  continuous_smul_mx _ (f := fun η : Mx D σ S.rank => (giA S ⬝ adj η : Mx D S.rank σ))
    (continuous_const.matrix_mul continuous_adj)

theorem adjMap_fin {y : Mx D S.rank σ} (h : y.map (infPart D) = 0) : (adjMap S σ y).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.zero_mul])

theorem adjInv_fin {η : Mx D σ S.rank} (h : η.map (infPart D) = 0) : (adjInv S σ η).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.mul_zero])

theorem finLat_comap {B : AddSubgroup (Mx D σ S.rank)} (hB : FinLat B) : FinLat (B.comap (adjMap S σ)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← adjInv_adjMap S σ a]
    exact (GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjInv_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hB.fin _ ha)))
  · have e : ((B.comap (adjMap S σ) : AddSubgroup _) : Set (Mx D S.rank σ)) = adjInv S σ '' (B : Set _) := by
      ext a
      constructor
      · intro ha
        exact ⟨_, ha, adjInv_adjMap S σ a⟩
      · rintro ⟨η, hη, rfl⟩
        show adjMap S σ (adjInv S σ η) ∈ B
        rw [adjMap_adjInv]
        exact hη
    rw [e]
    exact hB.cpt.image (continuous_adjInv S σ)
  · obtain ⟨U, hU, h0, hUB⟩ := hB.opn
    refine ⟨adjMap S σ ⁻¹' U, hU.preimage (continuous_adjMap S σ), by rw [Set.mem_preimage, map_zero]; exact h0,
      fun a ha hf => ?_⟩
    exact hUB _ ha ((GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjMap_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 hf)))

theorem exists_bump_adj : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  intro D V₀ W W₀ σ dW B₂ hB y
  obtain ⟨b, hb, hby, -, hs, hp⟩ := exists_bump_le y (B₂.comap (adjMap V₀ σ)) (finLat_comap V₀ σ hB) Set.univ Filter.univ_mem
  refine ⟨fun z => (b z : ℂ), hb, by simp [hby], fun η hη c hc z => ?_, fun z hz => ?_⟩
  · have h1 : dW.pY ⬝ (dW.jY ⬝ adjMap V₀ σ c) = dW.pY ⬝ (dW.jY ⬝ η) := congrArg (fun w : WO V₀ W => dW.pY ⬝ (show Mx D W.rank V₀.rank from w)) hc
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dW.pY_jY, Matrix.one_mul, Matrix.one_mul] at h1
    have h2 : c ∈ B₂.comap (adjMap V₀ σ) := by
      rw [AddSubgroup.mem_comap, h1]; exact hη
    beta_reduce
    rw [hp c h2 z]
  · obtain ⟨r, hr, -, hz'⟩ := hs z (fun h => hz (by simp [h]))
    exact ⟨r, hr, _, hz', rfl⟩

end GlobalTheory.AscFinBumpAdj

end
