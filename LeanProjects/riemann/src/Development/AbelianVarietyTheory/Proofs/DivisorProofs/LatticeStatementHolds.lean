import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.LatDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def actZ (Dw : Datum H) : 𝓞 E →+* Module.End ℤ Dw.La := (Algebra.lsmul ℤ ℤ Dw.La).toRingHom

theorem actZ_apply (Dw : Datum H) (o : 𝓞 E) :
    actZ Dw o = (LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ :=
  LinearMap.ext fun _ => rfl

theorem finrank_eig (Dw : Datum H) [Module.Finite ℤ Dw.La] [Module.Free ℤ Dw.La] {K : Type} [Field K]
    [Algebra K ℂ] (V : ValuationSubring K) (σ : 𝓞 E →+* V) :
    Module.finrank V (EigenSplit.eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ) = Dw.p + Dw.q := by
  have : FaithfulSMul V K := (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := EigenSplit.flat_of_valuationRing V K
  have hF := EigenSplit.finrank_eigenSub_of_flat (R := V) (R' := K) (ρ := EigenSplit.baseChangeAction V (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction K (actZ Dw)) (f := EigenSplit.extendTensor ℤ V K Dw.La)
    (EigenSplit.extendTensor_equivariant V K (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ V K Dw.La) σ
  have hC := EigenSplit.finrank_eigenSub_of_flat (R := K) (R' := ℂ) (ρ := EigenSplit.baseChangeAction K (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction ℂ (actZ Dw)) (f := EigenSplit.extendTensor ℤ K ℂ Dw.La)
    (EigenSplit.extendTensor_equivariant K ℂ (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ K ℂ Dw.La)
    ((algebraMap V K).comp σ)
  have hT := TensorDet.finrank_eigenSub (E := E) (k := ℂ) (O := ℤ) (M := Dw.La)
    ((algebraMap K ℂ).comp ((algebraMap V K).comp σ)) (RingHom.ext_int _ _)
  have e : TensorDet.rightAction ℂ ℤ (𝓞 E) Dw.La = EigenSplit.baseChangeAction ℂ (actZ Dw) := rfl
  rw [e, hC, hF, Dw.rank] at hT
  exact hT

end GlobalTheory.FlatModel.LatDual

namespace GlobalTheory.FlatModel.LatDual

theorem latSt : LatSt := by
  intro E _ _ _ H Dw l c W p hp hW τ
  classical
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI : Module.IsTorsionFree ℤ Dw.La :=
      Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  haveI : Module.Free ℤ Dw.La := Module.Free.of_basis a
  haveI : Module.Finite ℤ Dw.La := Module.Finite.of_basis a
  set σ : 𝓞 E →+* c.V W := embV c W (conjEmb τ.1) with hσ
  set K := EigenSplit.eigenSub (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ with hK
  haveI : Module.Free (c.V W) K := EigenSplit.free_eigenSub_of_valuationRing _ _
  haveI : Module.Finite (c.V W) K := EigenSplit.finite_eigenSub_of_valuationRing _ _
  have hrk : Fintype.card (Ind Dw τ.1) = Module.finrank (c.V W) K := by
    rw [hK, finrank_eig, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      GlobalTheory.ShFam.Pad.AdmExist.mult_add_mult_conj]
  let b : Module.Basis (Ind Dw τ.1) (c.V W) K := (Module.finBasis (c.V W) K).reindex (Fintype.equivFinOfCardEq hrk).symm
  obtain ⟨Q, hQ⟩ := EigenSplit.exists_isCompl_eigenSub_of_valuationRing (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ
  let pr := Submodule.linearProjOfIsCompl K Q hQ
  let f : Ind Dw τ.1 → (c.V W ⊗[ℤ] Dw.La →ₗ[c.V W] c.V W) := fun i => (b.coord i).comp pr
  have hf : ∀ i j, f i (b j) = if i = j then 1 else 0 := by
    intro i j
    show b.coord i (pr (b j)) = _
    rw [show pr (b j) = b j from Submodule.linearProjOfIsCompl_apply_left hQ (b j), Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  choose y hy using fun m' : Fin N => Dw.unimod.2 (a.coord m')
  let cc : Fin N → Fin N → ℤ := fun m' m => a.repr (y m') m
  have hcc : ∀ m' k, ∑ m, cc m' m * Dw.EF (a m) (a k) = if m' = k then 1 else 0 := by
    intro m' k
    have h0 : Dw.EF (y m') (a k) = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
      calc Dw.EF (y m') (a k) = Dw.EF (∑ m, a.repr (y m') m • a m) (a k) := by rw [a.sum_repr]
        _ = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, cc]
    rw [← h0, hy, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  let tb := Algebra.TensorProduct.basis (c.V W) a
  let T : Ind Dw τ.1 → Fin N → c.V W := fun j m => tb.repr (b j : c.V W ⊗[ℤ] Dw.La) m
  let S : Ind Dw τ.1 → Fin N → c.V W := fun i m => ∑ m', f i (1 ⊗ₜ a m') * (cc m' m : c.V W)
  have hT : ∀ j, ∑ m, T j m ⊗ₜ[ℤ] a m = (b j : c.V W ⊗[ℤ] Dw.La) := by
    intro j
    conv_rhs => rw [← tb.sum_repr (b j : c.V W ⊗[ℤ] Dw.La)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hS : ∀ i k, ∑ m, S i m * ((Dw.EF (a m) (a k) : ℤ) : c.V W) = f i (1 ⊗ₜ a k) := by
    intro i k
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ m', ∑ m, f i (1 ⊗ₜ a m') * (cc m' m : c.V W) * ((Dw.EF (a m) (a k) : ℤ) : c.V W)
        = f i (1 ⊗ₜ a m') * (if m' = k then 1 else 0) := by
      intro m'
      have h2 := congrArg (fun z : ℤ => (z : c.V W)) (hcc m' k)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, h2]
      split_ifs <;> simp
    simp_rw [e, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨N, a, T, S, ?_, ?_, ?_⟩
  · intro i o
    have hm := EigenSplit.mem_eigenSub.1 (b i).2 o
    rw [EigenSplit.baseChangeAction_apply, actZ_apply] at hm
    have e1 : ∑ m, T i m ⊗ₜ[ℤ] (o • a m)
        = ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange (c.V W) (∑ m, T i m ⊗ₜ[ℤ] a m) := by
      simp [map_sum, LinearMap.baseChange_tmul]
    rw [e1, hT, hm, ← hT, Finset.smul_sum]
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  · intro i j
    have e2 : ∑ m, ∑ m', S i m * T j m' * ((Dw.EF (a m) (a m') : ℤ) : c.V W) = f i (b j) := by
      rw [Finset.sum_comm]
      simp_rw [mul_comm (S i _) (T j _), _root_.mul_assoc, ← Finset.mul_sum, hS]
      rw [← hT j, map_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have e3 : T j m' ⊗ₜ[ℤ] a m' = T j m' • ((1 : c.V W) ⊗ₜ[ℤ] a m') := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e3, map_smul, smul_eq_mul]
    rw [e2, hf]
  · intro x hx
    have hxK : x ∈ K := EigenSplit.mem_eigenSub.2 fun o => by
      rw [EigenSplit.baseChangeAction_apply, actZ_apply]; exact hx o
    have e' : x = ∑ i, b.repr ⟨x, hxK⟩ i • (b i : c.V W ⊗[ℤ] Dw.La) := by
      conv_lhs => rw [show x = ((⟨x, hxK⟩ : K) : c.V W ⊗[ℤ] Dw.La) from rfl, ← b.sum_repr ⟨x, hxK⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [e']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hT i⟩)

end GlobalTheory.FlatModel.LatDual
