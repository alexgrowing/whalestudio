import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.JetBase

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

variable {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]

theorem map_pairP_basis {n : ℕ} (lam : ι → DomWeight n) (i j : VVIdx lam) :
    σ (pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVVfun K lam i) (bVVfun K lam j)) =
      pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (map σ (bVVfun K lam i)) (map σ (bVVfun K lam j)) := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  have e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q := by
    rw [hQ, MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  have e2 : σ (extNorm K lam) = extNorm ℂ lam := by
    rw [pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  rw [pairP_apply, pairP_apply, pb_gramTw_one, pb_gramTw_one, pb_blockAct_one_tr, pb_blockAct_one_tr, fockL_apply, fockL_apply,
    map_mul, map_div₀, map_one, e2]
  congr 1
  rw [e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]

theorem sqAt_eq {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) (y : Formalism.L2.DIV.VV ℂ lam)
    (h : (y : Pol ℂ ι n) = map σ (x : Pol K ι n)) : sqAt σ lam x = invNormSq lam y := by
  have hx : (x : Pol K ι n) = ∑ i, (bVV K lam).repr x i • bVVfun K lam i := by
    conv_lhs => rw [← (bVV K lam).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  have hy : (y : Pol ℂ ι n) = ∑ i, σ ((bVV K lam).repr x i) • map σ (bVVfun K lam i) := by
    rw [h]
    conv_lhs => rw [hx]
    simp only [map_sum, smul_eq_C_mul, map_mul, map_C]
  unfold sqAt invNormSq
  congr 1
  rw [pairK_apply, hy]
  simp only [pairK_apply, bVV_coe, map_pairP_basis, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {a b : ℕ}

omit [StarRing K] in

theorem degAt_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ)
    (hμ : μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ lastEntry (nu τ))).support) (τ : ι) :
    ((degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ : ℕ) : ℤ) = ∑ i, (nu τ).w i := by
  classical
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ
    (GlobalTheory.JetDeg.sharp_hom (fun τ => lastEntry (nu τ)) τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  have hd : degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ = Finsupp.weight (GlobalTheory.JetDeg.derW a b τ) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, degAt, Finset.sum_filter,
      Finset.sum_subset (Finset.subset_univ _)]
    · simp [GlobalTheory.JetDeg.derW]
    · intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk]
      simp
  rw [hd, h]
  push_cast
  obtain ⟨h0, ⟨s', hs'⟩, -⟩ := hw τ
  have e : ∀ i, (nu τ).w i = ((lam τ).natW i : ℤ) + lastEntry (nu τ) := fun i => by
    have hi := i.2
    have ha : 0 < a := by omega
    rw [GlobalTheory.JetDeg.natW_cast, lastEntry, DomWeight.detShift, DomWeight.detShift, dif_pos ha, dif_pos ha,
      Int.toNat_of_nonneg (h0 _), hs', hs']
    ring
  simp [e, Finset.sum_add_distrib, mul_comm]

omit [StarRing K] in

theorem map_jetMap_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ)
    (hJ : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    map σ (jetMap J (fun τ => lastEntry (nu τ)) P) = jetMap J' (fun τ => lastEntry (nu τ)) (map σ P) := by
  have hdet : ∀ τ : ι, map σ (frDet K a τ) = frDet ℂ a τ := fun τ => by
    rw [GlobalTheory.JetPoint.map_frDet, frDet]
    simp only [map_X]
  rw [GlobalTheory.GO.map_jetMap σ J J' 1 _ P fun μ hμ => by
    rw [one_mul]; exact hJ _ (degAt_eq lam nu lam' hw P hP μ hμ), one_smul]
  simp [jetMap, hdet]

end GlobalTheory.JetBase

theorem GlobalTheory.coefOpLe_jetOp_of_opNormSqLe : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  intro K _ _ _ σ ι _ a b lam nu lam' hw hK hC J J' hJ t ht x
  have h := ht ⟨MvPolynomial.map σ (x : Pol K ι a), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ lam' _ _ ?_) h
  rw [GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hC _ _ (Subtype.prop _)), GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hK _ _ x.2)]
  exact (GlobalTheory.JetBase.map_jetMap_eq σ lam nu lam' hw J J' hJ _ x.2).symm

end
