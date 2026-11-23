import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralActsEqVolume

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq
open Classical

noncomputable section

namespace GlobalTheory.ArchKX

open GlobalTheory.RealWeil

def IsBddIntertwiner {l : Type} [Fintype l] (M : ℝ) (A' : Sch l →ₗ[ℂ] Sch l) : Prop :=
  (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2) ∧
    ∃ N : (l ⊕ l → ℝ) → (l ⊕ l → ℝ), (∀ w, ‖N w‖ ≤ M * ‖w‖) ∧ ∀ u f, dRho u (A' f) = A' (dRho (N u) f)

example {l : Type} [Fintype l] : IsBddIntertwiner (l := l) 1 LinearMap.id :=
  ⟨fun _ => le_rfl, id, fun _ => by simp, fun _ _ => rfl⟩

theorem exists_seminorm_weylAlg {l : Type} [Fintype l] (M : ℝ) {B : Sch l →L[ℂ] Sch l} (hB : B ∈ weylAlg l) :
    ∃ q : Seminorm ℂ (Sch l), Continuous q ∧ ∀ A', IsBddIntertwiner M A' → ∀ f, ‖schwartzToL2 l (B (A' f))‖ ≤ q f := by
  refine weylAlg_induction (P := fun B => ∃ q : Seminorm ℂ (Sch l), Continuous q ∧
    ∀ A', IsBddIntertwiner M A' → ∀ f, ‖schwartzToL2 l (B (A' f))‖ ≤ q f) ?_ ?_ ?_ ?_ ?_ hB
  · refine ⟨(normSeminorm ℂ (L2 l)).comp (schwartzToL2 l).toLinearMap, continuous_norm.comp (schwartzToL2 l).continuous,
      fun A' hA f => ?_⟩
    have := norm_toLp_le_of_lintegral_le A' 1 ENNReal.one_ne_top (fun f => by rw [one_mul]; exact hA.1 f) f
    simpa [schwartzToL2_apply] using this
  · rintro A w ⟨q, hq, h⟩
    let c : ℝ≥0 := Real.toNNReal (M * ‖w‖)
    refine ⟨∑ a : l ⊕ l, c • q.comp (dRho (Pi.single a 1)).toLinearMap, Seminorm.continuous_finsetSum fun a _ => ?_,
      fun A' hA f => ?_⟩
    · change Continuous fun f => (c : ℝ) * q (dRho (Pi.single a 1) f)
      exact continuous_const.mul (hq.comp (dRho (Pi.single a 1)).continuous)
    · obtain ⟨N, hN, hI⟩ := hA.2
      have e : (∑ a : l ⊕ l, c • q.comp (dRho (Pi.single a 1)).toLinearMap) f =
          ∑ a : l ⊕ l, (c : ℝ) * q (dRho (Pi.single a 1) f) := by
        simp [NNReal.smul_def, smul_eq_mul]
      rw [e, ContinuousLinearMap.mul_apply, hI]
      refine (h A' hA _).trans ?_
      rw [dRho_eq_sum]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [map_smul_eq_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (((norm_le_pi_norm (N w) a).trans (hN w)).trans (Real.le_coe_toNNReal _))
        (apply_nonneg q _)
  · exact ⟨0, continuous_zero, fun A' _ f => by simp⟩
  · rintro A B ⟨q, hq, h⟩ ⟨q', hq', h'⟩
    refine ⟨q + q', hq.add hq', fun A' hA f => ?_⟩
    rw [ContinuousLinearMap.add_apply, map_add]
    exact (norm_add_le _ _).trans (add_le_add (h A' hA f) (h' A' hA f))
  · rintro c A ⟨q, hq, h⟩
    refine ⟨‖c‖₊ • q, ?_, fun A' hA f => ?_⟩
    · change Continuous fun f => ‖c‖ * q f
      exact continuous_const.mul hq
    · rw [ContinuousLinearMap.smul_apply, map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (h A' hA f) (norm_nonneg c)

theorem exists_seminorm_unif {l : Type} [Fintype l] (M : ℝ) (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ (Sch l), Continuous q ∧ ∀ A', IsBddIntertwiner M A' → ∀ f, p (A' f) ≤ q f := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ) p hp
  choose B hB hle using exists_seminorm_le (l := l)
  choose q hq hq' using fun k n r => exists_seminorm_weylAlg M (hB k n r)
  refine ⟨C • ∑ i ∈ s, ∑ r, q i.1 i.2 r, ?_, fun A' hA f => ?_⟩
  · change Continuous fun f => (C : ℝ) * (∑ i ∈ s, ∑ r, q i.1 i.2 r) f
    exact continuous_const.mul (Seminorm.continuous_finsetSum fun i _ => Seminorm.continuous_finsetSum fun r _ => hq _ _ _)
  · refine (hC (A' f)).trans ?_
    change (C : ℝ) * _ ≤ (C : ℝ) * (∑ i ∈ s, ∑ r, q i.1 i.2 r) f
    refine mul_le_mul_of_nonneg_left ?_ C.2
    refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
    have h1 : (∑ r, q i.1 i.2 r) ≤ ∑ i ∈ s, ∑ r, q i.1 i.2 r :=
      Finset.single_le_sum (f := fun i : ℕ × ℕ => ∑ r, q i.1 i.2 r) (fun _ _ => bot_le) hi
    refine le_trans ?_ (h1 f)
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    refine (hle i.1 i.2 (A' f)).trans ?_
    have e : (∑ r, q i.1 i.2 r) f = ∑ r, q i.1 i.2 r f := by simp
    rw [e]
    exact Finset.sum_le_sum fun r _ => hq' _ _ r A' hA f

theorem exists_model_schrF (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type)
    [Fintype κ] :
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ), schrF (trP F κ) (P w) φ ∘ Q = rhoFun w (φ ∘ Q) := by
  let β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ := -Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
  have hβ : ∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a) := by
    intro a
    let z : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)
    have hAt : At (evI F) z := by
      intro c hc
      refine Prod.ext ?_ ?_
      · change c.1 * _ = 0
        rw [GlobalTheory.ArchHeis.fst_eq_zero_of_ev hc, zero_mul]
      · change c.2 * 0 = 0
        rw [mul_zero]
    have he : evI F z = a :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
    change ψ z = _
    rw [hψ.2.2 z hAt, he]
    simp only [β, LinearMap.neg_apply]
    congr 1
    push_cast
    ring
  have hnd : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
    intro a ha
    by_contra h
    push Not at h
    exact ha (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace a fun b => neg_eq_zero.1 (h b))
  obtain ⟨n, Q, P, h⟩ := GlobalTheory.WeilAdm.RealModel.exists_model F ψ β hβ hnd κ
  refine ⟨n, Q, P, fun w φ => ?_⟩
  rw [← h]
  congr 1
  funext z
  rw [GlobalTheory.WeilAdm.RealModel.schrInf_eq ψ β hβ]
  simp only [schrF, trP, β, LinearMap.neg_apply]
  congr 2
  push_cast
  ring

theorem unif_bound (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (M : ℝ) (s : Finset (ℕ × ℕ)) : ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ),
    ∀ (A : SInf F κ →ₗ[ℂ] SInf F κ)
      (L N : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ v, L (N v) = v) → (∀ v, ‖N v‖ ≤ M * ‖v‖) → (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SInf F κ), ⇑f' = schrF (trP F κ) v ⇑f → ⇑(A f') = schrF (trP F κ) (L v) ⇑(A f)) →
      ∀ f, (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) (A f) ≤
        C * (s'.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨n, Q, P, hQP⟩ := exists_model_schrF F ψ hψ κ
  obtain ⟨c, hc⟩ := GlobalTheory.lintegral_sq_comp_linearEquiv_mixed F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let Pc := P.toContinuousLinearEquiv
  let a : ℝ := ‖Pc.symm.toContinuousLinearMap‖
  let b : ℝ := ‖Pc.toContinuousLinearMap‖
  have hW := schwartz_withSeminorms ℂ (κ → mixedEmbedding.mixedSpace F) ℂ
  have hs : Continuous (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) :
      Seminorm ℂ (SInf F κ)) := Seminorm.continuous_finsetSup fun i _ => hW.continuous_seminorm i
  obtain ⟨q, hq, hqA⟩ := exists_seminorm_unif (l := Fin n) (a * (|M| * b))
    ((s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)).comp CQi.toLinearMap)
    (hs.comp CQi.continuous)
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous hW (q.comp CQ.toLinearMap) (hq.comp CQ.continuous)
  refine ⟨s', C, fun A L N hLN hN hA hI f => ?_⟩
  let A' : Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.symm.toLinearMap ∘ₗ L ∘ₗ P.toLinearMap
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : Sch (Fin n)), ⇑g' = rhoFun w ⇑g → ⇑(A' g') = rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = schrF (trP F κ) (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = schrF (trP F κ) (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2, hL']
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = schrF (trP F κ) (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = rhoFun (L' w) ⇑(A' g) := congrArg (rhoFun (L' w)) (hCQ _).symm
  have hd := DRhoTransfer.dRho_intertwine (Fin n) L' A' 1 ENNReal.one_ne_top
    (fun g => by rw [one_mul]; exact hbound g) hint
  have hB : IsBddIntertwiner (a * (|M| * b)) A' := by
    refine ⟨hbound, fun w => P.symm (N (P w)), fun w => ?_, fun u g => ?_⟩
    · have h1 : ‖P.symm (N (P w))‖ ≤ a * ‖N (P w)‖ := Pc.symm.toContinuousLinearMap.le_opNorm _
      have h2 : ‖P w‖ ≤ b * ‖w‖ := Pc.toContinuousLinearMap.le_opNorm _
      have h3 : ‖N (P w)‖ ≤ |M| * (b * ‖w‖) := (hN _).trans
        (mul_le_mul (le_abs_self M) h2 (norm_nonneg _) (abs_nonneg M))
      calc _ ≤ a * (|M| * (b * ‖w‖)) := h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        _ = _ := by ring
    · have e : L' (P.symm (N (P u))) = u := by
        change P.symm (L (P (P.symm (N (P u))))) = u
        rw [P.apply_symm_apply, hLN, P.symm_apply_apply]
      rw [hd, e]
  have h1 := hqA A' hB (CQ f)
  have e : CQi (A' (CQ f)) = A f := by rw [hA'apply, hQQ, hQQ]
  change (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) (CQi (A' (CQ f))) ≤ _ at h1
  rw [e] at h1
  exact h1.trans (hC f)

theorem locOpInf_unif_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ s : Finset (ℕ × ℕ), ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), ∀ k ∈ KAt K (evI F),
      ∀ f : SInf F (Fin a × Fin (a + a')),
        (s.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) (locOpInf (om (k, 1)) f) ≤
          C * (s'.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) f := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT K hK s
  have hψ : IsStd B.ψ := hT.base.std
  have hW : G.M.IsWeil B.ψ X.β (X.β / X.α) om := hT.weil
  have hcK : IsCompact (K : Set (UA σ G.V.J)) :=
    GlobalTheory.StabCpt.isCompact_of_isStab hKP F E σ B a G.V (a - G.p) G.p K hT.base hT.geo.hV hK
  obtain ⟨M, hM⟩ := GlobalTheory.ArchKX.archActX_bound G.M _ (isCompact_KAt hcK (evI F))
  obtain ⟨s', C, hC⟩ := unif_bound F B.ψ hψ (Fin a × Fin (a + a')) M s
  refine ⟨s', C, fun k hk f => ?_⟩
  have hkU : k ∈ UAt σ G.V (evI F) := hk.2
  have hex := GlobalTheory.ThK.ArchActs.acts_inf hKP F E σ B a a' G X om om' hT k hkU
  have hlin : IsLinearMap ℂ ⇑(om (k, 1)) := (om (k, 1)).isLinear
  let A : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := locOpInf (om (k, 1))
      map_add' := fun f g => by simpa using locOpInf_lin hlin hex 1 1 f g
      map_smul' := fun c f => by simpa using locOpInf_lin hlin hex c 0 f f }
  let L := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX G.M k)
  let N := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX G.M k⁻¹)
  have hLN : ∀ v, L (N v) = v := GlobalTheory.ArchKX.archActX_inv G.M k
  have hN : ∀ v, ‖N v‖ ≤ M * ‖v‖ := hM k⁻¹ (inv_mem hk)
  have h2 : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 := fun f =>
    (GlobalTheory.ArchKX.lintegral_acts_eq_volume G.M B.ψ X.β (X.β / X.α) om hW k f (A f) (acts_locOpInf (hex f))).le
  have hI : ∀ v (f f' : SInf F (Fin a × Fin (a + a'))), ⇑f' = schrF (trP F (Fin a × Fin (a + a'))) v ⇑f →
      ⇑(A f') = schrF (trP F (Fin a × Fin (a + a'))) (L v) ⇑(A f) := fun v f f' h =>
    GlobalTheory.ArchKX.locOpInf_schrF G.M B.ψ X.β (X.β / X.α) om hψ hW k hkU hex v f f' h
  exact hC A L N hLN hN h2 hI f

end GlobalTheory.ArchKX
