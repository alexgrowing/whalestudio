import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartEqual
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ShiftDecayA

open GlobalTheory.ThK.LemF GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic GlobalTheory.ConeArchB GlobalTheory.ConeArchA

theorem linear_bound {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {ι : Type} (L : ι → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V' ℂ) (w : ι → ℝ) (p : Seminorm ℂ (SchwartzMap V' ℂ))
    (hb : ∀ f : ℕ → SchwartzMap V ℂ, (∀ q : Seminorm ℂ (SchwartzMap V ℂ), Continuous q → ∃ C : ℝ, ∀ t, q (f t) ≤ C) →
      ∃ C : ℝ, ∀ t i, w i * p (L i (f t)) ≤ C) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ h i, w i * p (L i h) ≤ C * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  by_contra hne
  push_neg at hne
  set S : ℕ → Finset (ℕ × ℕ) := fun k => Finset.range (k + 1) ×ˢ Finset.range (k + 1) with hS
  set q : ℕ → Seminorm ℂ (SchwartzMap V ℂ) := fun k => (S k).sup (schwartzSeminormFamily ℂ V ℂ) with hq
  choose h i hhi using fun k : ℕ => hne (S k) k
  have hpos : ∀ k, 0 < q k (h k) := by
    intro k
    rcases (apply_nonneg (q k) (h k)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h0 : h k = 0 := by
        ext x
        have h1 : ‖h k x‖ ≤ q k (h k) := by
          refine (SchwartzMap.norm_le_seminorm ℂ (h k) x).trans ?_
          exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ V ℂ) (i := (0, 0)) (by simp [S])
        rw [← heq] at h1
        simpa using norm_le_zero_iff.1 h1
      have := hhi k
      rw [h0] at this
      simp at this
  set f : ℕ → SchwartzMap V ℂ := fun k => ((q k (h k) : ℂ))⁻¹ • h k with hf
  have hqf : ∀ k, q k (f k) = 1 := fun k => by
    rw [hf, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos k),
      inv_mul_cancel₀ (hpos k).ne']
  have hbd : ∀ r : Seminorm ℂ (SchwartzMap V ℂ), Continuous r → ∃ C : ℝ, ∀ t, r (f t) ≤ C := by
    intro r hr
    obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) r hr
    set m := s.sup fun x : ℕ × ℕ => max x.1 x.2 with hm
    have hsub : ∀ k, m ≤ k → s ⊆ S k := fun k hk x hx => by
      have : max x.1 x.2 ≤ m := Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx
      simp only [S, Finset.mem_product, Finset.mem_range]
      omega
    refine ⟨C * (1 + ∑ k ∈ Finset.range m, s.sup (schwartzSeminormFamily ℂ V ℂ) (f k)), fun t => ?_⟩
    refine (hC (f t)).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    gcongr
    by_cases ht : m ≤ t
    · calc s.sup (schwartzSeminormFamily ℂ V ℂ) (f t) ≤ q t (f t) := Seminorm.le_def.1 (Finset.sup_mono (hsub t ht)) (f t)
        _ = 1 := hqf t
        _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
    · push_neg at ht
      have := Finset.single_le_sum (f := fun k => s.sup (schwartzSeminormFamily ℂ V ℂ) (f k))
        (fun _ _ => apply_nonneg _ _) (Finset.mem_range.2 ht)
      have h0 : 0 ≤ ∑ k ∈ Finset.range m, s.sup (schwartzSeminormFamily ℂ V ℂ) (f k) :=
        Finset.sum_nonneg fun _ _ => apply_nonneg _ _
      linarith
  obtain ⟨C, hC⟩ := hb f hbd
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have h1 := hhi k
  have h2 := hC k (i k)
  have h3 : w (i k) * p (L (i k) (h k)) = q k (h k) * (w (i k) * p (L (i k) (f k))) := by
    rw [hf, map_smul, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos k)]
    have hq0 : q k (h k) ≠ 0 := (hpos k).ne'
    field_simp
  rw [h3] at h1
  have h4 := hpos k
  have h5 : q k (h k) * (w (i k) * p (L (i k) (f k))) ≤ q k (h k) * C := mul_le_mul_of_nonneg_left h2 h4.le
  nlinarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem shift_decay_of_model {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    (hB : B.IsGood σ) (hG : G.IsGood B) (hM₁ : G₁.M.IsGood B.ψ)
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a'))}
    (hei : ∀ f, e (pure f G.M.vac) = pure (ei f) G₁.M.vac)
    {T : Type} (f : T → SInf F (Fin (b + 2) × Fin (b + 2 + a')))
    (hf : ∀ p : Seminorm ℂ (SInf F (Fin (b + 2) × Fin (b + 2 + a'))), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C)
    (p : Seminorm ℂ (SInf F (Fin b × Fin (b + a')))) (hp : Continuous p) (N : ℕ) :
    ∃ C : ℝ, ∀ t (l : (AE F E)ˣ), p (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (f t))) ≤
      C / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := by
  have hM := hG.hM
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hB.cm hG.hW.skew, hC.hH'.xy, map_one])
  obtain ⟨c, hc⟩ := exists_finPart_ne_zero G₁.M.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set g₁ : ℂ := ∏ᶠ v, G₁.M.vac v fun i => evalV F v (c i) with hg₁
  have hc' : g₁ ≠ 0 := hc (fun i => mk 0 (c i)) fun _ => rfl
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hg : (fun y : Fin (b + 2) × Fin (b + 2 + a') → Af F => ∏ᶠ v, G.M.vac v fun i => evalV F v (y i)) ∈ SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV G.M.vac (fun v => (hM.vac v).1) hM.std,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod G.M.vac (fun v => (hM.vac v).1) hM.std⟩
  obtain ⟨C, hCb⟩ := slice_decay B.ψ hB.std S U (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) hg f hf (isCompact_singleton (x := 0)) p hp N
  obtain ⟨A, hA0, hA⟩ := exists_piInf_le_crd (E := E) B.emb
  refine ⟨‖g₁‖⁻¹ * (|C| * A ^ N), fun k l => ?_⟩
  set x := GlobalTheory.XTermMaj.crd F E (l : AE F E) with hx
  have hx1 : ∀ i, (realAd F 1 * x i).1 = (x i).1 := fun i => by
    have h1 : (realAd F 1).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
      rw [map_one]; exact evI_realAd_one)
    change (realAd F 1).1 * (x i).1 = _
    rw [h1, one_mul]
  obtain ⟨f₁, hf₁, hb⟩ := hCb k (fun i => realAd F 1 * x i) (funext fun i => show (0 : Af F) * (x i).2 = 0 from zero_mul _)
  have hS : G.M.co.e (partInf F (shiftA H H' l)) = ∑ i, (realAd F 1 * x i) • S i := by
    simp only [S, mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum, ← smul_assoc (x _), ← Finset.sum_smul]
    rw [partInf, shiftA]
    congr 3
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  set h := ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (f k)) with hh
  have e1 : f₁ = g₁ • h := by
    refine DFunLike.coe_injective (hf₁.trans ?_)
    rw [← hS]
    change sliceL c (e (G.M.co.rho B.ψ (partInf F (shiftA H H' l)) (pure (f k) G.M.vac))) = _
    rw [(locOpInf_rho_eq hB.std hM _ _).1, hei]
    funext y
    change h (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))) * g₁ = g₁ * h y
    simp only [RingEquiv.apply_symm_apply, mul_comm]
  simp only [hx1] at hb
  set R := 1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hR
  set P := 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ with hP
  have hR0 : 0 < R := by positivity
  have hP0 : 0 < P := by positivity
  have hPR : P ^ N ≤ A ^ N * R ^ N := by rw [← mul_pow]; exact pow_le_pow_left₀ hP0.le (hA _) N
  rw [e1, map_smul_eq_mul, Real.rpow_neg hR0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)] at hb
  rw [le_div_iff₀ (by positivity), le_inv_mul_iff₀ (norm_pos_iff.2 hc')]
  have hp0 := apply_nonneg p h
  calc ‖g₁‖ * (p h * P ^ N) ≤ ‖g₁‖ * (p h * (A ^ N * R ^ N)) := by gcongr
    _ = ‖g₁‖ * p h * R ^ N * A ^ N := by ring
    _ ≤ _ := by gcongr; exact hb.trans (le_abs_self C)

theorem decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (a n N : ℕ), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (h : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (l : (AE F E)ˣ), l ∈ idelesAt E (evI F) →
      (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N * SchwartzMap.seminorm ℂ a n (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) h)) ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) h := by
  intro F E _ _ _ _ _ σ _ B b a' G G₁ H H' X om om' hCf hT hM₁ e he ei ev _ hev hloc a n N
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hSB : ∀ v, G.M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ f, e (pure f G.M.vac) = pure (ei f) G₁.M.vac := fun f => by
    rw [hloc f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  obtain ⟨s, C, hC'⟩ := linear_bound (ι := (AE F E)ˣ)
    (fun l => ei.toLinearMap ∘ₗ archOp (archW (G.M.co.e (partInf F (shiftA H H' l)))))
    (fun l => (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N) (SchwartzMap.seminorm ℂ a n) (fun f hf => by
      obtain ⟨C, hC⟩ := shift_decay_of_model hCf hT.base hT.geo hM₁ he hei f hf (SchwartzMap.seminorm ℂ a n)
        ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a, n)) N
      refine ⟨C, fun t l => ?_⟩
      have := hC t l
      rw [(locOpInf_rho_eq hψ hM _ _).2] at this
      rw [mul_comm]
      exact (le_div_iff₀ (by positivity)).1 this)
  refine ⟨s, C, fun h l _ => ?_⟩
  have := hC' h l
  rw [(locOpInf_rho_eq hψ hM _ _).2]
  exact this

end GlobalTheory.ShiftDecayA
