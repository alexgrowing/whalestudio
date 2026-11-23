import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzHadamardLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDenseHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TemperedFunctionalVanishMulStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeInfNe

open GlobalTheory.ArchUniq GlobalTheory.ArchUniqStd
open scoped SchwartzMap ContDiff

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem eq_zero_of_kills_mul {A : Type} (g : A → 𝓢(V, ℂ)) (hg : ∀ x, ∃ a, g a x ≠ 0) (T : 𝓢(V, ℂ) →L[ℂ] ℂ)
    (hT : ∀ a (ψ h : 𝓢(V, ℂ)), (∀ x, h x = g a x * ψ x) → T h = 0) : T = 0 := by
  have hzero : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) → T φ = 0 := by
    intro φ hφ
    obtain ⟨S, hS⟩ := hφ.isCompact.elim_finite_subcover (fun a => {x | g a x ≠ 0})
      (fun a => isOpen_ne_fun (g a).continuous continuous_const)
      (fun x _ => by obtain ⟨a, ha⟩ := hg x; exact Set.mem_iUnion.2 ⟨a, ha⟩)
    set s : V → ℂ := fun x => ∑ a ∈ S, g a x * (starRingEnd ℂ) (g a x) with hs
    have hconj : ∀ a, ContDiff ℝ ∞ fun x => (starRingEnd ℂ) (g a x) := fun a =>
      Complex.conjCLE.contDiff.comp ((g a).smooth ⊤)
    have hss : ContDiff ℝ ∞ s := ContDiff.sum fun a _ => ((g a).smooth ⊤).mul (hconj a)
    have hsne : ∀ x ∈ tsupport (φ : V → ℂ), s x ≠ 0 := by
      intro x hx h0
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS hx)
      have h1 : ∑ a ∈ S, Complex.normSq (g a x) = 0 := by
        have : s x = ((∑ a ∈ S, Complex.normSq (g a x) : ℝ) : ℂ) := by
          simp only [hs, Complex.mul_conj, Complex.ofReal_sum]
        rw [this] at h0
        exact_mod_cast h0
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg (g a x))).1 h1 a ha
      exact hxa (Complex.normSq_eq_zero.1 h2)
    set m : V → ℂ := fun x => φ x * (s x)⁻¹ with hm
    have hms : ContDiff ℝ ∞ m := by
      refine contDiff_iff_contDiffAt.2 fun x => ?_
      by_cases hx : x ∈ tsupport (φ : V → ℂ)
      · exact (φ.smooth ⊤).contDiffAt.mul (hss.contDiffAt.inv (hsne x hx))
      · have h1 : (φ : V → ℂ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [h1] with y hy
        simp only [hm, hy, Pi.zero_apply, zero_mul]
    have hmc : HasCompactSupport m := hφ.mul_right
    have hψc : ∀ a, HasCompactSupport fun x => (starRingEnd ℂ) (g a x) * m x := fun a => hmc.mul_left
    have hhc : ∀ a, HasCompactSupport fun x => g a x * ((starRingEnd ℂ) (g a x) * m x) := fun a => (hψc a).mul_left
    let ψ : A → 𝓢(V, ℂ) := fun a => (hψc a).toSchwartzMap ((hconj a).mul hms)
    let h : A → 𝓢(V, ℂ) := fun a => (hhc a).toSchwartzMap (((g a).smooth ⊤).mul ((hconj a).mul hms))
    have hφe : φ = ∑ a ∈ S, h a := by
      ext x
      rw [← evAt_apply x (∑ a ∈ S, h a), map_sum]
      change φ x = ∑ a ∈ S, g a x * ((starRingEnd ℂ) (g a x) * m x)
      simp only [← mul_assoc]
      rw [← Finset.sum_mul]
      change φ x = s x * (φ x * (s x)⁻¹)
      by_cases hx : x ∈ tsupport (φ : V → ℂ)
      · field_simp [hsne x hx]
      · rw [image_eq_zero_of_notMem_tsupport hx]; simp
    rw [hφe, map_sum]
    exact Finset.sum_eq_zero fun a _ => hT a (ψ a) (h a) fun x => rfl
  have hclosed : IsClosed {φ : 𝓢(V, ℂ) | T φ = 0} := isClosed_eq T.continuous continuous_const
  ext φ
  have hsub : closure {f : 𝓢(V, ℂ) | HasCompactSupport (f : V → ℂ)} ⊆ {φ | T φ = 0} :=
    closure_minimal (fun f hf => hzero f hf) hclosed
  exact hsub (GlobalTheory.schwartz_dense_hasCompactSupport φ)

theorem eq_zero_of_kills_schrF {P : V → V → ℝ} (hP : IsPairing P) (g : 𝓢(V, ℂ)) (hg : g ≠ 0) (T : 𝓢(V, ℂ) →L[ℂ] ℂ)
    (hT : ∀ w (h : 𝓢(V, ℂ)), ⇑h = schrF P w g → T h = 0) : T = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (SchwartzMap.ext h)
  choose t ht using fun a : V => schrF_schwartz hP (a, 0) g
  have ht' : ∀ a y, t a y = g (y + a) := fun a y => by
    rw [ht a]
    simp [schrF, hP.zero_right]
  refine eq_zero_of_kills_mul t (fun x => ⟨x₀ - x, by rw [ht']; simpa using hx₀⟩) T fun a => ?_
  refine GlobalTheory.T.tempered_functional_vanish_mul T (t a) fun ξ h hh => ?_
  obtain ⟨b, hb⟩ := exists_right hP ((-(1 / (2 * Real.pi))) • ξ)
  set c : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * ((P a b / 2 : ℝ) : ℂ)) with hc
  have h1 := hT (a, b) (c • h) (funext fun y => by
    change c * h y = _
    rw [hh, ht', schrF, hb, hc, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring)
  rw [map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)

omit [FiniteDimensional ℝ V] in

theorem schrF_neg {P : V → V → ℝ} (hP : IsPairing P) (w : V × V) (f : V → ℂ) : schrF P w (schrF P (-w) f) = f := by
  funext y
  have hL : ∀ x z, P (-x) z = -P x z := fun x z => by simpa using hP.smulL (-1) x z
  have hR : ∀ x z, P x (-z) = -P x z := fun x z => by simpa using hP.smulR (-1) x z
  simp only [schrF, Prod.fst_neg, Prod.snd_neg, hL, hR, hP.addL, add_neg_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_add, ← Complex.ofReal_add]
  rw [show P y w.2 + P w.1 w.2 / 2 + (-(P y w.2 + P w.1 w.2) + - -P w.1 w.2 / 2) = 0 by ring]
  simp

end Real

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

open GlobalTheory.EvZeroInf in

theorem arch_heis {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hevac : ∀ v, ev v (M.vac v) = M₁.vac v)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v))
    (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    ei (locOpInf (M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ))) f) =
      locOpInf (M₁.co.rho B.ψ (partInf F z)) (ei f) := by
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hSB₁ : ∀ v, M₁.vac v ∈ SB _ := fun v => (hM₁.vac v).1
  have hpure : ∀ f, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F _ := fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hpure₁ : ∀ f, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M₁.vac ∈ schA F _ := fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB₁ hM₁.std
  have hrest : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) (⇑f) (finPart M.vac) :=
    fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure f⟩
  have hrest₁ : ∀ f : SInf F (Fin n₁ × Fin d₁), Rest (evI F) (⇑f) (finPart M₁.vac) :=
    fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure₁ f⟩
  have hep : ∀ f, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) M₁.vac := by
    intro f
    rw [hloc f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl)]
    congr 1
    funext v
    exact hevac v
  apply eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std
  have h1 : M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (locOpInf (M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ))) f) M.vac :=
    (locOpInf_rho M.co hψ _ f).1 _ (hrest f)
  have h2 : M₁.co.rho B.ψ (partInf F z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) M₁.vac) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (locOpInf (M₁.co.rho B.ψ (partInf F z)) (ei f)) M₁.vac :=
    (locOpInf_rho M₁.co hψ _ (ei f)).1 _ (hrest₁ (ei f))
  have h3 : partInf F (incM F ι * z * (incM F ι')ᵀ) = incM F ι * partInf F z * (incM F ι')ᵀ := by
    rw [partInf, partInf, Matrix.mul_smul, Matrix.smul_mul]
  rw [← hep, ← h1, h3, he.Heisenberg₂ _ _ (hpure f), hep, h2]

end Adelic

end GlobalTheory.ConeInfNe

open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchUniqStd GlobalTheory.ConeInfNe in

theorem GlobalTheory.ConeInfNe.exists_ne_zero : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
    (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure)
    (l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) (hl : l ≠ 0)
    (hinv : ∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f),
    ∃ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f 1 1) ≠ 0 := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' _ hT hT₁ e he ei ev hei hev hpure K _ μK μ _ _ l hl _
  have hψ : IsStd B.ψ := hT.base.std
  by_contra hcon
  push_neg at hcon
  have hone : ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), locOpInf (om (1, 1)) f = f := fun f =>
    locOpInf_eq fun r _ => by rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  have hkill : ∀ f, l (ei f) = 0 := by
    intro f
    obtain ⟨f', hf'⟩ := schrF_schwartz (isPairing_trP (F := F) _) (-coordI G.M (shiftA H H' 1)) f
    have h1 : locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) f' = f := by
      apply DFunLike.coe_injective
      beta_reduce
      rw [(locOpInf_rho G.M.co hψ _ f').2, hf']
      exact schrF_neg (isPairing_trP _) _ _
    have h2 := hcon f'
    rw [coneInfInt, hone, h1, map_one, map_one] at h2
    simpa using h2
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  refine hl (eq_zero_of_kills_schrF (isPairing_trP (F := F) _) (ei f) hf l fun w h hh => ?_)
  have h1 := arch_heis hψ hT.geo.hM hT₁.geo.hM he ei ev (fun v => (hev v).1) hpure
    (G₁.M.co.e.symm (liftV w.1, liftV w.2)) f
  have h2 : locOpInf (G₁.M.co.rho B.ψ (partInf F (G₁.M.co.e.symm (liftV w.1, liftV w.2)))) (ei f) = h := by
    apply DFunLike.coe_injective
    beta_reduce
    rw [(locOpInf_rho G₁.M.co hψ _ (ei f)).2, hh, LinearEquiv.apply_symm_apply, loc_lift, loc_lift]
  rw [← h2, ← h1]
  exact hkill _

end
