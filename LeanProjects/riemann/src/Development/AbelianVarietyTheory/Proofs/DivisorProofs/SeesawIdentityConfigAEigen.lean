import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedModelCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelFunctionalEvalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_one' (n : ℕ) : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mulVec' {m k l : Type} [Fintype k] {R : Type} [CommRing R] (x : m → R) (A : Matrix l k R)
    (z : k → R) : Matrix.vecMulVec x (A *ᵥ z) = Matrix.vecMulVec x z * Aᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

open scoped Classical in

theorem finRelG_of_isEv {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v))
    (v : Pl F) : FinRelG B M M₁ ι ι' I v (ev v) := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n₁ × Fin d₁) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n₁ × Fin d₁) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁
    have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    have hevφ : ev v φ ∈ SB _ := by
      rw [← (hvm v).2]
      exact Submodule.mem_map_of_mem hφ
    rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
    exact canc _ _ h1
  · intro u hu hz φ hφ φ₁ hφ₁ hA
    have h1 := he.inv u hu _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    exact canc _ _ h1

open scoped Classical in
open GlobalTheory.ThK.EvUniqInf in

theorem infRelG_of_isEv {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (hev : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hloc0 : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    InfRelG B M M₁ ι ι' I ei := by
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => rest_pure g φ hφSB hstd
  have hRest₁ : ∀ g : SInf F (Fin n₁ × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v,
      Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i)) :=
    fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)
  have he : ∀ g : SInf F (Fin n × Fin d), e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei g) (fun v =>
      Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hloc g φ hφSB hcof, hevφ]
  refine ⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩
  · have h1 := hev.Heisenberg₂ z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ :=
      hA _ (hRest f)
    rw [h2, he, he] at h1
    have h3 : M₁.co.rho B.ψ z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v =>
        Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ (fun v =>
        Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :=
      hA₁ _ (hRest₁ (ei f))
    exact eq_of_pure_std _ _ (h1.trans h3)
  · have h1 := hev.inv u hu (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ := hA _ (hRest f)
    rw [h2, he, he] at h1
    exact eq_of_pure_std _ _ h1

theorem eq_smul_of_loc {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    (hM : M.IsGood B.ψ) {e e' : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    {ei ei' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)}
    {ev ev' : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ} {c : ℂ}
    (hl : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v))
    (hl' : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei' f) fun v => ev' v (φ v))
    (hc : ei' = c • ei) (hfin : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev' v φ = ev v φ) :
    ∀ Ψ ∈ schA F (Fin n × Fin d), e' Ψ = c • e Ψ := by
  intro Ψ hΨ
  have hs := GlobalTheory.T.adelicSchwartzSpace_mem_span_pureTensors F (Fin n × Fin d) Ψ hΨ
  clear hΨ
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, ⟨hφ, hind⟩, rfl⟩ := hx
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hind, hM.std] with v h1 h2
      rw [h1, h2]
      rfl
    rw [hl' f φ hφ hvac, hl f φ hφ hvac, hc]
    have hfe : (fun v => ev' v (φ v)) = fun v => ev v (φ v) := funext fun v => hfin v _ (hφ v)
    rw [hfe]
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
      SchwartzMap.smul_apply, mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, map_smul, hx, smul_comm]

end GlobalTheory.ThK.EvFactor

namespace GlobalTheory.ThK.EvFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isEv_comp_isoA {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₂ : Model σ X W₁} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁}
    {e₁ : Fn F n d →ₗ[ℂ] Fn F n d₁} {e₂ : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁}
    (h₁ : IsEv B M M₂ 1 H'.ι (iso0 n H') e₁)
    (h₂ : IsEv B M₂ M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₂)
    (hs : ∀ (ei₁ : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev₁ : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei₁ ≠ 0 →
      (∀ v, ev₁ v (M.vac v) = M₂.vac v ∧ (SB _).map (ev₁ v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
        e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei₁ f) fun v => ev₁ v (φ v)) →
      Function.Surjective ei₁) :
    IsEv B M M₁ H.ι H'.ι (isoA H H') (e₂ ∘ₗ e₁) := by
  refine ⟨fun Φ hΦ => h₂.maps _ (h₁.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_, ?_⟩
  · simp only [LinearMap.comp_apply]
    have e1 := h₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    rw [incM_one', Matrix.one_mul] at e1
    rw [e1]
    have e2 := h₂.Heisenberg₂ z (e₁ Φ) (h₁.maps Φ hΦ)
    rw [incM_one', Matrix.transpose_one, Matrix.mul_one] at e2
    exact e2
  · simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [h₁.inv u hu Φ hΦ]
    · have hz : Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z) =
          incM F (1 : Matrix (Fin n) (Fin n) E) * Matrix.vecMulVec (incV F H.x) z * (incM F H'.ι)ᵀ := by
        rw [incM_one', Matrix.one_mul, vecMulVec_mulVec']
      rw [hz, h₁.Heisenberg₂ _ Φ hΦ, h₂.inv _ ⟨z, rfl⟩ _ (h₁.maps Φ hΦ)]
  · obtain ⟨ei₁, ev₁, hne₁, hv₁, hl₁⟩ := h₁.loc
    obtain ⟨ei₂, ev₂, hne, hv₂, hl₂⟩ := h₂.loc
    have hsu := hs ei₁ ev₁ hne₁ hv₁ hl₁
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), ?_, fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · intro h0
      apply hne
      ext1 g
      obtain ⟨g', rfl⟩ := hsu g
      exact congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => T g') h0
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = M₂.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

theorem unique_isoA (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n}
    {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {H : Plane E n n₁} {H' : Plane E d d₁} {M : Model σ X W}
    {M₁ : Model σ X₁ W₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (hM₁ : M₁.IsGood B.ψ)
    {e e' : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e)
    (he' : IsEv B M M₁ H.ι H'.ι (isoA H H') e') :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin n × Fin d), e' Ψ = c • e Ψ := by
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he.loc
  obtain ⟨ei', ev', hei', hev', hloc'⟩ := he'.loc
  have hfin : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev' v φ = ev v φ := fun v φ hφ =>
    GlobalTheory.T.double_adapted_model_compatible hP F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁ v (ev v) (ev' v)
      (finRelG_of_isEv hM hM₁ he ei ev hei hev hloc v) (finRelG_of_isEv hM hM₁ he' ei' ev' hei' hev' hloc' v)
      (hev v).2 (hev' v).2 (hev v).1 (hev' v).1 φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.double_adapted_lagrangian_dim hP F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁ ei ei' hei
    (infRelG_of_isEv hM hM₁ he ei ev hev hloc) (infRelG_of_isEv hM hM₁ he' ei' ev' hev' hloc')
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hei' (by rw [hc, zero_smul])
  exact ⟨c, hc0, eq_smul_of_loc hM hloc hloc' hc hfin⟩

end GlobalTheory.ThK.EvFactor

theorem GlobalTheory.ThK.EvFactor.evA_eq_smul_comp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (M₂ : Model σ G.V G₁.W) (om₂ : Rep σ G.V G₁.W),
      IsPair B M₂ X.β (X.β / X.α) om₂ (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) →
    ∀ (e₁ : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F (b + 2) (b + a')) (e₂ : Fn F (b + 2) (b + a') →ₗ[ℂ] Fn F b (b + a')),
      IsEv B G.M M₂ 1 H'.ι (iso0 (b + 2) H') e₁ → IsEv B M₂ G₁.M H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₂ →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e Ψ = c • e₂ (e₁ Ψ) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ M₂ om₂ hP₂ e₁ e₂ h₁ h₂
  have hB := hT.base
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  have hM := hT.geo.hM
  have hM₁ := hT₁.geo.hM
  have hM₂ := hP₂.good
  have hE := GlobalTheory.ThK.EvFactor.isEv_comp_isoA h₁ h₂ fun ei₁ ev₁ hne hv hl =>
    GlobalTheory.T.adapted_model_functional_eval hK.base F E σ B _ _ _ _ _ _ _ 0 (b + 1) G.V G.W G₁.W H' G.M M₂ hB hV hW hM hC.hH' hM₂ ei₁ hne
      (GlobalTheory.ThK.EvUniq.infRel_of_isEv F E σ B _ _ _ _ _ _ _ 0 (b + 1) G.V G.W G₁.W H' G.M M₂ hB hV hW hM hC.hH' hM₂ e₁ h₁
        ei₁ ev₁ hne hv hl)
  obtain ⟨c, hc, hce⟩ := GlobalTheory.ThK.EvFactor.unique_isoA hK.base hB hV hW hM hC.hH hC.hH' hM₁ hE he
  exact ⟨c, hc, fun Ψ hΨ => hce Ψ hΨ⟩
