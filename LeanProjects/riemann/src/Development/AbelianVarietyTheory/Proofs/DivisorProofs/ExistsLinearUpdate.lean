import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

noncomputable section

namespace GlobalTheory.SoPure

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def atOp (v : Pl F) (π : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ x := π (fun y => Φ (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) (fun i => evFin F v (x i))
  map_add' Φ Ψ := by
    funext x
    have e : (fun y : κ → Fv F v => (Φ + Ψ) (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) =
      (fun y => Φ (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) +
        (fun y => Ψ (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) := rfl
    rw [e, map_add, Pi.add_apply, Pi.add_apply]
  map_smul' c Φ := by
    funext x
    have e : (fun y : κ → Fv F v => (c • Φ) (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) =
      c • (fun y => Φ (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) := rfl
    rw [e, map_smul, Pi.smul_apply, Pi.smul_apply, RingHom.id_apply]

theorem atOp_tens (v : Pl F) (π : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (χ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    atOp v π (tens (evFin F v) χ r) = tens (evFin F v) (π χ) r := by
  funext x
  have e : (fun y : κ → Fv F v => tens (evFin F v) χ r (x + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i)))) =
      r x • χ := by
    funext y
    have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x i))) :=
      fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    simp only [tens, hr x _ hz, Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel, Pi.smul_apply, smul_eq_mul]
    ring
  show π _ _ = _
  rw [e, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

theorem atOp_pure (v : Pl F) (π : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (f : SInf F κ)
    (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) :
    atOp v π (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v (π (φ v))) := by
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  have e := hrt (φ v)
  rw [Function.update_eq_self] at e
  rw [← e, atOp_tens v π _ r hr, hrt]

theorem exists_linear_update (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) :
    ∃ L : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), ∀ χ, L χ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ) := by
  obtain ⟨r, -, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  exact ⟨{ toFun := fun χ => tens (evFin F v) χ r
           map_add' := fun χ χ' => by funext x; simp [tens, add_mul]
           map_smul' := fun c χ => by funext x; simp [tens, mul_assoc] }, hrt⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem span_soLoc_le (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Submodule.span ℂ (M.SoLoc ψ t) ≤ SB _ := Submodule.span_le.2 fun _ h => h.1

theorem pure_mem_of_span (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (hstd : ∀ᶠ w in Filter.cofinite, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    (f : SInf F (Fin n × Fin d)) (Q : Submodule ℂ (Fn F n d))
    (hQ : ∀ φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      φ v ∈ M.SoLoc ψ t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ Q)
    (φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB _) (hev : ∀ᶠ w in Filter.cofinite, φ w = M.vac w)
    (hv : φ v ∈ Submodule.span ℂ (M.SoLoc ψ t)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ Q := by
  obtain ⟨L, hL⟩ := exists_linear_update v f φ ((hev.and hstd).mono fun w hw => hw.1.trans hw.2)
  have hle : Submodule.span ℂ (M.SoLoc ψ t) ≤ Q.comap L := by
    refine Submodule.span_le.2 fun χ hχ => ?_
    show L χ ∈ Q
    rw [hL]
    refine hQ _ (fun w => ?_) ?_ (by rwa [Function.update_self])
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hχ.1
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
  have := hle hv
  rwa [Submodule.mem_comap, hL, Function.update_eq_self] at this

theorem atOp_of_mem_so (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (hstd : ∀ᶠ w in Filter.cofinite, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    (π : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)) (hπ : ∀ χ ∈ M.SoLoc ψ t, π χ = χ) :
    ∀ Φ ∈ M.So ψ t, atOp v π Φ = Φ := by
  intro Φ hΦ
  have hle : M.So ψ t ≤ LinearMap.eqLocus (atOp v π) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, -, hev, hv, rfl⟩
    show atOp v π _ = _
    rw [atOp_pure v π f φ ((hev.and hstd).mono fun w hw => hw.1.trans hw.2), hπ _ hv, Function.update_eq_self]
    rfl
  exact hle hΦ

theorem pure_mem_polSo (B : Base F E) (M : Model σ Y W)
    (hstd : ∀ᶠ w in Filter.cofinite, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol B.ψ B.emb)
    (φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB _) (hev : ∀ᶠ w in Filter.cofinite, φ w = M.vac w)
    (hv : φ B.v₁ ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B M ⊓ M.So B.ψ B.τ₁ :=
  Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨f, hf, φ, hSB, hev, rfl⟩, pure_mem_of_span M B.ψ B.τ₁ hstd f (M.So B.ψ B.τ₁)
    (fun φ h1 h2 h3 => by unfold Model.So; exact Submodule.subset_span ⟨f, φ, h1, h2, h3, rfl⟩) φ hSB hev hv⟩

theorem polSo_eq_span (B : Base F E) (M : Model σ Y W)
    (hstd : ∀ᶠ w in Filter.cofinite, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) :
    PolData B M ⊓ M.So B.ψ B.τ₁ = Submodule.span ℂ {Φ | ∃ f ∈ M.Pol B.ψ B.emb, ∃ φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ,
      (∀ w, φ w ∈ SB _) ∧ (∀ᶠ w in Filter.cofinite, φ w = M.vac w) ∧ φ B.v₁ ∈ M.SoLoc B.ψ B.τ₁ ∧
        Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro Φ ⟨hP, hS⟩
    set S := Submodule.span ℂ (M.SoLoc B.ψ B.τ₁) with hSdef
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective S.subtype (Submodule.ker_subtype S)
    have hπ : ∀ χ ∈ M.SoLoc B.ψ B.τ₁, (S.subtype.comp r) χ = χ := fun χ hχ =>
      congrArg Subtype.val (LinearMap.congr_fun hr ⟨χ, Submodule.subset_span hχ⟩)
    rw [← atOp_of_mem_so M B.ψ B.τ₁ hstd _ hπ Φ hS]
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (atOp B.v₁ (S.subtype.comp r)) _)).2 ?_ hP)
    rintro _ ⟨f, hf, φ, hSB, hev, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [atOp_pure B.v₁ _ f φ ((hev.and hstd).mono fun w hw => hw.1.trans hw.2)]
    have hm : (S.subtype.comp r) (φ B.v₁) ∈ S := (r (φ B.v₁)).2
    refine pure_mem_of_span M B.ψ B.τ₁ hstd f _ (fun φ h1 h2 h3 => Submodule.subset_span ?_) _
      (fun w => ?_) ?_ (by rwa [Function.update_self])
    · exact ⟨f, hf, φ, h1, h2, h3, rfl⟩
    · by_cases hw : w = B.v₁
      · subst hw; rw [Function.update_self]; exact span_soLoc_le M B.ψ B.τ₁ hm
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne B.v₁] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
  · rintro _ ⟨f, hf, φ, hSB, hev, hv, rfl⟩
    exact pure_mem_polSo B M hstd f hf φ hSB hev (Submodule.subset_span hv)

end GlobalTheory.SoPure

end
