import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroRestrictionNonzeroContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo.GlueEv

section Gen

variable {R : Type} {κ κ' κ₁ : Type}

theorem glue_zero_eq_ext_zero [CommRing R] (eq : κ ≃ κ' ⊕ κ₁) (x : κ₁ → R) :
    glue eq (0 : κ' → R) x = GlobalTheory.ThK.AdaptEv.ext0 eq x := by
  funext k; simp only [glue, GlobalTheory.ThK.AdaptEv.ext0]; cases eq k <;> rfl

theorem restr_apply [CommRing R] (eq : κ ≃ κ' ⊕ κ₁) (Φ : (κ → R) → ℂ) (x : κ₁ → R) :
    restr eq Φ x = Φ (glue eq 0 x) := rfl

theorem glue_add_zero [CommRing R] (eq : κ ≃ κ' ⊕ κ₁) (x y : κ₁ → R) :
    glue eq (0 : κ' → R) x + glue eq 0 y = glue eq 0 (x + y) := by
  funext k; simp only [glue, Pi.add_apply]; cases eq k <;> simp

theorem continuous_glue_zero [CommRing R] [TopologicalSpace R] (eq : κ ≃ κ' ⊕ κ₁) :
    Continuous (fun x : κ₁ → R => glue eq 0 x) := by
  refine continuous_pi fun k => ?_
  simp only [glue]
  rcases eq k with i | j
  · exact continuous_const
  · exact continuous_apply j

theorem restr_mem_SB [CommRing R] [TopologicalSpace R] (eq : κ ≃ κ' ⊕ κ₁) (g : (κ → R) → ℂ)
    (hg : g ∈ SB (κ → R)) : restr eq g ∈ SB (κ₁ → R) := by
  have hc := continuous_glue_zero (R := R) eq
  have hr : Continuous (fun y : κ → R => fun j => y (eq.symm (Sum.inr j))) := by fun_prop
  have hl : ∀ x : κ₁ → R, (fun j => glue eq 0 x (eq.symm (Sum.inr j))) = x := fun x => by
    funext j; simp [glue]
  refine ⟨hg.1.comp_continuous hc, ?_⟩
  refine (hg.2.image hr).of_isClosed_subset (isClosed_tsupport _) ?_
  intro x hx
  exact ⟨glue eq 0 x, tsupport_comp_subset_preimage g hc hx, hl x⟩

theorem restr_vacGlue [CommRing R] (eq : κ ≃ κ' ⊕ κ₁) (l : (κ' → R) → ℂ) (φ : (κ₁ → R) → ℂ) :
    restr eq (vacGlue eq l φ) = l 0 • φ := by
  funext x
  simp only [restr_apply, vacGlue, Pi.smul_apply, smul_eq_mul]
  congr 2 <;> funext k <;> simp [glue]

end Gen

end GlobalTheory.ThK.PlaneCo.GlueEv

namespace GlobalTheory.ThK.PlaneCo.GlueEv

section Adelic

variable {F : Type} [Field F] [NumberField F] {κ κ' κ₁ : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁]

theorem restr_pureA (eq : κ ≃ κ' ⊕ κ₁) (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    restr eq (pureA F f g) = pureA F (GlobalTheory.ThK.AdaptEv.Restr.restrS F eq f) (restr eq g) := by
  funext x
  simp only [restr_apply, pureA, GlobalTheory.ThK.AdaptEv.Restr.restrS_apply]
  congr 1
  · congr 1
    funext k
    rw [← glue_zero_eq_ext_zero]
    simp only [glue]
    rcases eq k with i | j
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
      exact map_zero _
    · rfl
  · congr 1
    funext k
    simp only [glue]
    rcases eq k with i | j <;> rfl

theorem restr_mem_schA (eq : κ ≃ κ' ⊕ κ₁) (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) : restr eq Φ ∈ schA F κ₁ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [restr_pureA]
    exact Submodule.subset_span ⟨_, _, restr_mem_SB eq g hg, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem restr_pure (eq : κ ≃ κ' ⊕ κ₁) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    restr eq (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (GlobalTheory.ThK.AdaptEv.Restr.restrS F eq f) (fun v => restr eq (φ v)) := by
  funext x
  simp only [restr_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, GlobalTheory.ThK.AdaptEv.Restr.restrS_apply]
  congr 1
  · congr 1
    funext k
    rw [← glue_zero_eq_ext_zero]
    simp only [glue]
    rcases eq k with i | j
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
      exact map_zero _
    · rfl
  · congr 1
    funext v
    congr 1
    funext k
    simp only [glue]
    rcases eq k with i | j
    · exact map_zero _
    · rfl

end Adelic

end GlobalTheory.ThK.PlaneCo.GlueEv

namespace GlobalTheory.ThK.PlaneCo.GlueEv

theorem restr_isEv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ : ℕ} {κ' : Type} [Fintype κ'] (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (M₁ : Model σ X₁ W₁) (eq : Fin n × Fin d ≃ κ' ⊕ Fin n₁ × Fin d₁)
    (T : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] ((κ' → AF F) × (κ' → AF F)) × Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hf : ∀ w w', symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
        (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (T w).2 (T w').2)
    (l : ∀ v : Pl F, (κ' → Fv F v) → ℂ) (μ : Measure (UA σ X.J)) (D : Set (UA σ X.J)),
    (∀ z, T (incM F ι * z * (incM F ι')ᵀ) = ((0, 0), z)) → (∀ u ∈ I, (T u).1.1 = 0 ∧ (T u).2 = 0) →
    (∀ v, l v ∈ SB _ ∧ l v 0 = 1) → (∀ v, M₁.vac v ∈ SB _) →
    IsEv B (Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (l v) (M₁.vac v)) μ D) M₁ ι ι' I (restr eq) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ κ' _ X W X₁ W₁ ι ι' I M₁ eq T hf l μ D hblk hI hl hvac
  have he : ∀ w, (glueDarboux M₁.co eq T hf).e w =
      (glue eq (T w).1.1 (M₁.co.e (T w).2).1, glue eq (T w).1.2 (M₁.co.e (T w).2).2) :=
    glueDarboux_e M₁.co eq T hf
  refine ⟨fun Φ hΦ => restr_mem_schA eq Φ hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩
  · funext x
    have h1 := he (incM F ι * z * (incM F ι')ᵀ)
    rw [hblk z] at h1
    simp only [restr_apply, Darboux.rho, schr, h1, glue_dot, dotProduct_zero, zero_dotProduct, zero_add,
      glue_add_zero]
  · funext x
    have h1 := he u
    obtain ⟨hu1, hu2⟩ := hI u hu
    rw [hu1, hu2, map_zero] at h1
    simp only [restr_apply, Darboux.rho, schr, h1, Prod.fst_zero, Prod.snd_zero, glue_dot, dotProduct_zero,
      zero_dotProduct, add_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]
    rw [glue_add_zero, add_zero]
  · refine ⟨GlobalTheory.ThK.AdaptEv.Restr.restrS F eq, fun v => restr eq, GlobalTheory.ThK.AdaptEv.Restr.restrS_ne_zero F eq,
      fun v => ⟨?_, ?_⟩, fun f φ _ _ => restr_pure eq f φ⟩
    · show restr eq (vacGlue eq (l v) (M₁.vac v)) = M₁.vac v
      rw [restr_vacGlue, (hl v).2, one_smul]
    · refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun g hg => restr_mem_SB eq g hg) fun φ hφ => ?_
      refine ⟨vacGlue eq (l v) φ, (GlobalTheory.ThK.AdaptEv.sb_restrL_prodVac eq).2 (l v) (hl v).1 φ hφ, ?_⟩
      rw [restr_vacGlue, (hl v).2, one_smul]

end GlobalTheory.ThK.PlaneCo.GlueEv
