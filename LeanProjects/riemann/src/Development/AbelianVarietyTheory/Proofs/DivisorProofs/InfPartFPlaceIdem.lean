import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.WeilPartsF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def GfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (infPartF F E)).comp (matHomF σ J)).ker

def GinfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (finPartF F E)).comp (matHomF σ J)).ker

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

structure IsUnitaryOnThetaF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f

structure IsInfWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)

section Lemmas

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E} {ψ : AddChar (AF F) ℂ}

theorem heisOF_add (w : WOF F E nS nT) (f g : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (f + g) = heisOF σ JS JT xi0 ψ w f + heisOF σ JS JT xi0 ψ w g := by
  funext x
  simp only [heisOF, Pi.add_apply, mul_add]

theorem heisOF_smul (c : ℂ) (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (c • f) = c • heisOF σ JS JT xi0 ψ w f := by
  funext x
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add {f g : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    IsThetaFunOF σ JS JT xi0 ψ (f + g) where
  quasi γ w := by
    simp only [Pi.add_apply]
    rw [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    obtain ⟨V, hV, hV'⟩ := hg.level
    exact ⟨U ⊓ V, hU.inter hV, fun u hu h0 => by rw [heisOF_add, hU' u hu.1 h0, hV' u hu.2 h0]⟩
  cont := hf.cont.add hg.cont
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)

theorem theta_zero : IsThetaFunOF σ JS JT xi0 ψ (0 : WOF F E nS nT → ℂ) where
  quasi γ w := by simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext x; simp [heisOF]⟩
  cont := continuous_const
  smooth k L hL h0 w := contDiff_const

theorem theta_smul (c : ℂ) {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) :
    IsThetaFunOF σ JS JT xi0 ψ (c • f) where
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisOF_smul, hU' u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c

variable (σ JS JT xi0 ψ) in

def thetaSubF : Submodule ℂ (WOF F E nS nT → ℂ) where
  carrier := {f | IsThetaFunOF σ JS JT xi0 ψ f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : GAF σ J) : mtF σ J (g * g') = mtF σ J g * mtF σ J g' := by
  unfold mtF
  rw [map_mul]
  rfl

theorem actOF_mul (g g' : GAF σ JS) (h h' : GAF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT (g * g') (h * h') u = actOF σ JS JT g h (actOF σ JS JT g' h' u) := by
  unfold actOF
  rw [_root_.mul_inv_rev, mtF_mul, mtF_mul]
  simp only [Matrix.mul_assoc]

theorem mem_GfCF_of_supp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AEF F E} (ha : infPartF F E a = 0) {g : GAF σ J}
    (hg : ∀ i j, a * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j) : g ∈ GfCF σ J := by
  rw [GfCF, MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPartF F E ((mtF σ J g - 1) i j) = 0 := by rw [← hg i j, map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  show infPartF F E (mtF σ J g i j) = ((1 : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix _ _ _) i j
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem infPartF_placeIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdemF F v ε) :
    infPartF F E (algebraMap (AF F) (AEF F E) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfCF_of_suppAt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ J}
    (hg : SuppAtF σ e J g) : g ∈ GfCF σ J := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfCF_of_supp (h2 ▸ infPartF_placeIdem h1) hg

theorem isHeckeCharF_pow {η : (AEF F E)ˣ →* Circle} (h : IsHeckeCharF η) (n : ℕ) : IsHeckeCharF (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEtaF_pow {η : (AEF F E)ˣ →* Circle} (h : ResEtaF η 1) (n : ℕ) : ResEtaF (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

end Lemmas

end GlobalTheory.WeilPartsF

end
