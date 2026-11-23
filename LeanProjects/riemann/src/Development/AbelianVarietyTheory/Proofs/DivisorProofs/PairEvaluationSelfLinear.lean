import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalsLagrangian

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThK.EvChangeUniq

def ratInc (F R κ : Type) [Field F] [CommRing R] [Algebra F R] : ((κ → F) × (κ → F)) →ₗ[F] ((κ → R) × (κ → R)) where
  toFun w := (fun i => algebraMap F R (w.1 i), fun i => algebraMap F R (w.2 i))
  map_add' a b := by ext <;> simp
  map_smul' a b := by ext <;> simp [Algebra.smul_def]

theorem ratInc_injective (F R κ : Type) [Field F] [CommRing R] [Algebra F R] (h : Function.Injective (algebraMap F R)) :
    Function.Injective (ratInc F R κ) := by
  intro a b hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  exact Prod.ext (funext fun i => h (congrFun h1 i)) (funext fun i => h (congrFun h2 i))

theorem exists_rat {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V]
    (h : Function.Injective (algebraMap F R)) (c : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) :
    ∃ q : V →ₗ[F] ((κ → F) × (κ → F)), ∀ x, ratInc F R κ (q x) = c x := by
  have hmem : ∀ x, c x ∈ LinearMap.range (ratInc F R κ) := fun x => by
    obtain ⟨w, hw⟩ := hc x
    exact ⟨w, hw.symm⟩
  refine ⟨(LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm.toLinearMap ∘ₗ c.codRestrict _ hmem, fun x => ?_⟩
  have := LinearEquiv.ofInjective_apply (ratInc F R κ) (h := ratInc_injective F R κ h)
    ((LinearEquiv.ofInjective _ (ratInc_injective F R κ h)).symm (c.codRestrict _ hmem x))
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_lagrangian {F R κ V : Type} [Field F] [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V] [Fintype κ]
    [FiniteDimensional F V] (hV : Module.finrank F V = Fintype.card κ + Fintype.card κ)
    (h : Function.Injective (algebraMap F R)) (c c₁ : V →ₗ[F] ((κ → R) × (κ → R)))
    (hc : ∀ x, ∃ w, c x = ratInc F R κ w) (hc₁ : ∀ x, ∃ w, c₁ x = ratInc F R κ w)
    (hi : Function.Injective c) (hi₁ : Function.Injective c₁)
    (hf : ∀ x y, (c x).1 ⬝ᵥ (c y).2 - (c y).1 ⬝ᵥ (c x).2 = (c₁ x).1 ⬝ᵥ (c₁ y).2 - (c₁ y).1 ⬝ᵥ (c₁ x).2) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧ ∀ w ∈ L, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
  obtain ⟨q, hq⟩ := exists_rat h c hc
  obtain ⟨q₁, hq₁⟩ := exists_rat h c₁ hc₁
  have hqi : Function.Injective q := fun a b hab => hi (by rw [← hq, ← hq, hab])
  have hqi₁ : Function.Injective q₁ := fun a b hab => hi₁ (by rw [← hq₁, ← hq₁, hab])
  have hqs : Function.Surjective q₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).1 hqi₁
  let K : Submodule F V := LinearMap.ker (LinearMap.fst F _ _ ∘ₗ q₁)
  have hK : Module.finrank F K = Fintype.card κ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.fst F _ _ ∘ₗ q₁)
    have h2 : LinearMap.range (LinearMap.fst F _ _ ∘ₗ q₁) = ⊤ :=
      LinearMap.range_eq_top.2 (Prod.fst_surjective.comp hqs)
    rw [h2, finrank_top, hV, Module.finrank_fintype_fun_eq_card] at h1
    exact Nat.add_left_cancel h1
  have hL : ∀ w ∈ K.map q, ∃ x, ratInc F R κ w = c x ∧ (c₁ x).1 = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hq x, ?_⟩
    have hx' : (q₁ x).1 = 0 := hx
    rw [← hq₁]
    funext i
    simp [ratInc, hx']
  refine ⟨K.map q, fun a ha b hb => ?_, ?_, hL⟩
  · obtain ⟨x, hx, hx0⟩ := hL a ha
    obtain ⟨y, hy, hy0⟩ := hL b hb
    have h1 := hf x y
    rw [hx0, hy0, ← hx, ← hy, zero_dotProduct, zero_dotProduct, sub_zero, sub_eq_zero] at h1
    apply h
    simpa [dotProduct, ratInc] using h1
  · rw [← hK]
    exact (Submodule.equivMapOfInjective q hqi K).finrank_eq.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incL (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n d : ℕ) :
    Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
  LinearMap.mapMatrix (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap

theorem incL_injective (n d : ℕ) : Function.Injective (incL F E n d) := by
  intro a b hab
  ext i j
  exact Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun (congrFun hab i) j)

theorem eq_smul_isEv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev f hfh
  have hψ : IsStd B.ψ := hpair.base.std
  have hM : M.IsGood B.ψ := hpair.good
  have h2 : Module.finrank F E = 2 := hpair.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let ev0 : Fn F n d →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0
  have hmem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  have hrec : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ y, S Φ y = ev0 (S (M.co.rho B.ψ (M₁.co.e.symm (y, 0)) Φ)) := by
    intro S hS Φ hΦ y
    rw [hS _ Φ hΦ]
    simp [ev0, Darboux.rho, schr]
  obtain ⟨L, hiso, hrk, hL⟩ := exists_lagrangian (F := F) (R := AF F) (κ := Fin n × Fin d) (V := Matrix (Fin n) (Fin d) E)
    (by rw [Module.finrank_matrix, h2]; simp; ring) (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
    (M.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d) (M₁.co.e.toLinearMap.restrictScalars F ∘ₗ incL F E n d)
    (fun x => by obtain ⟨y, z, h⟩ := hM.rat x; exact ⟨(y, z), h⟩)
    (fun x => by obtain ⟨y, z, h⟩ := hM₁.rat x; exact ⟨(y, z), h⟩)
    (M.co.e.injective.comp (incL_injective n d)) (M₁.co.e.injective.comp (incL_injective n d))
    (fun x y => (M.co.form _ _).symm.trans (M₁.co.form _ _))
  have inv : ∀ S : Fn F n d →ₗ[ℂ] Fn F n d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ Φ ∈ schA F (Fin n × Fin d),
        (ev0 ∘ₗ S) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) Φ) =
          (ev0 ∘ₗ S) Φ := by
    intro S hS t w hw Φ hΦ
    obtain ⟨x, hx, hx0⟩ := hL w hw
    have hx' : ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) = M.co.e (incM F x) := hx
    have hx1 : (M₁.co.e (incM F x)).1 = 0 := hx0
    have hz : (M₁.co.e (t • incM F x)).1 = 0 := by rw [map_smul, Prod.smul_fst, hx1, smul_zero]
    have he : schr B.ψ (t • M.co.e (incM F x)) Φ = M.co.rho B.ψ (t • incM F x) Φ := by
      rw [Darboux.rho, map_smul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hx', he, hS _ Φ hΦ]
    generalize t • incM F x = z at hz
    simp [ev0, Darboux.rho, schr, hz]
  have hevh : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (e Φ) := by
    intro z Φ hΦ
    have := hev.Heisenberg₂ z Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => by simp [incM]
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  obtain ⟨ei, ev, hei, hloc0, hloc⟩ := hev.loc
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem' : Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem'
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨g, hg⟩ : ∃ g, ei g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  have hΦ₀ : pure g φ ∈ schA F (Fin n × Fin d) := (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd).2
  have hne : e (pure g φ) ≠ 0 := by
    rw [hloc g φ hφSB hcof, show (fun v => ev v (φ v)) = fun v =>
      Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 from funext hφev]
    intro h0
    apply hg
    apply GlobalTheory.ThK.EvUniqInf.eq_of_pure_std (ei g) 0
    rw [h0]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.SvNLinear.main hK.base F B.ψ hψ (Fin n × Fin d) L hiso hrk (ev0 ∘ₗ f) (ev0 ∘ₗ e) (inv f hfh) (inv e hevh)
    ⟨M.co.rho B.ψ (M₁.co.e.symm (y₀, 0)) (pure g φ), hmem _ _ hΦ₀, by
      rw [LinearMap.comp_apply, ← hrec e hevh _ hΦ₀ y₀]; exact hy₀⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [hrec f hfh Φ hΦ y, Pi.smul_apply, hrec e hevh Φ hΦ y, smul_eq_mul]
  exact hc _ (hmem _ _ hΦ)

end GlobalTheory.ThK.EvChangeUniq
