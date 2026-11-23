import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBound
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Twist (resM resM_resM app_resM)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChainPts.SummandNorm

open GlobalTheory.VB (IsFrame)
open GlobalTheory.ChainPts.FrameNorm

theorem repr_map_eq_sum {R M N ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Fintype ι] (b : Module.Basis ι R M) (b' : Module.Basis κ R N) (φ : M →ₗ[R] N) (u : M) (m : κ) :
    b'.repr (φ u) m = ∑ l, b.repr u l * b'.repr (φ (b l)) m := by
  conv_lhs => rw [← b.sum_repr u]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem repr_proj {R M N ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (b' : Module.Basis κ R N) (φ : M →ₗ[R] N) (σ : κ → ι) (hσ : Function.Injective σ)
    (h : ∀ k, φ (b (σ k)) = b' k) (h0 : ∀ j, j ∉ Set.range σ → φ (b j) = 0) (u : M) (k : κ) :
    b'.repr (φ u) k = b.repr u (σ k) := by
  classical
  have : b'.coord k ∘ₗ φ = b.coord (σ k) := by
    refine b.ext fun j => ?_
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨k', rfl⟩ := hj
      simp [h, Finsupp.single_apply, hσ.eq_iff]
    · have : j ≠ σ k := fun e => hj ⟨k, e.symm⟩
      simp [h0 j hj, Finsupp.single_apply, this]
  exact LinearMap.congr_fun this u

theorem sum_extend {C ι κ : Type} [Field C] [Fintype ι] [Fintype κ] (σ : κ → ι) (hσ : Function.Injective σ)
    (cf : κ → C) (g : ι → C) : ∑ j, Function.extend σ cf 0 j * g j = ∑ k, cf k * g (σ k) := by
  symm
  refine Fintype.sum_of_injective σ hσ _ _ (fun j hj => ?_) fun k => by rw [hσ.extend_apply]
  rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, zero_mul]

theorem norm_le_of_rel {X : Scheme.{0}} {ι κ n : Type} [Fintype κ] [Fintype n] {V V₁ U : X.Opens}
    (a : ι → n → Γ(X, V ⊓ U)) (c : κ → n → Γ(X, V₁ ⊓ U)) {V₀ : X.Opens} (B : ι → κ → Γ(X, V₀))
    (hB : ∀ (W : X.Opens) (h₀ : W ≤ V₀) (h : W ≤ V ⊓ U) (h₁ : W ≤ V₁ ⊓ U) (m : ι) (k : n),
      resG X h (a m k) = ∑ l, resG X h₀ (B m l) * resG X h₁ (c l k))
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X)
    (hw : ⊤ ≤ w ⁻¹ᵁ V₀) (hV₁ : ⊤ ≤ w ⁻¹ᵁ V₁) (cf : n → C)
    (H : ∀ l, ‖∑ k, cf k * valF (spMap (intO C).subtype ≫ w) _ (c l k)‖ ≤ 1) (m : ι) :
    ‖∑ k, cf k * valF (spMap (intO C).subtype ≫ w) _ (a m k)‖ ≤ 1 := by
  by_cases hx : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ (V ⊓ U)
  · have hU : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ ((V₀ ⊓ V₁) ⊓ (V ⊓ U)) :=
      fun q hq => ⟨⟨hw (Set.mem_univ (spMap (intO C).subtype q)), hV₁ (Set.mem_univ (spMap (intO C).subtype q))⟩, hx hq⟩
    have h₀ : (V₀ ⊓ V₁) ⊓ (V ⊓ U) ≤ V₀ := inf_le_left.trans inf_le_left
    have h₁ : (V₀ ⊓ V₁) ⊓ (V ⊓ U) ≤ V₁ ⊓ U := inf_le_inf inf_le_right inf_le_right
    have h : (V₀ ⊓ V₁) ⊓ (V ⊓ U) ≤ V ⊓ U := inf_le_right
    have key : ∀ k, valF (spMap (intO C).subtype ≫ w) _ (a m k) =
        ∑ l, valF (spMap (intO C).subtype ≫ w) _ (B m l) *
          valF (spMap (intO C).subtype ≫ w) _ (c l k) := fun k => by
      rw [← valHom_resG _ h hU, hB _ h₀ h h₁, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, valHom_resG, valHom_resG]
    have eq : ∑ k, cf k * valF (spMap (intO C).subtype ≫ w) _ (a m k) =
        ∑ l, valF (spMap (intO C).subtype ≫ w) _ (B m l) *
          ∑ k, cf k * valF (spMap (intO C).subtype ≫ w) _ (c l k) := by
      simp only [key, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [eq]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (norm_valF_le_one C w _ hw _) (norm_nonneg _) (H l)
  · simp only [valF, dif_neg hx, mul_zero, Finset.sum_const_zero, norm_zero, zero_le_one]

section Rel

variable {X : Scheme.{0}} {F F₁ : X.Modules} {i : F₁ ⟶ F} {q : F ⟶ F₁} {r r' : ℕ} {σ : Fin r' → Fin r}
  {U V V₁ : X.Opens} {s : Fin r → Γ(F, U)} {f : Fin r → Γ(F, V)} {e : Fin r' → Γ(F₁, V₁)}

theorem repr_app_proj (hσ : Function.Injective σ) (hs : IsFrame s) (h0 : ∀ j, j ∉ Set.range σ → q.app U (s j) = 0)
    (h₁ : IsFrame fun k => q.app U (s (σ k))) {W : X.Opens} (h : W ≤ U) (u : Γ(F, W)) (k : Fin r') :
    (h₁.basis h).repr (q.app W u) k = (hs.basis h).repr u (σ k) :=
  repr_proj (hs.basis h) (h₁.basis h) (appLinear q W) σ hσ
    (fun k => by rw [appLinear_apply, IsFrame.basis_apply, IsFrame.basis_apply, app_resM])
    (fun j hj => by rw [appLinear_apply, IsFrame.basis_apply, app_resM, h0 j hj, map_zero]) u k

theorem exists_rel_left (hσ : Function.Injective σ) (hs : IsFrame s)
    (hi : ∀ k, i.app U (q.app U (s (σ k))) = s (σ k)) (h0 : ∀ j, j ∉ Set.range σ → q.app U (s j) = 0)
    (h₁ : IsFrame fun k => q.app U (s (σ k))) (hf : IsFrame f) (he : IsFrame e) (d : Bool) :
    ∃ B : Fin r → Fin r' → Γ(X, V ⊓ V₁), ∀ (W : X.Opens) (h₀ : W ≤ V ⊓ V₁) (h : W ≤ V ⊓ U) (h' : W ≤ V₁ ⊓ U)
      (m : Fin r) (k : Fin r'),
      resG X h (coef d hf hs m (σ k)) = ∑ l, resG X h₀ (B m l) * resG X h' (coef d he h₁ l k) := by
  cases d
  · refine ⟨fun m l => (hf.basis inf_le_left).repr (resM F inf_le_right (i.app V₁ (e l))) m,
      fun W h₀ h h' m k => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    conv_lhs => rw [← hi k, ← app_resM, ← appLinear_apply]
    rw [repr_map_eq_sum (he.basis (h₀.trans inf_le_right))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, IsFrame.basis_apply, appLinear_apply, app_resM]
  · refine ⟨fun m l => (he.basis inf_le_right).repr (resM F₁ inf_le_left (q.app V (f m))) l,
      fun W h₀ h h' m k => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    rw [← repr_app_proj hσ hs h0 h₁, app_resM, repr_eq_sum (he.basis (h₀.trans inf_le_right))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [IsFrame.basis_apply]

theorem exists_rel_right (hiq : i ≫ q = 𝟙 F₁) (hσ : Function.Injective σ) (hs : IsFrame s)
    (h0 : ∀ j, j ∉ Set.range σ → q.app U (s j) = 0)
    (h₁ : IsFrame fun k => q.app U (s (σ k))) (hf : IsFrame f) (he : IsFrame e) (d : Bool) :
    ∃ B : Fin r' → Fin r → Γ(X, V ⊓ V₁), ∀ (W : X.Opens) (h₀ : W ≤ V ⊓ V₁) (h' : W ≤ V₁ ⊓ U) (h : W ≤ V ⊓ U)
      (l : Fin r') (k : Fin r'),
      resG X h' (coef d he h₁ l k) = ∑ m, resG X h₀ (B l m) * resG X h (coef d hf hs m (σ k)) := by
  cases d
  · refine ⟨fun l m => (he.basis inf_le_right).repr (resM F₁ inf_le_left (q.app V (f m))) l,
      fun W h₀ h' h l k => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    rw [← app_resM, ← appLinear_apply, repr_map_eq_sum (hf.basis (h₀.trans inf_le_left))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm, IsFrame.basis_apply, appLinear_apply, app_resM]
  · refine ⟨fun l m => (hf.basis inf_le_left).repr (resM F inf_le_right (i.app V₁ (e l))) m,
      fun W h₀ h' h l k => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    have hq : ∀ u : Γ(F₁, W), q.app W (i.app W u) = u := fun u => by
      rw [app_app, hiq]; rfl
    conv_lhs => rw [← hq (resM F₁ _ (e l))]
    rw [repr_app_proj hσ hs h0 h₁, app_resM, repr_eq_sum (hf.basis (h₀.trans inf_le_left))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [IsFrame.basis_apply]

end Rel

theorem norm_le_one_iff : ∀ {X : Scheme.{0}} {F F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁), i ≫ q = 𝟙 F₁ → ∀ {r r' : ℕ} (σ : Fin r' → Fin r), Function.Injective σ → ∀ {U V V₁ : X.Opens} (s : Fin r → Γ(F, U)) (hs : GlobalTheory.VB.IsFrame s), (∀ k, i.app U (q.app U (s (σ k))) = s (σ k)) → (∀ j, j ∉ Set.range σ → q.app U (s j) = 0) → ∀ (h₁ : GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k)))) (f : Fin r → Γ(F, V)) (hf : GlobalTheory.VB.IsFrame f) (e : Fin r' → Γ(F₁, V₁)) (he : GlobalTheory.VB.IsFrame e) (d : Bool) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ w ⁻¹ᵁ V₁ → ∀ cf : Fin r' → C, (∀ l, ‖∑ j, Function.extend σ cf 0 j * valF (spMap (intO C).subtype ≫ w) _ (coef d hf hs l j)‖ ≤ 1) ↔ ∀ l, ‖∑ k, cf k * valF (spMap (intO C).subtype ≫ w) _ (coef d he h₁ l k)‖ ≤ 1 := by
  intro X F F₁ i q hiq r r' σ hσ U V V₁ s hs hi h0 h₁ f hf e he d C _ _ w hV hV₁ cf
  simp only [sum_extend σ hσ]
  have hw : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V₁) := fun q hq => ⟨hV hq, hV₁ hq⟩
  obtain ⟨A, hA⟩ := exists_rel_left hσ hs hi h0 h₁ hf he d
  obtain ⟨B, hB⟩ := exists_rel_right hiq hσ hs h0 h₁ hf he d
  exact ⟨norm_le_of_rel _ (fun m k => coef d hf hs m (σ k)) B hB C w hw hV cf,
    norm_le_of_rel (fun m k => coef d hf hs m (σ k)) _ A hA C w hw hV₁ cf⟩

end GlobalTheory.ChainPts.SummandNorm

end
