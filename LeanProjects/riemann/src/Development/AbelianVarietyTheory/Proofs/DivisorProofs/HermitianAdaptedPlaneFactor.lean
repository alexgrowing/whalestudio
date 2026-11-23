import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LagrUniq

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

theorem proj_zero_mem_adm (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem smul_of_commute (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hc : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ w (T φ)) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, T φ = c • φ := by
  obtain ⟨c, hc'⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (ha _ (proj_zero_mem_adm κ)) (fun y φ hφ => by
    have e : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [e, hc _ φ hφ]; simp [schr])
  refine ⟨c, fun φ hφ => funext fun x => ?_⟩
  have h1 := congrFun (hc (x, 0) φ hφ) 0
  have e : schr ψ (x, 0) φ = fun z => φ (z + x) := by funext z; simp [schr]
  have h2 := hc' _ (e ▸ GlobalTheory.SchwartzTranslate.main F κ x φ hφ)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h2
  rw [h1] at h2
  simp [schr] at h2
  simpa [e] using h2

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_model {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hco : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ (vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (T : Fn F n d →ₗ[ℂ] Fn F n d)
      (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
      (⟨co, vac, M.μ, M.dom⟩ : Model σ X W).IsGood B.ψ ∧ Function.Surjective ei ∧
      (∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d)) ∧
      (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ u Φ) = co.rho B.ψ u (T Φ)) ∧
      (∀ v, ev v (M.vac v) = vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
        T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  obtain ⟨T, ei, ev, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hB hX hW hM co hco
  exact ⟨fun v => ev v (M.vac v), T, ei, ev, ⟨hco, h5, h6, hM.haar, hM.dom⟩, h1, h2, h3, fun v => ⟨rfl, h4 v⟩, h7⟩

theorem ne_zero_of_surjective {κ : Type} [Fintype κ] {ei : SInf F κ →L[ℂ] SInf F κ} (h : Function.Surjective ei) :
    ei ≠ 0 := by
  rintro rfl
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  apply h0
  have hle : schA F κ ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, -, rfl⟩
    obtain ⟨f', hf'⟩ := h f
    have : f = 0 := hf'.symm
    subst this
    funext x
    simp [pureA]
  rw [(Submodule.mem_bot ℂ).1 (hle hΦ)]
  rfl

theorem exists_intertwiner {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hco : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ T : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d)) ∧
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Φ ∈ schA F (Fin n × Fin d), T Φ = Ψ) ∧
      (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), T (co.rho B.ψ u Φ) = M.co.rho B.ψ u (T Φ)) ∧
      ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d) := by
  obtain ⟨vac, T₀, ei₀, ev₀, g₀, s₀, m₀, i₀, v₀, p₀⟩ := exists_model hB hX hW hM co hco
  obtain ⟨vac', T, ei, ev, g, s, m, i, v₁, p⟩ := exists_model hB hX hW g₀ M.co hM.rat
  have hT : IsEv B (⟨co, vac, M.μ, M.dom⟩ : Model σ X W) (⟨M.co, vac', M.μ, M.dom⟩ : Model σ X W) 1 1 ∅ T :=
    ⟨m, fun z Φ hΦ => by
      rw [incM_one, incM_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]; exact i z Φ hΦ,
      fun u hu => hu.elim, ei, ev, ne_zero_of_surjective s, v₁, p⟩
  have hTT : IsEv B M (⟨M.co, vac', M.μ, M.dom⟩ : Model σ X W) 1 1 ∅ (T ∘ₗ T₀) := by
    refine ⟨fun Φ hΦ => m _ (m₀ Φ hΦ), fun z Φ hΦ => ?_, fun u hu => hu.elim, ei.comp ei₀, fun v => ev v ∘ₗ ev₀ v,
      ne_zero_of_surjective (s.comp s₀), fun v => ⟨?_, ?_⟩, fun f φ hφ hφv => ?_⟩
    · rw [incM_one, incM_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, LinearMap.comp_apply, i₀ z Φ hΦ]
      exact i z _ (m₀ Φ hΦ)
    · rw [LinearMap.comp_apply, (v₀ v).1]; exact (v₁ v).1
    · rw [Submodule.map_comp, (v₀ v).2, (v₁ v).2]
    · rw [LinearMap.comp_apply, p₀ f φ hφ hφv]
      refine p _ _ (fun v => ?_) ?_
      · rw [← (v₀ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      · filter_upwards [hφv] with v hv
        rw [hv]; exact (v₀ v).1
  obtain ⟨c, hc⟩ := smul_of_commute B.ψ hB.std (T ∘ₗ T₀)
    (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W _ _ 1 1 ∅ _ hM g hTT) (fun w φ hφ => by
      obtain ⟨u, rfl⟩ := M.co.e.surjective w
      show T (T₀ (M.co.rho B.ψ u φ)) = M.co.rho B.ψ u (T (T₀ φ))
      rw [i₀ u φ hφ]
      exact i u _ (m₀ φ hφ))
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d X W X W _ _ 1 1 ∅ _ hM g hTT
    exact h0 (by rw [hc Φ hΦ, zero_smul])
  refine ⟨T, m, fun Ψ hΨ => ⟨c⁻¹ • T₀ Ψ, Submodule.smul_mem _ _ (m₀ Ψ hΨ), ?_⟩, i,
    GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W _ _ 1 1 ∅ _ g₀ g hT⟩
  rw [map_smul, show T (T₀ Ψ) = c • Ψ from hc Ψ hΨ, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem form_unique {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hco : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (l l' : Fn F n d →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) (hl' : l' ∈ (adeleClass F).adm (Fin n × Fin d))
    (hi : ∀ u, (co.e u).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ)
    (hi' : ∀ u, (co.e u).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d), l' (M.co.rho B.ψ u Φ) = l' Φ)
    (h0 : ∃ Φ ∈ schA F (Fin n × Fin d), l Φ ≠ 0) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l' Φ = c * l Φ := by
  obtain ⟨T, m, s, i, a⟩ := exists_intertwiner hB hX hW hM co hco
  have key : ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u, (co.e u).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l (T Φ) = c * Φ 0 := fun l hl hi =>
    GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hB.std _ (l ∘ₗ T) (a l hl) fun y φ hφ => by
      obtain ⟨u, hu⟩ := co.e.surjective (0, y)
      have e : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = co.rho B.ψ u φ := by funext x; simp [Darboux.rho, hu, schr]
      rw [e, LinearMap.comp_apply, LinearMap.comp_apply, i u φ hφ]
      exact hi u (by rw [hu]) _ (m φ hφ)
  obtain ⟨c, hc⟩ := key l hl hi
  obtain ⟨c', hc'⟩ := key l' hl' hi'
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Ψ, hΨ, h⟩ := h0
    obtain ⟨Φ, hΦ, rfl⟩ := s Ψ hΨ
    exact h (by rw [hc Φ hΦ, zero_mul])
  refine ⟨c' / c, fun Ψ hΨ => ?_⟩
  obtain ⟨Φ, hΦ, rfl⟩ := s Ψ hΨ
  rw [hc Φ hΦ, hc' Φ hΦ]
  field_simp

theorem schr_add_of_orth {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w w' : (κ → AF F) × (κ → AF F))
    (h : w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) (φ : (κ → AF F) → ℂ) : schr ψ (w + w') φ = schr ψ w (schr ψ w' φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  have h2 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-⅟(2 : AF F)) * h + (w.1 ⬝ᵥ w'.2) * h2

theorem one_eq_decomp {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ j₀ j₁) :
    ∃ (a b : Fin n → E) (P : Matrix (Fin n₁) (Fin n) E),
      (1 : Matrix (Fin n) (Fin n) E) = Matrix.vecMulVec H.x a + H.ι * P + Matrix.vecMulVec H.y b := by
  have hz : ∀ z : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro z
    have hm : z ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [Submodule.IsLattice.span_eq_top (self := hX.lat)]; trivial
    induction hm using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
      exact ⟨s, t, u, h⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add z z' _ _ h h' =>
      obtain ⟨s, t, u, rfl⟩ := h
      obtain ⟨s', t', u', rfl⟩ := h'
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul c z _ h =>
      obtain ⟨s, t, u, rfl⟩ := h
      exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul]; module⟩
  choose a b u h using fun j : Fin n => hz (Pi.single j 1)
  refine ⟨a, b, Matrix.of fun k j => u j k, ?_⟩
  ext i j
  have := congrFun (h j) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.single_apply] at this
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [this]; ring

theorem exists_decomp {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ (a b : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)),
      u = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z + Matrix.vecMulVec (incV F H.y) b := by
  obtain ⟨a, b, P, h⟩ := one_eq_decomp hX hH
  have h' : (1 : Matrix (Fin n) (Fin n) (AE F E)) =
      Matrix.vecMulVec (incV F H.x) (incV F a) + incM F H.ι * incM F P + Matrix.vecMulVec (incV F H.y) (incV F b) := by
    rw [← incM_one, h]
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum]
  refine ⟨incV F a ᵥ* u, incV F b ᵥ* u, incM F P * u, ?_⟩
  conv_lhs => rw [← Matrix.one_mul u, h']
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.mul_assoc]

end GlobalTheory.LagrUniq

theorem GlobalTheory.LagrUniq.eq_smul_evalZero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ S : Fn F n d →ₗ[ℂ] Fn F n₁ d, (∀ Φ ∈ schA F (Fin n × Fin d), S Φ ∈ schA F (Fin n₁ × Fin d)) →
        (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
          S (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (S Φ)) →
        (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d),
          S (M.co.rho B.ψ u Φ) = S Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ S ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), S Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he S hS hSh hSi hSa
  obtain ⟨j, co, hj, hco, hι, hx, hy⟩ := GlobalTheory.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁
    hP₁.herm hH hP₁.good
  have hψ := hP.base.std
  have hone : ∀ z : Matrix (Fin n₁) (Fin d) (AE F E),
      incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z := fun z => by
    rw [GlobalTheory.LagrUniq.incM_one, Matrix.transpose_one, Matrix.mul_one]
  have hext : Function.extend j (0 : Fin n₁ × Fin d → AF F) (0 : Fin n × Fin d → AF F) = 0 := by
    funext i
    rw [Function.extend_def]
    split_ifs <;> rfl
  have hlag : ∀ u, (co.e u).1 = 0 → ∃ a z, (M₁.co.e z).1 = 0 ∧ u = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z := by
    intro u hu
    obtain ⟨a, b, z, rfl⟩ := GlobalTheory.LagrUniq.exists_decomp hP.herm hH u
    rw [map_add, map_add, Prod.fst_add, Prod.fst_add, (hx a).1, hι z, zero_add] at hu
    have hz : (M₁.co.e z).1 = 0 := by
      funext k
      have := congrFun hu (j k)
      rw [Pi.add_apply, (hy b).2 k, add_zero] at this
      exact (hj.extend_apply (M₁.co.e z).1 0 k).symm.trans this
    have hb : co.e (Matrix.vecMulVec (incV F H.y) b) = 0 := by
      refine Prod.ext ?_ (hy b).1
      rw [hz] at hu
      simpa [hext] using hu
    refine ⟨a, z, hz, ?_⟩
    rw [co.e.map_eq_zero_iff.1 hb, add_zero]
  have key : ∀ S : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
        S (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (S Φ)) →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
        ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ u Φ) = S Φ) →
      ∀ u, (co.e u).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ u Φ) 0 = S Φ 0 := by
    intro S hh hi u hu Φ hΦ
    obtain ⟨a, z, hz, rfl⟩ := hlag u hu
    have h1 : (co.e (incM F H.ι * z)).1 = 0 := by rw [hι z, hz]; exact hext
    have hsy : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F H.x) a) (incM F H.ι * z) = 0 := by
      rw [co.form, (hx a).1, h1]; simp
    have hmul : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z) Φ =
        M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) a) (M.co.rho B.ψ (incM F H.ι * z) Φ) := by
      rw [M.co.form] at hsy
      simp only [Darboux.rho, map_add]
      exact GlobalTheory.LagrUniq.schr_add_of_orth B.ψ _ _ hsy Φ
    rw [hmul, hi _ ⟨a, rfl⟩ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ), ← hone, hh z Φ hΦ]
    simp [Darboux.rho, schr, hz]
  have hval : ∀ S : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z : Matrix (Fin n₁) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d),
        S (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), S Φ x = S (M.co.rho B.ψ (incM F H.ι * M₁.co.e.symm (x, 0)) Φ) 0 := by
    intro S hh x Φ hΦ
    rw [← hone, hh _ Φ hΦ]
    simp [Darboux.rho, schr]
  have hδ := GlobalTheory.LagrUniq.proj_zero_mem_adm (F := F) (Fin n₁ × Fin d)
  obtain ⟨c, hc⟩ := GlobalTheory.LagrUniq.form_unique hP.base hP.herm hP.skew hP.good co hco (LinearMap.proj 0 ∘ₗ e)
    (LinearMap.proj 0 ∘ₗ S) (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ _ _ _ e hP.good hP₁.good he _ hδ) (hSa _ hδ)
    (key e he.Heisenberg₂ he.inv) (key S hSh hSi) (by
      obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n₁ d X W X₁ W M M₁ _ _ _ e hP.good hP₁.good he
      obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
      refine ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (incM F H.ι * M₁.co.e.symm (x, 0)) Φ hΦ, ?_⟩
      rw [hval e he.Heisenberg₂ x Φ hΦ] at hx
      exact hx)
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  rw [Pi.smul_apply, hval S hSh x Φ hΦ, hval e he.Heisenberg₂ x Φ hΦ]
  exact hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ)

end
