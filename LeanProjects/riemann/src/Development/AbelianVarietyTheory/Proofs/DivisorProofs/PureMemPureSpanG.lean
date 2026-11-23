import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivOpSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaNonvanishing

noncomputable section

namespace GlobalTheory.ThetaFibMaxG

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThetaFibMax
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def pureSpanG (M : Model σ Y W) (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) : Submodule ℂ (Fn F n d) :=
  Submodule.span ℂ {Φ | ∃ f ∈ P, ∃ φ, Gd φ ∧ Φ = pure f φ}

abbrev DG (B : Base F E) (M : Model σ Y W) (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) :
    Submodule ℂ (Fn F n d) :=
  pureSpanG M Gd (M.Pol B.ψ B.emb)

theorem pureSpanG_mono (M : Model σ Y W) (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop)
    {P Q : Submodule ℂ (SInf F (Fin n × Fin d))} (h : P ≤ Q) : pureSpanG M Gd P ≤ pureSpanG M Gd Q := by
  apply Submodule.span_mono
  rintro _ ⟨f, hf, φ, h1, rfl⟩
  exact ⟨f, h hf, φ, h1, rfl⟩

section Gen

variable (M : Model σ Y W) (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop)

theorem pureSpanG_deriv (P : Submodule ℂ (SInf F (Fin n × Fin d))) (T : ℝ → Module.End ℂ (Fn F n d))
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP : ∀ f ∈ P, ∃ f₁ ∈ P, ActsD (evI F) (fun t => T t) f f₁) :
    ∀ Φ ∈ pureSpanG M Gd P, ∃ Φ₁ ∈ pureSpanG M Gd P, ∀ x, HasDerivAt (fun t => T t Φ x) (Φ₁ x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, rfl⟩ := hy
    obtain ⟨f₁, hf₁, hact⟩ := hP f hf
    exact ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, hf₁, φ, h1, rfl⟩,
      hasDerivAt_pure' φ (hGd φ h1).1 (good_std hstd (hGd φ h1)) hact⟩
  | zero => exact ⟨0, zero_mem _, fun x => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add y z _ _ hy hz =>
    obtain ⟨y₁, hy₁, hyd⟩ := hy
    obtain ⟨z₁, hz₁, hzd⟩ := hz
    refine ⟨y₁ + z₁, add_mem hy₁ hz₁, fun x => ?_⟩
    have h2 := (hyd x).add (hzd x)
    have e : ((fun t => T t y x) + fun t => T t z x) = fun t => T t (y + z) x := by
      funext t; simp [map_add]
    rw [e] at h2
    simpa using h2
  | smul c y _ hy =>
    obtain ⟨y₁, hy₁, hyd⟩ := hy
    refine ⟨c • y₁, Submodule.smul_mem _ c hy₁, fun x => ?_⟩
    have h2 := (hyd x).const_mul c
    have e : (fun t => c * T t y x) = fun t => T t (c • y) x := by
      funext t; simp [map_smul]
    rw [e] at h2
    simpa using h2

theorem pureSpanG_acts (P : Submodule ℂ (SInf F (Fin n × Fin d))) (T : Module.End ℂ (Fn F n d))
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP : ∀ f ∈ P, ∃ f₁ ∈ P, Acts (evI F) T f f₁) :
    ∀ Φ ∈ pureSpanG M Gd P, T Φ ∈ pureSpanG M Gd P := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, rfl⟩ := hy
    obtain ⟨f₁, hf₁, hact⟩ := hP f hf
    rw [acts_pure' φ (hGd φ h1).1 (good_std hstd (hGd φ h1)) hact]
    exact Submodule.subset_span ⟨f₁, hf₁, φ, h1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

end Gen

end GlobalTheory.ThetaFibMaxG

namespace GlobalTheory.ThetaFibMaxG

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThetaFibMax
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

abbrev AlgG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) : Type :=
  Algebra.adjoin ℂ (ops B om (DG B M Gd))

theorem nrG_stable (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) :
    ∀ A ∈ ops B om (DG B M Gd), ∀ x ∈ N.comap (DG B M Gd).subtype, A x ∈ N.comap (DG B M Gd).subtype := by
  rintro A (⟨γ, hγ, hex, rfl⟩ | ⟨k, hk, hk', rfl⟩) x hx
  · exact hN.lie γ hγ x.1 hx _ (derivOp _ _ hex x).2 (derivOp_spec hex x)
  · exact hN.cpt k hk x.1 hx

set_option synthInstance.maxHeartbeats 400000

instance instTowerAlgG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) :
    IsScalarTower ℂ (AlgG B M om Gd) (DG B M Gd) := inferInstance

def NrG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) : Submodule (AlgG B M om Gd) (DG B M Gd) :=
  subOf _ (N.comap (DG B M Gd).subtype) (nrG_stable B M om Gd N hN)

instance instModQG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) : Module (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN) :=
  inferInstance

instance instModQCG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) : Module ℂ (DG B M Gd ⧸ NrG B M om Gd N hN) :=
  inferInstance

instance instTowerQG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) :
    IsScalarTower ℂ (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN) :=
  inferInstance

def iotaG (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Gd φ) :
    M.Pol B.ψ B.emb →ₗ[ℂ] DG B M Gd ⧸ NrG B M om Gd N hN where
  toFun f := Submodule.Quotient.mk ⟨pure f.1 φ, Submodule.subset_span ⟨f.1, f.2, φ, hφ, rfl⟩⟩
  map_add' f g := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact (map_add (GlobalTheory.ThetaFacInf.pureL φ) f.1 g.1)
  map_smul' c f := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact (map_smul (GlobalTheory.ThetaFacInf.pureL φ) c f.1)

theorem iotaG_apply (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Gd φ)
    (f : M.Pol B.ψ B.emb) :
    iotaG B M om Gd N hN φ hφ f =
      (NrG B M om Gd N hN).mkQ ⟨pure f.1 φ, Submodule.subset_span ⟨f.1, f.2, φ, hφ, rfl⟩⟩ :=
  rfl

theorem iotaG_eq_zero (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Gd φ)
    (f : M.Pol B.ψ B.emb) : iotaG B M om Gd N hN φ hφ f = 0 ↔ pure f.1 φ ∈ N := by
  rw [iotaG_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

end GlobalTheory.ThetaFibMaxG

namespace GlobalTheory.ThetaFibMaxG

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThetaFibMax
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

set_option synthInstance.maxHeartbeats 400000

theorem pureSpanG_le (M : Model σ Y W) (B : Base F E) (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : P ≤ M.Pol B.ψ B.emb) : pureSpanG M Gd P ≤ DG B M Gd :=
  pureSpanG_mono M Gd hP

section Core

variable (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (Gd : (∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) → Prop) (N : Submodule ℂ (Fn F n d))
  (hN : GlobalTheory.ThetaFac.WStable B om (DG B M Gd) N)

theorem smul_mk (A : Module.End ℂ (DG B M Gd)) (hA : A ∈ ops B om (DG B M Gd)) (x : DG B M Gd) :
    (⟨A, Algebra.subset_adjoin hA⟩ : AlgG B M om Gd) • (NrG B M om Gd N hN).mkQ x = (NrG B M om Gd N hN).mkQ (A x) := by
  rw [← LinearMap.map_smul]; rfl

theorem mem_pre (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Gd φ)
    (T : Submodule (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN)) (f : SInf F (Fin n × Fin d)) :
    f ∈ ((T.restrictScalars ℂ).comap (iotaG B M om Gd N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype ↔
      ∃ hf : f ∈ M.Pol B.ψ B.emb, iotaG B M om Gd N hN φ hφ ⟨f, hf⟩ ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨f, hf⟩, h, rfl⟩

variable {B M om Gd N hN}

theorem ops_iota
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (A : Module.End ℂ (DG B M Gd)) (hA : A ∈ ops B om (DG B M Gd)) (f : M.Pol B.ψ B.emb) :
    ∃ f₁ : M.Pol B.ψ B.emb, (⟨A, Algebra.subset_adjoin hA⟩ : AlgG B M om Gd) • iotaG B M om Gd N hN φ hφ f =
      iotaG B M om Gd N hN φ hφ f₁ ∧
      ∀ P : Submodule ℂ (SInf F (Fin n × Fin d)), GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P → f.1 ∈ P → f₁.1 ∈ P := by
  have hs := good_std hstd (hGd φ hφ)
  rw [iotaG_apply, smul_mk B M om Gd N hN A hA]
  rcases hA with ⟨γ, hγ, hex, rfl⟩ | ⟨k, hk, hk', rfl⟩
  · obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f.1 f.2
    refine ⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.1 γ hγ f.1 hfP f₁ hact⟩
    rw [iotaG_apply]
    congr 1
    exact Subtype.ext (derivOp_eq hex _ _ (hasDerivAt_pure' φ (hGd φ hφ).1 hs hact))
  · obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f.1 f.2
    refine ⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.2 k hk f.1 hfP f₁ hact⟩
    rw [iotaG_apply]
    congr 1
    exact Subtype.ext (acts_pure' φ (hGd φ hφ).1 hs hact)

theorem exists_img
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P) :
    ∃ T : Submodule (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN),
      ∀ q, q ∈ T ↔ ∃ f : M.Pol B.ψ B.emb, f.1 ∈ P ∧ iotaG B M om Gd N hN φ hφ f = q := by
  refine ⟨quotSub _ (NrG B M om Gd N hN) ((P.comap (M.Pol B.ψ B.emb).subtype).map (iotaG B M om Gd N hN φ hφ)) ?_,
    fun q => ?_⟩
  · intro A hA x hx
    obtain ⟨f, hfP, hfx⟩ := hx
    obtain ⟨f₁, he, hP'⟩ := ops_iota hstd hGd hP3 hP4 hφ A hA f
    refine ⟨f₁, hP' P hP hfP, ?_⟩
    rw [← smul_mk B M om Gd N hN A hA x, ← hfx, he]
  · rw [mem_quotSub]
    constructor
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩

theorem coinv_lie
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (DG B M Gd) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (γ) (hγ : γ ∈ Lines σ Y) (f) (hf : f ∈ M.Pol B.ψ B.emb) (f₁ : SInf F (Fin n × Fin d))
    (h : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁) :
    f₁ ∈ M.Pol B.ψ B.emb ∧ pure f₁ φ ∈ N := by
  have hs := good_std hstd (hGd φ hφ)
  have h₁ := hP1 γ hγ f hf f₁ h
  exact ⟨h₁, hNc.lie γ hγ _ (Submodule.subset_span ⟨f, hf, φ, hφ, rfl⟩) _
    (Submodule.subset_span ⟨f₁, h₁, φ, hφ, rfl⟩) (hasDerivAt_pure' φ (hGd φ hφ).1 hs h)⟩

theorem coinv_cpt
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (DG B M Gd) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (k) (hk : k ∈ KInf σ Y B.emb) (f) (hf : f ∈ M.Pol B.ψ B.emb) (f₁ : SInf F (Fin n × Fin d))
    (h : Acts (evI F) (om (k, 1)) f f₁) :
    f₁ ∈ M.Pol B.ψ B.emb ∧ pure (f₁ - f) φ ∈ N := by
  have hs := good_std hstd (hGd φ hφ)
  refine ⟨hP2 k hk f hf f₁ h, ?_⟩
  have e : pure (f₁ - f) φ = om (k, 1) (pure f φ) - pure f φ := by
    rw [acts_pure' φ (hGd φ hφ).1 hs h, ← GlobalTheory.ThetaFacInf.pureL_apply, ← GlobalTheory.ThetaFacInf.pureL_apply,
      ← GlobalTheory.ThetaFacInf.pureL_apply, map_sub]
  rw [e]
  exact hNc.cpt k hk _ (Submodule.subset_span ⟨f, hf, φ, hφ, rfl⟩)

theorem thetaSub_pre
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (DG B M Gd) N)
    (hexD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ DG B M Gd, ∃ Φ₁ ∈ DG B M Gd,
      ∀ x, HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0)
    (hkD : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ DG B M Gd, om (1, k) Φ ∈ DG B M Gd)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (P₀ : Submodule ℂ (SInf F (Fin n × Fin d))) (hP₀ : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P₀)
    (T : Submodule (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN)) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om
      (P₀ ⊓ ((T.restrictScalars ℂ).comap (iotaG B M om Gd N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype) := by
  have hs := good_std hstd (hGd φ hφ)
  refine ⟨inf_le_left.trans hP₀.1, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h
    obtain ⟨h1, h2⟩ := coinv_lie hstd hGd hP1 hNc hφ γ hγ f hf f₁ h
    refine ⟨hP₀.2.1 γ hγ f hf f₁ h, (mem_pre B M om Gd N hN φ hφ T f₁).2 ⟨h1, ?_⟩⟩
    rw [(iotaG_eq_zero B M om Gd N hN φ hφ ⟨f₁, h1⟩).2 h2]
    exact zero_mem _
  · intro k hk f hf f₁ h
    obtain ⟨h1, h2⟩ := coinv_cpt hstd hGd hP2 hNc hφ k hk f hf f₁ h
    refine ⟨hP₀.2.2.1 k hk f hf f₁ h, (mem_pre B M om Gd N hN φ hφ T (f₁ - f)).2 ⟨sub_mem h1 hf, ?_⟩⟩
    rw [(iotaG_eq_zero B M om Gd N hN φ hφ ⟨f₁ - f, sub_mem h1 hf⟩).2 h2]
    exact zero_mem _
  · intro γ hγ f hf f₁ h
    obtain ⟨hfP₀, hfpre⟩ := hf
    obtain ⟨hfPol, hfT⟩ := (mem_pre B M om Gd N hN φ hφ T f).1 hfpre
    have hf₁P₀ := hP₀.2.2.2.1 γ hγ f hfP₀ f₁ h
    have hf₁Pol := hP₀.1 hf₁P₀
    refine ⟨hf₁P₀, (mem_pre B M om Gd N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩
    have hA : derivOp (DG B M Gd) (fun t => om (1, γ (Multiplicative.ofAdd t))) (hexD γ hγ) ∈
        ops B om (DG B M Gd) := Or.inl ⟨γ, hγ, hexD γ hγ, rfl⟩
    have e : iotaG B M om Gd N hN φ hφ ⟨f₁, hf₁Pol⟩ =
        (⟨_, Algebra.subset_adjoin hA⟩ : AlgG B M om Gd) • iotaG B M om Gd N hN φ hφ ⟨f, hfPol⟩ := by
      rw [iotaG_apply, iotaG_apply, smul_mk B M om Gd N hN _ hA]
      congr 1
      exact Subtype.ext (derivOp_eq (hexD γ hγ) _ _ (hasDerivAt_pure' φ (hGd φ hφ).1 hs h)).symm
    rw [e]
    exact T.smul_mem _ hfT
  · intro k hk f hf f₁ h
    obtain ⟨hfP₀, hfpre⟩ := hf
    obtain ⟨hfPol, hfT⟩ := (mem_pre B M om Gd N hN φ hφ T f).1 hfpre
    have hf₁P₀ := hP₀.2.2.2.2 k hk f hfP₀ f₁ h
    have hf₁Pol := hP₀.1 hf₁P₀
    refine ⟨hf₁P₀, (mem_pre B M om Gd N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩
    have hA : (om (1, k)).restrict (hkD k hk) ∈ ops B om (DG B M Gd) := Or.inr ⟨k, hk, hkD k hk, rfl⟩
    have e : iotaG B M om Gd N hN φ hφ ⟨f₁, hf₁Pol⟩ =
        (⟨_, Algebra.subset_adjoin hA⟩ : AlgG B M om Gd) • iotaG B M om Gd N hN φ hφ ⟨f, hfPol⟩ := by
      rw [iotaG_apply, iotaG_apply, smul_mk B M om Gd N hN _ hA]
      congr 1
      exact Subtype.ext (acts_pure' φ (hGd φ hφ).1 hs h).symm
    rw [e]
    exact T.smul_mem _ hfT

theorem sup_wstable
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P)
    (hfin : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ pureSpanG M Gd P, om (1, h) Φ ∈ pureSpanG M Gd P)
    (hNm : GlobalTheory.ThetaFac.IsMaxTh B om (DG B M Gd) N) :
    GlobalTheory.ThetaFac.WStable B om (DG B M Gd) (N ⊔ pureSpanG M Gd P) := by
  have hPl : P ≤ M.Pol B.ψ B.emb := hP.1
  refine ⟨?_, ?_, ?_⟩
  · intro v h hh Φ hΦ
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (hNm.stab.fin v h hh a ha) (hfin v h hh b hb)
  · intro γ hγ Φ hΦ Φ₁ _ hder
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨a₁, ha₁D, ha₁⟩ := pureSpanG_deriv M Gd (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd hGd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩) a (hNm.le ha)
    have ha₁N := hNm.stab.lie γ hγ a ha a₁ ha₁D ha₁
    obtain ⟨b₁, hb₁, hb₁d⟩ := pureSpanG_deriv M Gd P (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd hGd
      (fun f hf => by
        obtain ⟨f₁, -, hact, -⟩ := hP3 γ hγ f (hPl hf)
        exact ⟨f₁, hP.2.2.2.1 γ hγ f hf f₁ hact, hact⟩) b hb
    have e : Φ₁ = a₁ + b₁ := by
      funext x
      have h2 := (ha₁ x).add (hb₁d x)
      have e2 : ((fun t => om (1, γ (Multiplicative.ofAdd t)) a x) + fun t => om (1, γ (Multiplicative.ofAdd t)) b x) =
          fun t => om (1, γ (Multiplicative.ofAdd t)) (a + b) x := by
        funext t; simp [map_add]
      rw [e2] at h2
      exact (hder x).unique h2
    rw [e]
    exact Submodule.add_mem_sup ha₁N hb₁
  · intro k hk Φ hΦ
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    refine Submodule.add_mem_sup (hNm.stab.cpt k hk a ha) (pureSpanG_acts M Gd P (om (1, k)) hstd hGd (fun f hf => ?_) b hb)
    obtain ⟨f₁, -, hact, -⟩ := hP4 k hk f (hPl hf)
    exact ⟨f₁, hP.2.2.2.2 k hk f hf f₁ hact, hact⟩

theorem span_top (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hPl : P ≤ M.Pol B.ψ B.emb)
    (hS : N ⊔ pureSpanG M Gd P = DG B M Gd) (q : DG B M Gd ⧸ NrG B M om Gd N hN) :
    q ∈ Submodule.span (AlgG B M om Gd) {q | ∃ φ, ∃ hφ : Gd φ, ∃ f : M.Pol B.ψ B.emb, f.1 ∈ P ∧
      iotaG B M om Gd N hN φ hφ f = q} := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  have hx : x.1 ∈ N ⊔ pureSpanG M Gd P := by rw [hS]; exact x.2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
  have hbD : b ∈ DG B M Gd := pureSpanG_le M B Gd P hPl hb
  have e : (Submodule.Quotient.mk x : DG B M Gd ⧸ NrG B M om Gd N hN) = Submodule.Quotient.mk ⟨b, hbD⟩ := by
    rw [Submodule.Quotient.eq]
    show x.1 - b ∈ N
    rw [← hab, add_sub_cancel_right]
    exact ha
  rw [e]
  clear e hab ha hx
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, rfl⟩ := hy
    exact Submodule.subset_span ⟨φ, h1, ⟨f, hPl hf⟩, hf, rfl⟩
  | zero =>
    have : (⟨0, hbD⟩ : DG B M Gd) = 0 := rfl
    rw [this, Submodule.Quotient.mk_zero]
    exact zero_mem _
  | add y z hy hz ihy ihz =>
    have hyD := pureSpanG_le M B Gd P hPl hy
    have hzD := pureSpanG_le M B Gd P hPl hz
    have : (⟨y + z, hbD⟩ : DG B M Gd) = ⟨y, hyD⟩ + ⟨z, hzD⟩ := rfl
    rw [this, Submodule.Quotient.mk_add]
    exact add_mem (ihy hyD) (ihz hzD)
  | smul c y hy ihy =>
    have hyD := pureSpanG_le M B Gd P hPl hy
    have : (⟨c • y, hbD⟩ : DG B M Gd) = c • ⟨y, hyD⟩ := rfl
    rw [this, Submodule.Quotient.mk_smul]
    exact Submodule.smul_of_tower_mem _ c (ihy hyD)

theorem core
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hGd : ∀ φ, Gd φ → Good M φ)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (hfin : ∀ P : Submodule ℂ (SInf F (Fin n × Fin d)), ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ pureSpanG M Gd P,
      om (1, h) Φ ∈ pureSpanG M Gd P)
    (hchain : ∃ L : ℕ, ∀ (m : ℕ) (c : Fin m → Submodule ℂ (SInf F (Fin n × Fin d))), StrictMono c →
      (∀ i, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (c i)) → m ≤ L)
    (hsum : ∀ P P', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' →
      P ≠ M.Pol B.ψ B.emb → P' ≠ M.Pol B.ψ B.emb → P ⊔ P' ≠ M.Pol B.ψ B.emb)
    (hNm : GlobalTheory.ThetaFac.IsMaxTh B om (DG B M Gd) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Gd φ)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P)
    (hne : P ≠ M.Pol B.ψ B.emb) : P ≤ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
  classical
  set hN := hNm.stab
  have hexD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ DG B M Gd, ∃ Φ₁ ∈ DG B M Gd,
      ∀ x, HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0 := fun γ hγ =>
    pureSpanG_deriv M Gd (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd hGd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩)
  have hkD : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ DG B M Gd, om (1, k) Φ ∈ DG B M Gd := fun k hk =>
    pureSpanG_acts M Gd (M.Pol B.ψ B.emb) (om (1, k)) hstd hGd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f hf; exact ⟨f₁, hf₁, hact⟩)
  have hPolT : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (M.Pol B.ψ B.emb) := by
    refine ⟨le_rfl, fun γ hγ f hf f₁ h => hP1 γ hγ f hf f₁ h,
      fun k hk f hf f₁ h => sub_mem (hP2 k hk f hf f₁ h) hf, fun γ hγ f hf f₁ h => ?_, fun k hk f hf f₁ h => ?_⟩
    · obtain ⟨f₂, hf₂, -, hu⟩ := hP3 γ hγ f hf
      rw [hu f₁ h]; exact hf₂
    · obtain ⟨f₂, hf₂, -, hu⟩ := hP4 k hk f hf
      rw [hu f₁ h]; exact hf₂
  have dich : ∀ P' : Submodule ℂ (SInf F (Fin n × Fin d)), GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' →
      N ⊔ pureSpanG M Gd P' = N ∨ N ⊔ pureSpanG M Gd P' = DG B M Gd := fun P' hP' =>
    hNm.max _ le_sup_left (sup_le hNm.le (pureSpanG_le M B Gd P' hP'.1))
      (sup_wstable hstd hGd hP3 hP4 P' hP' (hfin P') hNm)
  obtain ⟨L, hL⟩ := hchain
  obtain ⟨Pm, ⟨hPmT, hPmS⟩, hPmin⟩ := exists_minimal_of_chain (GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om) L hL
    {P' | GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' ∧ N ⊔ pureSpanG M Gd P' = DG B M Gd} (fun _ hx => hx.1)
    (M.Pol B.ψ B.emb) ⟨hPolT, le_antisymm (sup_le hNm.le le_rfl) le_sup_right⟩

  have hatom : ∀ (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ' : Gd φ')
      (T : Submodule (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN)),
      (∀ q, q ∈ T ↔ ∃ f : M.Pol B.ψ B.emb, f.1 ∈ Pm ∧ iotaG B M om Gd N hN φ' hφ' f = q) → T = ⊥ ∨ IsAtom T := by
    intro φ' hφ' T hT
    by_cases hT0 : T = ⊥
    · exact Or.inl hT0
    right
    refine ⟨hT0, fun T' hT' => ?_⟩
    have hpreT := thetaSub_pre (hN := hN) hstd hGd hP1 hP2 hNm.coinv hexD hkD hφ' Pm hPmT T'
    set pre := Pm ⊓ ((T'.restrictScalars ℂ).comap (iotaG B M om Gd N hN φ' hφ')).map (M.Pol B.ψ B.emb).subtype
      with hpre
    have hpre_ne : pre ≠ Pm := by
      intro he
      apply (lt_iff_le_and_ne.1 hT').2
      refine le_antisymm hT'.le fun q hq => ?_
      obtain ⟨f, hfPm, rfl⟩ := (hT q).1 hq
      have hf : f.1 ∈ pre := by rw [he]; exact hfPm
      obtain ⟨hf', hfT'⟩ := (mem_pre B M om Gd N hN φ' hφ' T' f.1).1 hf.2
      exact hfT'
    have hlt : pre < Pm := lt_of_le_of_ne inf_le_left hpre_ne
    have hSpre : N ⊔ pureSpanG M Gd pre = N :=
      (dich pre hpreT).resolve_right fun h => hPmin pre ⟨hpreT, h⟩ hlt
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨f, hfPm, rfl⟩ := (hT q).1 (hT'.le hq)
    have hfpre : f.1 ∈ pre := ⟨hfPm, (mem_pre B M om Gd N hN φ' hφ' T' f.1).2 ⟨f.2, hq⟩⟩
    have hfN : pure f.1 φ' ∈ N := by
      rw [← hSpre]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨f.1, hfpre, φ', hφ', rfl⟩)
    rw [Submodule.mem_bot]
    exact (iotaG_eq_zero B M om Gd N hN φ' hφ' f).2 hfN

  have hss : IsSemisimpleModule (AlgG B M om Gd) (DG B M Gd ⧸ NrG B M om Gd N hN) := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro q _
    refine (Submodule.span_le.2 ?_) (span_top (hN := hN) Pm hPmT.1 hPmS q)
    rintro _ ⟨φ', hφ', f, hfPm, rfl⟩
    obtain ⟨T, hT⟩ := exists_img (hN := hN) hstd hGd hP3 hP4 hφ' Pm hPmT
    have hmem : iotaG B M om Gd N hN φ' hφ' f ∈ T := (hT _).2 ⟨f, hfPm, rfl⟩
    rcases hatom φ' hφ' T hT with h0 | ha
    · rw [h0, Submodule.mem_bot] at hmem
      rw [SetLike.mem_coe, hmem]
      exact zero_mem _
    · exact Submodule.mem_sSup_of_mem (isSimpleModule_iff_isAtom.2 ha) hmem

  by_contra hPK
  obtain ⟨f, hfP, hfN⟩ := SetLike.not_le_iff_exists.1 hPK
  obtain ⟨TP, hTP⟩ := exists_img (hN := hN) hstd hGd hP3 hP4 hφ P hP
  have hTP0 : TP ≠ ⊥ := by
    intro h0
    apply hfN
    have h1 := (hTP _).2 ⟨⟨f, hP.1 hfP⟩, hfP, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (iotaG_eq_zero B M om Gd N hN φ hφ ⟨f, hP.1 hfP⟩).1 h1
  obtain ⟨C, hC⟩ := exists_isCompl TP
  have hP'T := thetaSub_pre (hN := hN) hstd hGd hP1 hP2 hNm.coinv hexD hkD hφ (M.Pol B.ψ B.emb) hPolT C
  set P' := M.Pol B.ψ B.emb ⊓ ((C.restrictScalars ℂ).comap (iotaG B M om Gd N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype
    with hP'
  have hP'ne : P' ≠ M.Pol B.ψ B.emb := by
    intro he
    apply hTP0
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨g, hgP, rfl⟩ := (hTP q).1 hq
    have hg : g.1 ∈ P' := by rw [he]; exact g.2
    obtain ⟨_, hgC⟩ := (mem_pre B M om Gd N hN φ hφ C g.1).1 hg.2
    rw [Submodule.mem_bot]
    exact Submodule.disjoint_def.1 hC.disjoint _ hq hgC
  have hsup : P ⊔ P' = M.Pol B.ψ B.emb := by
    refine le_antisymm (sup_le hP.1 hP'T.1) fun g hg => ?_
    have htop : iotaG B M om Gd N hN φ hφ ⟨g, hg⟩ ∈ TP ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 htop
    obtain ⟨p, hpP, rfl⟩ := (hTP a).1 ha
    have hgp : g - p.1 ∈ P' := by
      refine ⟨sub_mem hg p.2, (mem_pre B M om Gd N hN φ hφ C (g - p.1)).2 ⟨sub_mem hg p.2, ?_⟩⟩
      have e : iotaG B M om Gd N hN φ hφ ⟨g - p.1, sub_mem hg p.2⟩ =
          iotaG B M om Gd N hN φ hφ ⟨g, hg⟩ - iotaG B M om Gd N hN φ hφ p := by
        rw [← map_sub]; rfl
      rw [e, ← hac, add_sub_cancel_left]
      exact hc
    have e2 : g = p.1 + (g - p.1) := by abel
    rw [e2]
    exact Submodule.add_mem_sup hpP hgp
  exact hsum P P' hP hP'T hne hP'ne hsup

end Core

end GlobalTheory.ThetaFibMaxG

end
