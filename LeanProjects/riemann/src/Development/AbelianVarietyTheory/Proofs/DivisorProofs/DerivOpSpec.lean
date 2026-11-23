import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply

noncomputable section

namespace GlobalTheory.ThetaFibMax

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

section Deriv

variable {α : Type} (D : Submodule ℂ (α → ℂ)) (T : ℝ → Module.End ℂ (α → ℂ))

def derivOp (hex : ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x, HasDerivAt (fun t => T t Φ x) (Φ₁ x) 0) : Module.End ℂ D where
  toFun Φ := ⟨(hex Φ.1 Φ.2).choose, (hex Φ.1 Φ.2).choose_spec.1⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    have h1 := (hex Φ.1 Φ.2).choose_spec.2 x
    have h2 := (hex Ψ.1 Ψ.2).choose_spec.2 x
    have h3 := (hex (Φ + Ψ).1 (Φ + Ψ).2).choose_spec.2 x
    have h4 : HasDerivAt (fun t => T t (Φ + Ψ).1 x) ((hex Φ.1 Φ.2).choose x + (hex Ψ.1 Ψ.2).choose x) 0 := by
      have e : (fun t => T t (Φ + Ψ).1 x) = fun t => T t Φ.1 x + T t Ψ.1 x := by
        funext t; simp [map_add]
      rw [e]; exact h1.add h2
    exact h3.unique h4
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    have h1 := (hex Φ.1 Φ.2).choose_spec.2 x
    have h3 := (hex (c • Φ).1 (c • Φ).2).choose_spec.2 x
    have h4 : HasDerivAt (fun t => T t (c • Φ).1 x) (c * (hex Φ.1 Φ.2).choose x) 0 := by
      have e : (fun t => T t (c • Φ).1 x) = fun t => c * T t Φ.1 x := by
        funext t; simp [map_smul]
      rw [e]; exact h1.const_mul c
    exact h3.unique h4

variable {D T}

theorem derivOp_spec (hex : ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x, HasDerivAt (fun t => T t Φ x) (Φ₁ x) 0) (Φ : D) (x : α) :
    HasDerivAt (fun t => T t Φ.1 x) (((derivOp D T hex Φ : D) : α → ℂ) x) 0 :=
  (hex Φ.1 Φ.2).choose_spec.2 x

theorem derivOp_eq (hex : ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x, HasDerivAt (fun t => T t Φ x) (Φ₁ x) 0) (Φ : D) (Ψ : α → ℂ)
    (h : ∀ x, HasDerivAt (fun t => T t Φ.1 x) (Ψ x) 0) : ((derivOp D T hex Φ : D) : α → ℂ) = Ψ :=
  funext fun x => (derivOp_spec hex Φ x).unique (h x)

end Deriv

section Adjoin

variable {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M))

def subOf (T : Submodule ℂ M) (hT : ∀ A ∈ s, ∀ x ∈ T, A x ∈ T) : Submodule (Algebra.adjoin ℂ s) M where
  carrier := T
  add_mem' := T.add_mem
  zero_mem' := T.zero_mem
  smul_mem' r x hx := by
    obtain ⟨r, hr⟩ := r
    show r x ∈ T
    induction hr using Algebra.adjoin_induction generalizing x with
    | mem A hA => exact hT A hA x hx
    | algebraMap c => simpa using T.smul_mem c hx
    | add A A' _ _ h h' => simpa using T.add_mem (h x hx) (h' x hx)
    | mul A A' _ _ h h' => exact h _ (h' x hx)

def quotSub (Nr : Submodule (Algebra.adjoin ℂ s) M) (T : Submodule ℂ (M ⧸ Nr))
    (hT : ∀ A ∈ s, ∀ x : M, Nr.mkQ x ∈ T → Nr.mkQ (A x) ∈ T) : Submodule (Algebra.adjoin ℂ s) (M ⧸ Nr) where
  carrier := T
  add_mem' := T.add_mem
  zero_mem' := T.zero_mem
  smul_mem' r q hq := by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
    obtain ⟨r, hr⟩ := r
    have e : (⟨r, hr⟩ : Algebra.adjoin ℂ s) • Nr.mkQ x = Nr.mkQ (r x) := by
      rw [← LinearMap.map_smul]; rfl
    show (⟨r, hr⟩ : Algebra.adjoin ℂ s) • Nr.mkQ x ∈ T
    rw [e]
    clear e
    induction hr using Algebra.adjoin_induction generalizing x with
    | mem A hA => exact hT A hA x hq
    | algebraMap c =>
      have : Nr.mkQ ((algebraMap ℂ (Module.End ℂ M) c) x) = c • Nr.mkQ x := by
        simp only [Module.algebraMap_end_apply]
        exact (Submodule.Quotient.mk_smul Nr c x)
      rw [this]; exact T.smul_mem c hq
    | add A A' _ _ h h' =>
      have : Nr.mkQ ((A + A') x) = Nr.mkQ (A x) + Nr.mkQ (A' x) := by
        rw [LinearMap.add_apply, map_add]
      rw [this]; exact T.add_mem (h x hq) (h' x hq)
    | mul A A' _ _ h h' => exact h _ (h' x hq)

theorem mem_quotSub (Nr : Submodule (Algebra.adjoin ℂ s) M) (T : Submodule ℂ (M ⧸ Nr))
    (hT : ∀ A ∈ s, ∀ x : M, Nr.mkQ x ∈ T → Nr.mkQ (A x) ∈ T) (q : M ⧸ Nr) : q ∈ quotSub s Nr T hT ↔ q ∈ T :=
  Iff.rfl

end Adjoin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def ops (B : Base F E) (om : Rep σ Y W) (D : Submodule ℂ (Fn F n d)) : Set (Module.End ℂ D) :=
  {A | (∃ γ ∈ Lines σ W, ∃ hex : ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x,
      HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0,
      A = derivOp D (fun t => om (1, γ (Multiplicative.ofAdd t))) hex) ∨
    ∃ k ∈ KInf σ W B.emb, ∃ hk : ∀ Φ ∈ D, om (1, k) Φ ∈ D, A = (om (1, k)).restrict hk}

def pureSpan (M : Model σ Y W) (P : Submodule ℂ (SInf F (Fin n × Fin d))) : Submodule ℂ (Fn F n d) :=
  Submodule.span ℂ {Φ | ∃ f ∈ P, ∃ φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ Φ = pure f φ}

end GlobalTheory.ThetaFibMax

namespace GlobalTheory.ThetaFibMax

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def Good (M : Model σ Y W) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB _) ∧ ∀ᶠ v in Filter.cofinite, φ v = M.vac v

abbrev Alg (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) : Type :=
  Algebra.adjoin ℂ (ops B om (PolData B M))

theorem nr_stable (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) :
    ∀ A ∈ ops B om (PolData B M), ∀ x ∈ N.comap (PolData B M).subtype, A x ∈ N.comap (PolData B M).subtype := by
  rintro A (⟨γ, hγ, hex, rfl⟩ | ⟨k, hk, hk', rfl⟩) x hx
  · exact hN.lie γ hγ x.1 hx _ (derivOp _ _ hex x).2 (derivOp_spec hex x)
  · exact hN.cpt k hk x.1 hx

set_option synthInstance.maxHeartbeats 400000 in
instance instTowerAlg (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) :
    IsScalarTower ℂ (Alg B M om) (PolData B M) := inferInstance

def Nr (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) : Submodule (Alg B M om) (PolData B M) :=
  subOf _ (N.comap (PolData B M).subtype) (nr_stable B M om N hN)

set_option synthInstance.maxHeartbeats 400000 in
instance instModQ (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) : Module (Alg B M om) (PolData B M ⧸ Nr B M om N hN) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instModQC (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) : Module ℂ (PolData B M ⧸ Nr B M om N hN) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instTowerQ (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) : IsScalarTower ℂ (Alg B M om) (PolData B M ⧸ Nr B M om N hN) :=
  inferInstance

def iota (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Good M φ) :
    M.Pol B.ψ B.emb →ₗ[ℂ] PolData B M ⧸ Nr B M om N hN where
  toFun f := Submodule.Quotient.mk ⟨pure f.1 φ, Submodule.subset_span ⟨f.1, f.2, φ, hφ.1, hφ.2, rfl⟩⟩
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

theorem iota_apply (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Good M φ)
    (f : M.Pol B.ψ B.emb) :
    iota B M om N hN φ hφ f = (Nr B M om N hN).mkQ ⟨pure f.1 φ, Submodule.subset_span ⟨f.1, f.2, φ, hφ.1, hφ.2, rfl⟩⟩ :=
  rfl

theorem iota_eq_zero (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Good M φ)
    (f : M.Pol B.ψ B.emb) : iota B M om N hN φ hφ f = 0 ↔ pure f.1 φ ∈ N := by
  rw [iota_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

end GlobalTheory.ThetaFibMax

end
