import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteDimensionalCoeffSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnIdent

variable {D : D7}

theorem uj_neg_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (-J) * (g : Matrix (Fin n) (Fin n) A) = -J ↔
    Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uh_neg_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem gramAt_neg_eq (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem mem_GQ_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V := by
  cases ε
  · exact Iff.rfl
  · constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq]; exact hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq] at hx; exact hx, e⟩

theorem mem_GfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V := Iff.rfl

theorem mem_GinfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V :=
  Iff.rfl

theorem uh_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  cases ε
  · rfl
  · rw [gramAt_neg_eq, uh_neg_eq]

theorem lieAt_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) : lieAt (sgn ε V) τ = lieAt V τ := by
  cases ε
  · rfl
  · ext X
    show Xᴴ * gramAt D (neg V) τ + gramAt D (neg V) τ * X = 0 ↔ Xᴴ * gramAt D V τ + gramAt D V τ * X = 0
    rw [gramAt_neg_eq, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

theorem isAtTau_sgn (θ : InfFam D) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (sgn ε V)) : IsAtTau θ (sgn ε V) τ g x ↔ IsAtTau θ V τ g (ofSgn ε V x) := Iff.rfl

theorem atTau_sgn (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g := by
  by_cases h : ∃ x, IsAtTau θ V τ g x
  · have h₁ : ∃ x, IsAtTau θ (sgn ε V) τ g x := by
      obtain ⟨x, hx⟩ := h
      refine ⟨(ofSgn ε V).symm x, (isAtTau_sgn θ ε V τ g _).2 ?_⟩
      rw [MulEquiv.apply_symm_apply]; exact hx
    have a : IsAtTau θ (sgn ε V) τ g (atTau θ (sgn ε V) τ g) := by
      unfold atTau; rw [dif_pos h₁]; exact h₁.choose_spec
    have b : IsAtTau θ V τ g (atTau θ V τ g) := by
      unfold atTau; rw [dif_pos h]; exact h.choose_spec
    exact GlobalTheory.Published.AutFin.Model.isAtTau_unique θ V hθ ((isAtTau_sgn θ ε V τ g _).1 a) b
  · have h₁ : ¬ ∃ x, IsAtTau θ (sgn ε V) τ g x := fun ⟨x, hx⟩ => h ⟨_, (isAtTau_sgn θ ε V τ g x).1 hx⟩
    have a : atTau θ (sgn ε V) τ g = 1 := by unfold atTau; rw [dif_neg h₁]
    have b : atTau θ V τ g = 1 := by unfold atTau; rw [dif_neg h]
    rw [a, b, map_one]

theorem meas_sgn (ε : Bool) (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν := by
  obtain ⟨-, -, -, hb, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, -, -, hb₁, hg₁, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (sgn ε V)
  let h : GA D (sgn ε V) ≃ₜ GA D V :=
    { toEquiv := (ofSgn ε V).toEquiv, continuous_toFun := continuous_ofSgn ε V,
      continuous_invFun := continuous_ofSgn_symm ε V }
  have me : MeasurableEmbedding (ofSgn ε V) := h.toMeasurableEquiv.measurableEmbedding
  have hm : Measurable (ofSgn ε V) := (continuous_ofSgn ε V).measurable
  have hm' : Measurable (ofSgn ε V).symm := (continuous_ofSgn_symm ε V).measurable
  have mp : MeasurePreserving (ofSgn ε V) (ν.map (ofSgn ε V).symm) ν := by
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm hm']
    have : (⇑(ofSgn ε V) ∘ ⇑(ofSgn ε V).symm) = id := funext fun x => (ofSgn ε V).apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨ν.map (ofSgn ε V).symm,
    (ofSgn ε V).symm.isHaarMeasure_map ν (continuous_ofSgn_symm ε V) (continuous_ofSgn ε V), ?_, fun φ => ?_⟩
  · refine h𝓕.preimage_of_equiv mp.quasiMeasurePreserving
      (e := fun γ : GQ V => (⟨(ofSgn ε V).symm γ, (mem_GQ_sgn ε V _).2 (by rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩ :
        GQ (sgn ε V))) ⟨fun a b hab => ?_, fun δ => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((ofSgn ε V).symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ofSgn ε V δ, (mem_GQ_sgn ε V δ).1 δ.2⟩, Subtype.ext ((ofSgn ε V).symm_apply_apply δ)⟩
    · show ofSgn ε V ((ofSgn ε V).symm (γ : GA D V) * x) = (γ : GA D V) * ofSgn ε V x
      rw [map_mul, MulEquiv.apply_symm_apply]
  · exact ⟨mp.integrableOn_comp_preimage me, mp.setIntegral_preimage_emb me φ 𝓕⟩

theorem sgnLaw_holds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V :=
  fun _ θ hθ ε V => ⟨mem_GQ_sgn ε V, mem_GfC_sgn ε V, mem_GinfC_sgn ε V, uh_sgn ε V, lieAt_sgn ε V,
    fun τ g => atTau_sgn θ hθ ε V τ g, fun ν 𝓕 hν h𝓕 => meas_sgn ε V ν 𝓕 hν h𝓕⟩

end GlobalTheory.SgnIdent

end
