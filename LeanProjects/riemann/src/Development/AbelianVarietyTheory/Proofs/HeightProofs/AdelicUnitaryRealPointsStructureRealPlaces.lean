import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms.RealPts

theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem gramAt_herm {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem gramAt_unit {D : D7} (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)

theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem finMat_eq {D : D7} (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem glue {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    (∀ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → g ∈ GfC V) ∧
    ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
      ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.image (tauE D)
  have hm : ∀ σ, σ ∈ Ψ ↔ ∃ τ, tauE D τ = σ := fun σ => by simp [Ψ]
  choose s hs using fun σ : Ψ => (hm σ.1).1 σ.2
  have hst : ∀ τ, s ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩ = τ := fun τ => tauE_injective D (hs _)
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (s σ))
    (fun σ => by rw [hm, hm]; exact tauE_cm D σ) (fun σ => by rw [← hs σ]; exact hθ (s σ))
  refine ⟨fun g hg => h1 g fun σ => hg (s σ), fun u hu => ?_⟩
  obtain ⟨h, hh, hhu⟩ := h4 (fun σ => u (s σ)) (fun σ => by rw [← hs σ]; exact hu (s σ))
  refine ⟨h, hh, fun τ => ?_⟩
  have := hhu ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩
  simp only [hst] at this
  exact this

theorem realPoints : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  intro D
  refine ⟨fun θ θ' h h' => funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ), fun θ hθ V => ?_⟩
  obtain ⟨g1, g2⟩ := glue θ hθ V
  obtain ⟨s1, s2, s3, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  have hmul : ∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
      infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g' := fun g g' τ => by
    rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]
  have hfin : ∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1 := fun k hk τ => by
    have hk' : infHom V k = 1 := hk
    rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun τ => ⟨gramAt_herm V τ, gramAt_unit V τ⟩, g2, fun g hg g' hg' h => ?_, hmul, hfin, s2,
    fun g => ?_, fun g a ha => ?_⟩
  · refine mul_inv_eq_one.1 (s3 _ (mul_mem hg (inv_mem hg')) (g1 _ fun τ => ?_))
    rw [hmul, h, ← hmul, mul_inv_cancel, hfin 1 (one_mem _)]
  · obtain ⟨a, ha, k, hk, e⟩ := s1 g
    exact ⟨k, hk, a, ha, e.trans (s2 a ha k hk)⟩
  · have ha' : finHom V a = 1 := ha
    rw [finMat_eq V, finMat_eq V, map_mul, ha', mul_one]

end GlobalTheory.SmoothForms.RealPts

end
