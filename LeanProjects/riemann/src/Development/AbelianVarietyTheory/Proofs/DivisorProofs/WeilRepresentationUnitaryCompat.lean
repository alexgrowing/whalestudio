import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.RealLift

namespace GlobalTheory.ConjLineSecond

theorem actsD_conj : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ActsD (evI F) (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T f) (T f₁) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW _hM hw g _hg h _hh T hT hTs γ hγ f hf f₁ hf₁
  have hder := GlobalTheory.RealLift.Main.i_derex
  have hvl := GlobalTheory.RealLift.Main.i_vacline hder
  have hfe := GlobalTheory.RealLift.Main.i_fockex hder
  choose A hA hAθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.RealLift.Main.i_polrange GlobalTheory.RealLift.actsLaws hder hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm
    hb.std fr hAθ hCθ hΦ
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hw
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := GlobalTheory.RealLift.Main.i_liescalar hK.base hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _
    hb.cm hb.std fr hΦ hsp2
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.RealLift.Main.i_genex F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨T0, rfl⟩ := GlobalTheory.RealLift.Main.pol_eq B M Φ hr hf
  obtain ⟨D, hSD⟩ : ∃ D, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D := ⟨_, hc γ hγ Yg hY T0⟩
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) D D).1 _ (fun t => map_zero _) hSD
  have e0 : f₁ = D := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) f₁ D).2.2.1 _ hf₁ hAD
  subst e0
  have hSD2 : SD (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T (Φ T0)) (T f₁) := by
    intro g' hg' l hl
    have hl' : l ∘ₗ om (g, h) ∈ (adeleClass F).adm (Fin n × Fin d) := hsp.adm (g, h) l hl
    have hrest : ∀ f0 : SInf F (Fin n × Fin d), Rest (evI F) (⇑f0) (fun x => g' fun i => (x i).2) := fun f0 =>
      ⟨fun x z hz => by
        show g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
        congr 1
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero], Submodule.subset_span ⟨f0, g', hg', rfl⟩⟩
    have hpure : ∀ f0 : SInf F (Fin n × Fin d), pureA F (⇑f0) g' = tens (evI F) (⇑f0) (fun x => g' fun i => (x i).2) :=
      fun _ => rfl
    have e1 : om (g⁻¹, h⁻¹) (pureA F (⇑(T (Φ T0))) g') = pureA F (⇑(Φ T0)) g' := by
      rw [hpure, hTs _ _ (hrest _), LinearEquiv.symm_apply_apply]
      rfl
    have e2 : om (g, h) (pureA F (⇑f₁) g') = pureA F (⇑(T f₁)) g' := by
      rw [hpure, hT _ _ (hrest _)]
      rfl
    have e3 : ∀ t : ℝ, om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹) (pureA F (⇑(T (Φ T0))) g') =
        om (g, h) (om (1, γ (Multiplicative.ofAdd t)) (pureA F (⇑(Φ T0)) g')) := by
      intro t
      have hp : ((1 : UA σ X.J), h * γ (Multiplicative.ofAdd t) * h⁻¹) = (g, h) * (1, γ (Multiplicative.ofAdd t)) * (g⁻¹, h⁻¹) :=
        Prod.ext (by simp) (by simp)
      rw [hp, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1]
    simp only [e3]
    have := hSD g' hg' _ hl'
    simpa only [LinearMap.comp_apply, e2] using this
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T (Φ T0)) (T f₁) (T f₁)).1 _ (fun t => map_zero _) hSD2

end GlobalTheory.ConjLineSecond
