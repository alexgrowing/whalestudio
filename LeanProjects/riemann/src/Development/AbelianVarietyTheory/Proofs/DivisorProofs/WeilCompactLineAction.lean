import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.RealLift

namespace GlobalTheory.AdCompactLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_mem_UAt {d : ℕ} {W : Spc F E d} (k g : UA σ W.J) (hg : g ∈ UAt σ W (evI F)) :
    k * g * k⁻¹ ∈ UAt σ W (evI F) := by
  intro u hu
  have h0 : u • (mat g - 1) = 0 := hg u hu
  have h1 : mat k * mat k⁻¹ = 1 := by
    show ((k * k⁻¹ : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1
    rw [mul_inv_cancel]
    rfl
  have h2 : mat (k * g * k⁻¹) - 1 = mat k * (mat g - 1) * mat k⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rfl
  show u • (mat (k * g * k⁻¹) - 1) = 0
  rw [h2, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem conj_mem_lines {d : ℕ} {W : Spc F E d} (k : UA σ W.J) (δ : Multiplicative ℝ →* UA σ W.J) (hδ : δ ∈ Lines σ W) :
    (MulAut.conj k).toMonoidHom.comp δ ∈ Lines σ W :=
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Matrix (Fin d) (Fin d) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  ⟨show Continuous fun t => k * δ t * k⁻¹ from (continuous_const.mul hδ.1).mul continuous_const,
    fun t => conj_mem_UAt k (δ t) (hδ.2 t)⟩

theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  have hrest : Rest (evI F) (⇑f) (fun x => g fun i => (x i).2) :=
    ⟨fun x z hz => by
      show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero], Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  exact h _ hrest

theorem actsD_conj : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb, ∀ δ ∈ Lines σ W, ∃ ε ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb,
      ∀ f₁ f₂ f₃ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f f₂ →
        Acts (evI F) (om (1, k)) f₂ f₃ → ActsD (evI F) (fun t => om (1, ε (Multiplicative.ofAdd t))) f₁ f₃ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp k _hk γ hγ
  refine ⟨_, conj_mem_lines k γ hγ, fun f hf f₁ f₂ f₃ h₁ h₂ h₃ => ?_⟩
  have hb := hp.base
  have hX := hp.herm
  have hW := hp.skew
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
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hp.weil
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := GlobalTheory.RealLift.Main.i_liescalar hP hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _
    hb.cm hb.std fr hΦ hsp2
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.RealLift.Main.i_genex F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨T0, rfl⟩ := GlobalTheory.RealLift.Main.pol_eq B M Φ hr hf
  obtain ⟨D, hSD⟩ : ∃ D, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D := ⟨_, hc γ hγ Yg hY T0⟩
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) D D).1 _ (fun t => map_zero _) hSD
  have e0 : f₂ = D := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) f₂ D).2.2.1 _ h₂ hAD
  subst e0
  have hSD2 : SD (fun t => om (1, k * γ (Multiplicative.ofAdd t) * k⁻¹)) f₁ f₃ := by
    intro g hg l hl
    have hl' : l ∘ₗ om (1, k) ∈ (adeleClass F).adm (Fin n × Fin d) := hsp.adm (1, k) l hl
    have e1 := sa_of_acts h₁ g hg
    have e2 := sa_of_acts h₃ g hg
    have e3 : ∀ t : ℝ, om (1, k * γ (Multiplicative.ofAdd t) * k⁻¹) (pureA F (⇑f₁) g) =
        om (1, k) (om (1, γ (Multiplicative.ofAdd t)) (pureA F (⇑(Φ T0)) g)) := by
      intro t
      have hq : ((1 : UA σ X.J), k * γ (Multiplicative.ofAdd t) * k⁻¹) * (1, k) = (1, k) * (1, γ (Multiplicative.ofAdd t)) :=
        Prod.ext (by simp) (by simp)
      rw [← e1, ← Module.End.mul_apply, ← map_mul, hq, map_mul, Module.End.mul_apply]
    simp only [e3]
    have := hSD g hg _ hl'
    simpa only [LinearMap.comp_apply, e2] using this
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f₁ f₃ f₃).1 _ (fun t => map_zero _) hSD2

end GlobalTheory.AdCompactLine

end
