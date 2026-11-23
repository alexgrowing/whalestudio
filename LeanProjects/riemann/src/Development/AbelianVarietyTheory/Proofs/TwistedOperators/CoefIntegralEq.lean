import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) : WO V W :=
  HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D))

def meanX {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)) (F : WO V W → ℂ)
    (x : WO V W) : ℂ :=
  ∫ y in 𝓨, F (emb V W P Q y + x) ∂μ

theorem emb_add {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y y' : Mx D a b) :
    emb V W P Q (y + y') = emb V W P Q y + emb V W P Q y' := by
  simp only [emb, Matrix.mul_add, Matrix.add_mul]

theorem emb_zero {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : emb V W P Q (0 : Mx D a b) = 0 := by
  simp [emb]

theorem meanX_translate : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∀ y₀ : Mx D a b, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F (GlobalTheory.IsoMean.emb V W P Q y₀ + x) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F x := by
  intro D V W a b P Q hiso ψ hψ μ 𝓨 hμ F hF x hx y₀
  obtain ⟨hHaar, h𝓨, -⟩ := hμ
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  set f : Mx D a b → ℂ := fun y => F (emb V W P Q y + x) with hf
  have per : ∀ γ ∈ ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range, ∀ y, f (γ + y) = f y := by
    rintro _ ⟨γ, rfl⟩ y
    have hr : emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
      simp [emb, ratW, Matrix.map_mul]
    simp only [hf]
    rw [emb_add, add_assoc, hr, hF.quasi, ← hr, l2, hH0 _ _ (hiso _ _), skew, hH0 _ _ (hx _), neg_zero,
      add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have e1 : meanX V W P Q μ 𝓨 F (emb V W P Q y₀ + x) = ∫ y in 𝓨, f (y₀ + y) ∂μ := by
    unfold meanX
    congr 1; funext y
    simp only [hf, emb_add]
    congr 1; abel
  rw [e1]
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have hmp : MeasurePreserving (fun y : Mx D a b => y₀ + y) μ μ := measurePreserving_add_left μ y₀
  have hemb : MeasurableEmbedding (fun y : Mx D a b => y₀ + y) := (MeasurableEquiv.addLeft y₀).measurableEmbedding
  haveI : Countable (Matrix (Fin a) (Fin b) D.host.E) := inferInstanceAs (Countable (Fin a → Fin b → D.host.E))
  haveI : Countable (((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range) := (Set.countable_range _).to_subtype
  rw [← hmp.setIntegral_image_emb hemb f 𝓨]
  haveI : VAddInvariantMeasure (Mx D a b) (Mx D a b) μ := ⟨fun c s _ => measure_preimage_add μ c s⟩
  have h2 := h𝓨.vadd_of_comm y₀
  rw [← Set.image_vadd] at h2
  exact h2.setIntegral_eq h𝓨 fun g y => per g g.2 y

theorem coef_integral_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (κ : Measure (Mx D a b)), κ.IsAddHaarMeasure → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν) ∂κ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) f u * star (f' u) ∂ν) ∂κ := by
  intro D V W a b P Q ψ χS χT ω hω κ hκ g h hfix hunip ν 𝓕 hν h𝓕 f f' hf hf' w hw
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  have hψ := hω.std
  obtain ⟨y₀, hy₀⟩ := hunip w hw
  have key : ∀ y : Mx D a b,
      ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν =
        ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q y) f u * star (f' u) ∂ν := by
    intro y
    have e : ω (g, h) (heisO ψ V W (w + emb V W P Q y) f) =
        heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) := by
      have hadd : actO V W g h (w + emb V W P Q y) = actO V W g h w + actO V W g h (emb V W P Q y) := by
        simp only [actO, Matrix.mul_add, Matrix.add_mul]
      rw [hω.om_heis g h _ f hf, hadd, hy₀, hfix, emb_add, add_assoc]
    rw [← e]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V W ν 𝓕 hν h𝓕 (ω (g, h)) (fun f hf => hω.om_pres _ f hf)
      (fun f hf => hω.om_unit ν 𝓕 hν h𝓕 _ f hf) _ f' (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf'
  rw [← integral_add_left_eq_self _ y₀]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end GlobalTheory.IsoMean

end
