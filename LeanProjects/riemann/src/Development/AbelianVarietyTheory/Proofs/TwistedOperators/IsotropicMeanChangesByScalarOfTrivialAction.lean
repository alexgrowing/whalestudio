import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProductsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IsoMean

theorem GlobalTheory.IsoMean.meanX_prod_zero : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f) 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f') 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f' 0) := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip f f' hf hf'
  exact GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products D V W a b P Q hP hQ hiso ψ hω.std μ 𝓨 hμ _ _ _ _ (hω.om_pres _ f hf) (hω.om_pres _ f' hf') hf hf'
    (fun ν 𝓕 hν h𝓕 w hw => GlobalTheory.IsoMean.coef_integral_eq D V W a b P Q ψ χS χT ω hω μ hμ.1 g h hfix hunip ν 𝓕 hν h𝓕 f f'
      hf hf' w hw)

namespace GlobalTheory.IsoMean

theorem mean_scalar : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
  change ∀ y y' : Mx D a b, symplO V W (emb V W P Q y) (emb V W P Q y') = 0 at hiso
  change ∀ y : Mx D a b, actO V W g h (emb V W P Q y) = emb V W P Q y at hfix
  change ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (emb V W P Q y) = 0) →
    ∃ y : Mx D a b, actO V W g h x = x + emb V W P Q y at hunip
  have hψ := hω.std
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  have phase : ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀ y,
      symplOH V W (emb V W P Q y) (x + emb V W P Q y₀) = 0 := fun x hx y₀ y => by
    rw [l2, skew, hH _ _ (hx y), hH _ _ (hiso y y₀), neg_zero, add_zero]

  have hint : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      ∫ y in 𝓨, heisO ψ V W x F (emb V W P Q y) ∂μ = meanX V W P Q μ 𝓨 F x := fun F x hx => by
    unfold meanX heisO
    congr 1; funext y
    have := phase x hx 0 y
    rw [show emb V W P Q (0 : Mx D a b) = 0 by simp [emb], add_zero] at this
    rw [this, AddChar.map_zero_eq_one, one_mul]
  have hmean : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀,
      meanX V W P Q μ 𝓨 (heisO ψ V W (x + emb V W P Q y₀) F) 0 = meanX V W P Q μ 𝓨 F (x + emb V W P Q y₀) :=
    fun F x hx y₀ => by
      unfold meanX heisO
      congr 1; funext y
      rw [add_zero, phase x hx y₀ y, AddChar.map_zero_eq_one, one_mul]
  have hz : emb V W P Q (0 : Mx D a b) = 0 := by simp [emb]

  have hωx : ∀ f, IsThetaFunO ψ V W f → ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (ω (g, h) (heisO ψ V W x f)) 0 = meanX V W P Q μ 𝓨 (ω (g, h) f) x := fun f hf x hx => by
    obtain ⟨y₀, hy₀⟩ := hunip x hx
    rw [hω.om_heis g h x f hf, hy₀, hmean _ x hx y₀, add_comm,
      GlobalTheory.IsoMean.meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ _ (hω.om_pres _ f hf) x hx y₀]
  have hfx : ∀ (f : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (heisO ψ V W x f) 0 = meanX V W P Q μ 𝓨 f x := fun f x hx => by
    have := hmean f x hx 0
    rwa [hz, add_zero] at this
  let Ix := {p : (WO V W → ℂ) × WO V W // IsThetaFunO ψ V W p.1 ∧ ∀ y, symplO V W p.2 (emb V W P Q y) = 0}
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul (X := Ix)
    (fun p => meanX V W P Q μ 𝓨 p.1.1 p.1.2) (fun p => meanX V W P Q μ 𝓨 (ω (g, h) p.1.1) p.1.2)
    (fun p q => by
      have e := meanX_prod_zero D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
        (heisO ψ V W q.1.2 q.1.1) (heisO ψ V W p.1.2 p.1.1)
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ q.2.1 _) (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ p.2.1 _)
      rwa [hωx _ q.2.1 _ q.2.2, hωx _ p.2.1 _ p.2.2, hfx _ _ q.2.2, hfx _ _ p.2.2] at e)
  refine ⟨⟨c, ?_⟩, fun f hf x hx => ?_⟩
  · show c ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.2 hc
  · have e := congrFun hcf ⟨(f, x), hf, hx⟩
    simp only [Pi.smul_apply, smul_eq_mul] at e
    exact (hint (ω (g, h) f) x hx).trans (e.trans (congrArg _ (hint f x hx).symm))

end GlobalTheory.IsoMean

end
