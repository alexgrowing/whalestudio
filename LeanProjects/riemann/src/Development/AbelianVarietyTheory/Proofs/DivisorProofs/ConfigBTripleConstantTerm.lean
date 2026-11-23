import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.ConePlane

open scoped ComplexOrder in

theorem one_le_p {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a r p : ℕ} {V : Spc F E a} (hB : B.IsGood σ) (hV : V.IsHerm σ B r p)
    (hx : ∃ x : Fin a → E, x ≠ 0 ∧ form σ V.J x x = 0) : 1 ≤ p := by
  by_contra h0
  have hp0 : p = 0 := by omega
  subst hp0
  obtain ⟨x, hx0, hxx⟩ := hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrn, A, hA⟩ := hV.sig w
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hcm : ∀ y : E, τ (σ y) = star (τ y) := fun y => hB.cm.2.2.2 τ y
  set M : Matrix (Fin a) (Fin a) ℂ := V.J.map τ with hM
  set z : Fin a → ℂ := fun i => τ (x i) with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simpa [z] using this
  have key : z ⬝ᵥ M *ᵥ star z = 0 := by
    have h1 : τ (form σ V.J x x) = z ⬝ᵥ M *ᵥ star z := by
      simp [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hcm, M, z, Matrix.map_apply]
    rw [← h1, hxx, map_zero]
  set P := M * A.map star with hP
  have hA1 : Aᵀ * P = 1 := by
    rw [hP, ← Matrix.mul_assoc, hA]
    ext (i | i) (j | j)
    · simp [Matrix.fromBlocks, Matrix.one_apply]
    all_goals first | exact i.elim0 | exact j.elim0
  have e : (Fin r ⊕ Fin 0) ≃ Fin a := (Equiv.sumEmpty _ _).trans (finCongr (by omega))
  have hA2 : P * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hA1
  have hA3 : A * Pᵀ = 1 := by
    have := congrArg Matrix.transpose hA2
    simpa [Matrix.transpose_mul] using this
  have hA4 : A.map star * (P.map star)ᵀ = 1 := by
    have := congrArg (fun Q : Matrix (Fin a) (Fin a) ℂ => Q.map star) hA3
    simpa [Matrix.map_mul, Matrix.transpose_map] using this
  have hMP : M = P * (P.map star)ᵀ := by
    rw [hP, Matrix.mul_assoc, hA4, Matrix.mul_one]
  set u := z ᵥ* P with hu
  have hstar : (P.map star)ᵀ *ᵥ star z = star u := by
    funext i
    simp [u, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  have hval : z ⬝ᵥ M *ᵥ star z = u ⬝ᵥ star u := by
    rw [hMP, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar]
  have hu0 : u ≠ 0 := by
    intro h
    apply hz0
    have : z = A *ᵥ u := by
      rw [hu, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hA3, Matrix.one_mulVec]
    rw [this, h, Matrix.mulVec_zero]
  rw [hval] at key
  exact hu0 ((dotProduct_self_star_eq_zero).1 key)

theorem exists_plane_model_ev : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → (∃ x : Fin a → E, x ≠ 0 ∧ form σ G.V.J x x = 0) → ∃ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p ∧ H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ ∧ M₂.IsGood B.ψ ∧ IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ hx
  have hB : B.IsGood σ := hT.base
  have hV := hT.geo.hV
  have hp : 1 ≤ G.p := one_le_p hB hV hx
  have hr : 1 ≤ a - G.p := by have := hT.geo.eBig; omega
  have ha : 3 ≤ a := by have := hT.geo.aBig; have := hT.geo.lt; omega
  obtain ⟨V₂, X₁, H₀, hV₂, hX₁, hH₀⟩ := GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace F E σ B hB a (a - 2) (by omega) (by omega) G.V (a - G.p) G.p hr hp hV
    0 1 (by omega) (by omega)
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hB (a - 2) (a + b) X₁ G₁.W _ _ _ _ hX₁ hT₁.geo.hW
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  let M' : Model σ (reS G.V V₂) G.W := ⟨G.M.co, G.M.vac, G.M.μ, G.M.dom⟩
  have hP' : IsPair B M' X.β (X.β / X.α) om (a - G.p) G.p (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
    { hP with herm := hV₂, good := ⟨hP.good.rat, hP.good.vac, hP.good.std, hP.good.haar, hP.good.dom⟩ }
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.theta_evaluation_zero_cone hKP.base).2 F E σ B a (a + (b + 2)) (reS G.V V₂) G.W M' X.β (X.β / X.α) om _ _ _ _ hP'
    (a - 2) (a + b) X₁ G₁.W H₀ H' a (a + b + 1) 0 1 M₂ hH₀ hC.hH' hM₂
  exact ⟨V₂, a - 2, X₁, H₀, 0, 1, M₂, e, hV₂, hH₀, hM₂, ⟨he.maps, he.Heisenberg₂, he.inv, he.loc⟩⟩

end GlobalTheory.ThK.ConePlane
