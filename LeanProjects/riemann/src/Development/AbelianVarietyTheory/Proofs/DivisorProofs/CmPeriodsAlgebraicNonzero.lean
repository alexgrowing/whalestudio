import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatingIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamEigenspaceCorankLeTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicEndomorphismCorankDeRhamStatement
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_rank_coker {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (c : K)
    (hrk : Module.rank K (V ⧸ LinearMap.range (T - c • 1)) ≤ 2)
    (hdis : Disjoint (LinearMap.ker (T - c • 1)) (LinearMap.range (T - c • 1)))
    (y₀ : V) (hy : y₀ ≠ 0) (hTy : T y₀ = c • y₀) (f f' : Module.Dual K V) (hf0 : f y₀ = 0) (hf'0 : f' y₀ = 0)
    (hf : ∀ x, f (T x) = c * f x) (hf' : ∀ x, f' (T x) = c * f' x) (x y : V) :
    f x * f' y = f y * f' x := by
  set W := LinearMap.range (T - c • 1) with hW
  have vanish : ∀ (g : Module.Dual K V), (∀ x, g (T x) = c * g x) → ∀ w ∈ W, g w = 0 := by
    rintro g hg w ⟨v, rfl⟩
    simp [hg, smul_eq_mul]
  have hyW : y₀ ∉ W := by
    intro h
    have hk : y₀ ∈ LinearMap.ker (T - c • 1) := by simp [hTy]
    exact hy ((Submodule.disjoint_def.1 hdis) y₀ hk h)
  by_contra hD
  have hD' : f x * f' y - f y * f' x ≠ 0 := sub_ne_zero.2 hD
  have hli : LinearIndependent K ![W.mkQ y₀, W.mkQ x, W.mkQ y] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    replace hg : g 0 • y₀ + g 1 • x + g 2 • y ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] using hg
    have e1 := vanish f hf _ hg
    have e2 := vanish f' hf' _ hg
    simp only [map_add, map_smul, smul_eq_mul, hf0, hf'0, mul_zero, zero_add] at e1 e2
    have hb : g 1 = 0 := by
      have : g 1 * (f x * f' y - f y * f' x) = 0 := by linear_combination f' y * e1 - f y * e2
      exact (mul_eq_zero.1 this).resolve_right hD'
    have hc : g 2 = 0 := by
      have : g 2 * (f x * f' y - f y * f' x) = 0 := by linear_combination f x * e2 - f' x * e1
      exact (mul_eq_zero.1 this).resolve_right hD'
    rw [hb, hc, zero_smul, zero_smul, add_zero, add_zero] at hg
    have ha : g 0 = 0 := by
      by_contra ha
      exact hyW ((W.smul_mem_iff ha).1 hg)
    intro j; fin_cases j <;> assumption
  have := hli.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_ofNat, Cardinal.lift_ofNat] at this
  have h3 : (3 : Cardinal) ≤ 2 := by
    have := this.trans (Cardinal.lift_le.2 hrk)
    simpa using this
  norm_num at h3

end GlobalTheory.EigenFunctional

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_eigen : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  intro hPC hDR E _ _ _ I _ φ L 𝔠 X₀ X p U hcm hp i y₀ hy0 hy f f' hf0 hf'0 hff x y
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.cm_type_separating_integer E I φ hcm i
  have halg : IsAlgebraic ℚ (φ i ((b₀ : FR E) : E)) := by
    have h1 : IsIntegral ℤ (φ i ((b₀ : FR E) : E)) :=
      ((b₀.2.map (algebraMap (FR E) E).toIntAlgHom).map (φ i).toIntAlgHom)
    exact (h1.tower_top (A := ℚ)).isAlgebraic
  let β₀ : Qb := ⟨φ i ((b₀ : FR E) : E), mem_algebraicClosure_iff.2 halg⟩
  have hβ : algebraMap Qb ℂ β₀ = φ i ((b₀ : FR E) : E) := rfl
  obtain ⟨hC1, hC2⟩ := GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two hPC hDR E I φ L 𝔠 X U hcm i b₀ hb₀
  rw [← hβ] at hC1 hC2
  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.algebraic_endomorphism_corank_de_rham hDR (FR E) 𝔠 X₀ X p hp b₀ β₀ hC1 hC2
  exact mul_comm_of_rank_coker _ β₀ hQ1 hQ2 y₀ hy0 (hy b₀ β₀ hβ) f f' hf0 hf'0
    (fun z ↦ (hff b₀ β₀ hβ z).1) (fun z ↦ (hff b₀ β₀ hβ z).2) x y

end GlobalTheory.EigenFunctional
