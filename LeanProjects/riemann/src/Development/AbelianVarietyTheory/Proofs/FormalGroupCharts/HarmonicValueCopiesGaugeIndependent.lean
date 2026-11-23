import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.HarmCopies

open GlobalTheory.PowGerm

theorem monomial_eq_boxSer {k : Type} [CommRing k] {n d : ℕ} (e : Fin n × Fin d →₀ ℕ) :
    (MvPowerSeries.monomial e 1 : PS k n d) =
      boxSer fun b => ∏ j : Fin d, (MvPowerSeries.X ((0 : Fin 1), j) : PS k 1 d) ^ e (b, j) := by
  unfold boxSer
  simp only [map_prod, map_pow, MvPowerSeries.rename_X]
  rw [← Fintype.prod_prod_type' (fun b j => (MvPowerSeries.X (b, j) : PS k n d) ^ e (b, j)),
    MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem exists_jet {k : Type} [CommRing k] {n d : ℕ} (N : ℕ) (f : PS k n d) :
    ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N →
      MvPowerSeries.coeff e f =
        MvPowerSeries.coeff e (∑ j : S, MvPowerSeries.coeff j.1 f • (MvPowerSeries.monomial j.1 1 : PS k n d)) := by
  classical
  refine ⟨(Finsupp.finite_of_degree_le N).toFinset, fun e he => ?_⟩
  rw [map_sum, Finset.sum_eq_single ⟨e, by simpa using he⟩]
  · simp
  · intro j _ hj
    rw [map_smul, MvPowerSeries.coeff_monomial_ne (fun h => hj (Subtype.ext h.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def letterEquiv (T : Type) (r : T → ℕ) (n : ℕ) : (Σ τ : T, Fin (r τ)) × Fin n ≃ Formalism.L2.Pj.Letter T r n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem const_eq_zero {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} (hh : B.IsCanonGauge k h) :
    MvPowerSeries.constantCoeff h = 0 := by
  rw [← TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt (n := 1) 0)) h, hh.ax0, map_zero]

theorem col_sum_eq_zero {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : MvPolynomial.rename (letterEquiv T r n) Q ∈ harmK r n k cc isX (fun _ => 1))
    (τ : T) (hτ : isX τ) (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
      (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hQ
  have h := hQ τ hτ i i'
  apply MvPolynomial.rename_injective _ (letterEquiv T r n).injective
  rw [map_zero, ← h, map_sum, lap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, one_smul, ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective,
      ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective]
    rfl
  · intro b' _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.HarmCopies

namespace GlobalTheory

open HarmCopies PowGerm in

theorem nabValN_harmonic_gauge_independent :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n P hP w0 q f
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv T r n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv T r n).surjective P
  obtain ⟨S, hS⟩ := exists_jet (MvPolynomial.rename (letterEquiv T r n) Q).totalDegree f
  rw [(nabJet R d O B k h w0 q n _ _ _).1 _ _ _ hS, (nabJet R d O B k h' w0 q n _ _ _).1 _ _ _ hS,
    (nabJet R d O B k h w0 q n _ _ _).2.1, (nabJet R d O B k h' w0 q n _ _ _).2.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [monomial_eq_boxSer,
    nabValN_boxSer R d O B k h w0 (const_eq_zero hh) q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl),
    nabValN_boxSer R d O B k h' w0 (const_eq_zero hh') q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl)]
  exact canonGauge_independence_harmonic R d O k B h h' hh hh' T r cc isX σ hcc hX hσ hsep u hu n Q
    (col_sum_eq_zero Q hP) w0 q _

end GlobalTheory
