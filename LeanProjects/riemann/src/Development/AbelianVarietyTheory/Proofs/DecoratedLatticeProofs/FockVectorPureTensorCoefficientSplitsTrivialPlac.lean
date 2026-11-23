import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCoeffSplit

theorem ip_double_sum {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {ι κ : Type}
    (s : Finset ι) (t : Finset κ) (a : ι → ℂ) (b : κ → ℂ) (u : ι → WO S T → ℂ) (w : κ → WO S T → ℂ)
    (hI : ∀ i j, IntegrableOn (fun z => u i z * (starRingEnd ℂ) (w j z)) 𝓕 μ) :
    ipO μ 𝓕 (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • w j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * (starRingEnd ℂ) (b j) * ipO μ 𝓕 (u i) (w j) := by
  unfold ipO
  have e : (fun z => (∑ i ∈ s, a i • u i) z * (starRingEnd ℂ) ((∑ j ∈ t, b j • w j) z)) =
      fun z => ∑ i ∈ s, ∑ j ∈ t, a i * (starRingEnd ℂ) (b j) * (u i z * (starRingEnd ℂ) (w j z)) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hI i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

open Classical in

def monoFactor {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) (τ : D.what₂.Tau) : MvPolynomial (FVar D m n) ℂ :=
  ∏ y ∈ k.support with y.1 = τ, MvPolynomial.X y ^ k y

theorem monoFactor_supported {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) (τ : D.what₂.Tau) :
    monoFactor k τ ∈ MvPolynomial.supported ℂ {y : FVar D m n | y.1 = τ} := by
  classical
  unfold monoFactor
  refine Subalgebra.prod_mem _ fun y hy => Subalgebra.pow_mem _ (MvPolynomial.X_mem_supported.2 ?_) _
  exact (Finset.mem_filter.1 hy).2

theorem prod_monoFactor {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) :
    ∏ τ, monoFactor k τ = MvPolynomial.monomial k 1 := by
  classical
  unfold monoFactor
  rw [Finset.prod_fiberwise k.support (fun y => y.1) (fun y => MvPolynomial.X y ^ k y), MvPolynomial.monomial_eq,
    MvPolynomial.C_1, one_mul]
  rfl

theorem fockPure_any {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (x : Place D → WO S T → ℂ) (f : WO S T → ℂ) (hx : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f)
    (hx0 : ∀ τ, x (.inr τ) = f₀) (P : D.what₂.Tau → MvPolynomial (FVar D T.rank S.rank) ℂ)
    (hP : ∀ τ, P τ ∈ MvPolynomial.supported ℂ {y : FVar D T.rank S.rank | y.1 = τ}) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
      (Sum.elim (fun v => x (.inl v)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (P τ))
      (pureTensorO ψ θ S T sS sT BS BT f (∏ τ, P τ)) := by
  classical
  have hl : GlobalTheory.FockPureTensor.IsMultiLin (IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀) :=
    (GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
  have h1 : ∀ g, pureTensorO ψ θ S T sS sT BS BT g 1 = g := fun g => GlobalTheory.Ker.FockAlg.pure_one g
  have key := GlobalTheory.FockPureTensor.prod_step hl (pureTensorO ψ θ S T sS sT BS BT f)
    (pureTensorO ψ θ S T sS sT BS BT f₀)
    (fun τ => {y : FVar D T.rank S.rank | y.1 = τ})
    (fun τ y hy z R Q h => by
      rw [GlobalTheory.FockPureTensor.pureTensorO_X_mul hb BS BT hx.2.1,
        GlobalTheory.FockPureTensor.pureTensorO_X_mul hb BS BT (base_theta hb)]
      obtain rfl : y.1 = τ := hy
      unfold aPlusAll
      exact GlobalTheory.FockPureTensor.isPure_aPlus hb hμ z _ _ _ _ _ h) hP (x := x) (by rw [h1]; exact hx)
    (fun τ => by rw [h1]; exact hx0 τ) Finset.univ
  simp only [Finset.mem_univ, if_true] at key
  exact key

theorem pureTensorO_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT f P =
      ∑ k ∈ P.support, P.coeff k • pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial k 1) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem coeff_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : Place D → WO S T → ℂ), (∀ τ, x (.inr τ) = f₀) → ∀ (v : FinPl D) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (g : GA D S), gAt S (.inl v) g = 1 → ∃ C : ℂ, ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ≠ .inl v → x₁ p = x p) → (∀ p, p ≠ .inl v → x₂ p = x p) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → ipO μ 𝓕 (om (g, 1) (pureTensorO ψ θ S T sS sT BS BT f₁ P)) (pureTensorO ψ θ S T sS sT BS BT f₂ P) = C * ipO μ 𝓕 (x₁ (.inl v)) (x₂ (.inl v)) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _ hb hμ BS BT x hx0 v P g hg
  classical
  let Y : (FVar D T.rank S.rank →₀ ℕ) → Place D → WO S T → ℂ := fun k =>
    Sum.elim (fun u => x (.inl u)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (monoFactor k τ)
  let R : (FVar D T.rank S.rank →₀ ℕ) → (FVar D T.rank S.rank →₀ ℕ) → ℂ := fun k l =>
    ∏ᶠ (p : Place D) (_ : p ≠ .inl v), ipO μ 𝓕 (om (gAt S p g, gAt T p 1) (Y k p)) (Y l p)
  refine ⟨∑ k ∈ P.support, ∑ l ∈ P.support, P.coeff k * (starRingEnd ℂ) (P.coeff l) * R k l, ?_⟩
  intro x₁ x₂ f₁ f₂ e1 e2 hp1 hp2
  have hne : ∀ τ : D.what₂.Tau, (Sum.inr τ : Place D) ≠ .inl v := fun τ h => by cases h
  have pure : ∀ (y : Place D → WO S T → ℂ) (f : WO S T → ℂ), (∀ p, p ≠ .inl v → y p = x p) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f → ∀ k, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Sum.elim (fun u => y (.inl u)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (monoFactor k τ))
        (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial k 1)) := fun y f ey hy k => by
    have := fockPure_any BS BT hb hμ y f hy (fun τ => (ey _ (hne τ)).trans (hx0 τ)) (monoFactor k)
      (monoFactor_supported k)
    rwa [prod_monoFactor] at this
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have ipb := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std hb) hμ
  have pom := fun k => GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hb hμ _ _
    (pure x₁ f₁ e1 hp1 k) g 1
  rw [pureTensorO_eq_sum ψ θ S T sS sT BS BT f₁, pureTensorO_eq_sum ψ θ S T sS sT BS BT f₂, map_sum]
  simp only [map_smul]
  rw [ip_double_sum μ 𝓕 _ _ _ _ _ _ fun k l => (ipb _ _ (pom k).2.1 (pure x₂ f₂ e2 hp2 l).2.1).1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc (P.coeff k * (starRingEnd ℂ) (P.coeff l))]
  congr 1
  obtain ⟨hfin, heq⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ _ _ _
    (pom k) (pure x₂ f₂ e2 hp2 l)
  rw [heq, ← mul_finprod_cond_ne (.inl v) hfin, mul_comm]
  congr 1
  · refine finprod_congr fun p => finprod_congr fun hp => ?_
    cases p with
    | inl u => simp only [Sum.elim_inl, Y, e1 _ hp, e2 _ hp]
    | inr τ => simp only [Sum.elim_inr, Y]
  · simp only [Sum.elim_inl, hg, gAt_one, om1]

end GlobalTheory.FockCoeffSplit
