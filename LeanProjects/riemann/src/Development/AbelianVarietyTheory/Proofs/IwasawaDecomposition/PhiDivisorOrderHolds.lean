import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormsOnConesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralLinearFormOnBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormRealCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeAndRankBoundIntegersStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.PhiDivO

variable {E : Type} [Field E] [NumberField E]

theorem comb_eval {O : Type} [CommRing O] (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    (comb a ψ b φ).eval X B = a * ψ.eval X B + b * φ.eval X B := rfl

theorem comb_evalZ {O : Type} [CommRing O] (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) :
    (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := rfl

theorem comb_linearOn {O : Type} [CommRing O] {a : ℕ} {ψ : InvFun O} {b : ℕ} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h₁ : ψ.LinearOn γ)
    (h₂ : φ.LinearOn γ) : (comb a ψ b φ).LinearOn γ := by
  intro c hc
  rw [comb_eval, h₁ c hc, h₂ c hc]
  simp only [comb_evalZ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem resInt_eval (φs : InvFun ℤ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Finite ℤ X] (B : X → X → ℝ) : (resInt (𝓞 E) φs).eval X B = φs.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [InvFun.eval_eq _ hr]
  exact φs.eval_comp (r := r.restrictScalars ℤ) hr B

theorem resInt_evalZ (φs : InvFun ℤ) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X) : (resInt (𝓞 E) φs).evalZ β = φs.evalZ β :=
  resInt_eval φs X _

end GlobalTheory.TorRef.PhiDivO

namespace GlobalTheory.TorRef.PhiDivO

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vals {H : Host E} {q g : ℕ} {φs : InvFun ℤ} {𝒩 : Finset ℕ} {φ : InvFun (𝓞 E)}
    (hg : Module.finrank ℚ E * q ≤ g) (hs : IsPolFan id g φs) (hR : Refines H q φs 𝒩 φ)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone H.bar φ γ) (i : Fin m) :
    (∃ n : ℕ, φ.evalZ (γ i) = n) ∧ ∃ n : ℕ, (resInt (𝓞 E) φs).evalZ (γ i) = n := by
  refine ⟨(hR.1 X hX).exists_nat (hγ.mem i) (hγ.nonneg i), ?_⟩
  obtain ⟨hfree, hrk⟩ := GlobalTheory.T.free_and_rank_bound_integers E X
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hP : IsPolFanOn id φs X := hs X (hrk.trans ((Nat.mul_le_mul_left _ hX).trans hg))
  have hmem : γ i ∈ balForms id X :=
    ⟨(hγ.mem i).1, fun (a : ℤ) y z => by simp only [LinearMap.map_smul, LinearMap.smul_apply, id]⟩
  obtain ⟨n, hn⟩ := hP.exists_nat hmem (hγ.nonneg i)
  exact ⟨n, by rw [resInt_evalZ]; exact hn⟩

theorem cone {H : Host E} {q g : ℕ} {φs : InvFun ℤ} {𝒩 : Finset ℕ} {φ : InvFun (𝓞 E)}
    (hg : Module.finrank ℚ E * q ≤ g) (hs : IsPolFan id g φs) (hR : Refines H q φs 𝒩 φ) (a d b : ℕ)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : ConeO H φ X m γ) :
    ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) →
      (∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal be = ∑ i, c i • toReal (γ i)) →
        (comb a (comb d (resInt _ φs) 0 φ) b φ).evalZ be = ℓ be ∧ 0 ≤ ℓ be := by
  have hc : IsCone H.bar φ γ := hγ
  obtain ⟨hfree, -⟩ := GlobalTheory.T.free_and_rank_bound_integers E X
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  choose ny hny using fun i => (vals hg hs hR hX hc i).1
  choose nx hnx using fun i => (vals hg hs hR hX hc i).2
  set ψ := comb a (comb d (resInt _ φs) 0 φ) b φ with hψ
  have hval : ∀ i, ψ.evalZ (γ i) = ((a * (d * nx i) + b * ny i : ℕ) : ℝ) := fun i => by
    rw [hψ, comb_evalZ, comb_evalZ, hnx, hny]; push_cast; ring
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.integral_linear_form_on_basis H.bar X m γ hc.mem hc.basis fun i => ((a * (d * nx i) + b * ny i : ℕ) : ℤ)
  have hlin : ψ.LinearOn γ :=
    comb_linearOn (comb_linearOn ((hR.2.2.2.2.2 X hX m γ hc).1) hc.linear) hc.linear
  refine ⟨ℓ, fun be _ ⟨c, hc0, hbe⟩ => ?_⟩
  have hreal := GlobalTheory.T.linear_form_real_combination X ℓ m γ c be hbe
  have hpt : (fun x y => (be x y : ℝ)) = fun x y => ∑ i, c i * (γ i x y : ℝ) := by
    funext x y
    have := LinearMap.congr_fun₂ hbe x y
    simpa [toReal, LinearMap.sum_apply] using this
  have h1 : ψ.evalZ be = ∑ i, c i * (ℓ (γ i) : ℝ) := by
    rw [InvFun.evalZ, hpt, hlin c hc0]
    exact Finset.sum_congr rfl fun i _ => by rw [hval, hℓ]; push_cast; rfl
  refine ⟨h1.trans hreal.symm, ?_⟩
  have : (0 : ℝ) ≤ (ℓ be : ℝ) := by
    rw [hreal]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc0 i) (by rw [hℓ]; positivity)
  exact_mod_cast this

end GlobalTheory.TorRef.PhiDivO

theorem GlobalTheory.TorRef.phiDivO : PhiDivOSt := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ hg hs hR hZ a d b
  exact GlobalTheory.T.linear_forms_on_cones E H D l Xo c Z (ConeO H φ) _
    (fun X _ _ _ _ hX m γ hγ => GlobalTheory.TorRef.PhiDivO.cone hg hs hR a d b X hX m γ hγ) hZ
