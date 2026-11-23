import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := h0
  have himg : ∀ x : Fin n → M, x '' {b | b.val < r} = Set.range (fun b : Fin r => x (Fin.castLE hrn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hrn b, b.2, rfl⟩
  have hadj1 : adj 1 = 1 := by
    have := hadj 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  let f : (Fin r → M) → F := fun z =>
    if h : Submodule.span R (Set.range z) = ⊤ then (((ψ (adj (h1 y z hy h).exists.choose))⁻¹ : Fˣ) : F) else 0
  have hf : ∀ (z : Fin r → M) (g : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ → (∀ b, g (y b) = z b) →
      f z = (((ψ (adj g))⁻¹ : Fˣ) : F) := by
    intro z g hz hg
    have : (h1 y z hy hz).exists.choose = g :=
      (h1 y z hy hz).unique (h1 y z hy hz).exists.choose_spec hg
    simp only [f, dif_pos hz, this]
  have hspan : ∀ (z : Fin r → M) (k : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ →
      Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
    intro z k hz
    have e : (Set.range fun b => k (z b)) = (k : M →ₗ[R] M) '' Set.range z := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hz, Submodule.map_top, LinearEquiv.range]
  let x₀ : Fin n → M := fun b => if h : b.val < r then y ⟨b.val, h⟩ else 0
  have hx₀ : (fun b : Fin r => x₀ (Fin.castLE hrn b)) = y := by
    funext b
    simp [x₀]
  refine ⟨fun x => f (fun b => x (Fin.castLE hrn b)), x₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' h
    have : (fun b : Fin r => x (Fin.castLE hrn b)) = fun b => x' (Fin.castLE hrn b) :=
      funext fun b => h _ b.2
    simp only [this]
  · intro x hx
    rw [himg]
    by_contra hz
    exact hx (by simp only [f, dif_neg hz])
  · intro k x
    set z : Fin r → M := fun b => x (Fin.castLE hrn b) with hzdef
    change f (fun b => k (z b)) = _ * f z
    by_cases hz : Submodule.span R (Set.range z) = ⊤
    · obtain ⟨g, hg, -⟩ := h1 y z hy hz
      rw [hf z g hz hg, hf _ (k * g) (hspan z k hz) (fun b => by simp [hg b]), hadj, map_mul, mul_inv,
        Units.val_mul, mul_comm]
    · have hz' : ¬ Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
        intro h
        have := hspan _ k.symm h
        simp only [LinearEquiv.symm_apply_apply] at this
        exact hz this
      simp only [f, dif_neg hz, dif_neg hz', mul_zero]
  · change f (fun b : Fin r => x₀ (Fin.castLE hrn b)) = 1
    rw [hx₀, hf y 1 hy (fun b => rfl), hadj1]
    simp
  · rw [himg, hx₀, hy]

theorem exists_phiPin_of_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → Dw.p + Dw.q ≤ n → ∀ ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, ∃ (φ : (Fin n → LevQ Dw d.l₂) → c.F) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d), DeltaDat.PhiPin { d with φδ := φ } ph ψ x₀ := by
  intro E _ _ _ H Dw l Xo c n d hd hn ψ
  obtain ⟨h0, h1, adj, hadj, hiff⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨ph, x₀, ha, hb, hc, hd1, hd2⟩ :=
    exists_equivariant_fun_on_spanning_families hn h0 h1 adj hadj ψ
  refine ⟨fun q => d.eF.symm (∑ᶠ x : Fin n → LaJ Xo c d, d.eF (ph x) *
      ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))), ph, x₀, ha, hb, ?_, hd1, hd2, ?_⟩
  · intro k kst h x
    have := (hiff k kst).mp h
    subst this
    exact hc kst x
  · intro q
    exact d.eF.apply_symm_apply _

end GlobalTheory
