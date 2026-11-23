import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

theorem selfDual_frame_level_one_lattice_eq_standard {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem pi_eq_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem arr_injective {n : ℕ} {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  unfold arr at h'
  apply Fin.ext
  split_ifs at h' <;> simp only at h' <;> omega

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

theorem nNeg_eq (τ : D.what₂.Tau) : nNeg (M.ε τ) = q := by
  rw [nNeg_shape (by omega) (hε τ)]; omega

theorem negM_eq (τ : D.what₂.Tau) :
    negM V q = diagonal fun c => (if M.ε τ (arr (nNeg (M.ε τ)) c) = true then (1 : ℂ) else -1) := by
  unfold negM
  congr 1
  funext c
  have := c.2
  rw [nNeg_eq M hpq hε, hε, arr, sgn]
  by_cases h : (c : ℕ) < q
  · rw [dif_pos h, if_pos h, if_neg (by simp only [decide_eq_true_eq]; omega)]; simp
  · rw [dif_neg h, if_neg h, if_pos (by simp only [decide_eq_true_eq]; omega)]; simp

theorem isONeg_x0Mat : IsONeg V q (x0Mat M) := by
  intro τ
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  have h3 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      ((onb M τ)ᴴ * gramAt D V τ * onb M τ).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h3, h2, negM_eq M hpq hε τ, Formalism.REAL.Jm, Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le _))]
  rfl

theorem cart_eq_cartZ : cart M = cartZ V q (x0Mat M) := by
  funext τ
  have hn : negM V q * negM V q = 1 := by
    rw [negM_eq M hpq hε τ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have h1 : (negM V q * ((x0Mat M τ)ᴴ * gramAt D V τ)) * x0Mat M τ = 1 := by
    rw [Matrix.mul_assoc, isONeg_x0Mat M hpq hε τ, hn]
  have hu : IsUnit (x0Mat M τ).det := Matrix.isUnit_det_of_left_inverse h1
  rw [cartZ, negM_eq M hpq hε τ, ← torus_x0Mat M τ fun a => if M.ε τ a = true then (1 : ℂ) else -1,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end Model

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV; exact h

theorem latEmb_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ ι) := by
  subst hV; exact h

theorem isAA_span {k : ℕ} (L : Lt D.host.E k) : GlobalTheory.Ker.IsAA (Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) L := by
  intro v
  rw [← Submodule.mem_toAddSubgroup]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x hx' hx =>
      clear hx'
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hx
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx) hv

theorem isMov_hLat (W : HSp D) (h : GA D W) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt W h) (Bridge.hLat W 1) (Bridge.hLat W (FWT.fin W h)) := by
  intro u
  rw [GlobalTheory.MovedLat.hLat_one]
  have := Set.ext_iff.1 (GlobalTheory.MovedLat.hat_hLat W (FWT.fin W h)) u
  exact this.trans ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

end GlobalTheory.OneMapRef.FactsLat
