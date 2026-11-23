import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesTranslationLatticeBoundedNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTranslate

theorem coefFn_natCast_smul {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (N : ℕ) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam ((N : K) • F) x = (N : ℂ) * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_natCast]
  ring

theorem coefLatFn_transfer {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → D.host.E →+* K) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n) {O O' : Subring ℂ} (hOO : O ≤ O')
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (N : ℕ) (hN : N ≠ 0) (hinv : ((N : ℂ))⁻¹ ∈ O')
    (hF : ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, (N : K) • F ∈ Formalism.L2.DIV.nabAtr emb lam M')
    {φ : GLR D n → ℂ} (hφ : φ ∈ coefLatFn σ emb O lam M) : φ ∈ coefLatFn σ emb O' lam M' := by
  induction hφ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hFm, rfl⟩ := h
    have h1 : coefFn σ lam (((N : K) • F : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O' lam M' :=
      Submodule.subset_span ⟨_, hF F hFm, rfl⟩
    have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : O') h1
    convert h2 using 1
    funext x
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change _ = (N : ℂ)⁻¹ * _
    rw [Submodule.coe_smul, coefFn_natCast_smul, inv_mul_cancel_left₀ hN']
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c, hOO c.2⟩ : O') h1

theorem normProd_ne_zero {D : D7} (Q : Finset (Pl D.host.E)) : normProd Q ≠ 0 := by
  unfold normProd
  refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

set_option maxHeartbeats 800000 in

theorem lat_translate : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  intro D ρ hρ i j b k Q h hQ P hS hD hh hsupp hP
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0 (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b h)
    (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b (h * hQ)) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := hρ.range_le i b k (GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring D ρ i b Q hD)
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  have hF : ∀ F ∈ Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) h)),
      (((normProd Q ^ c) ^ a : ℕ) : ↥D.LL0) • F ∈
        Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) := by
    intro F hF
    have := ha F hF
    rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]
  exact coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam (hρ.range_le i b k)
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv hF hP.2

end GlobalTheory.LatTranslate

end
