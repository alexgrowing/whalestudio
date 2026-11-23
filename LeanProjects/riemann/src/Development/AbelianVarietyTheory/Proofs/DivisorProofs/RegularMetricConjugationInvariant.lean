import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqConjugateOfIsConjMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoCompConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
open Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegConj

theorem under_eq_of_conj {F : Type} [Field F] [NumberField F] {Y : Var F} {σ σ' : F →+* ℂ} {p : Pts Y σ}
    {p' : Pts Y σ'} (e : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : under p' = under p := by
  show p'.1 _ = p.1 _
  rw [e]
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))

theorem lnRatio_eq_log {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}
    (m m' : (cxSt F).Met Y σ Δ) (y : Pts Y σ) :
    lnRatio m m' y = Real.log (Var.Met.h m (eqn Δ (under y)) y) / 2 - Real.log (Var.Met.h m' (eqn Δ (under y)) y) / 2 := by
  have h₁ : y ∈ Var.eqnSet σ Δ (eqn Δ (under y)) := Base.isEqn_eqn _ _
  have e₁ := Var.pn_frame (m := m) h₁
  have e₂ := Var.pn_frame (m := m') h₁
  simp only [lnRatio, lnN]
  rw [← e₁, ← e₂]
  rfl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem phW_conj (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) {σ σ' : D.what₂.LL →+* ℂ} (u : D.what₂.Tau → Fin N → ℝ)
    {p : Pts (Φ.C k).Y σ} {p' : Pts (Φ.C k).Y σ'} (e : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    phW (metsOf x Φ) (refMet x Φ) k σ' u p' = phW (metsOf x Φ) (refMet x Φ) k σ u p := by
  have hu := under_eq_of_conj e
  unfold phW
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun r _ => congrArg (_ * ·) ?_)
  have h₁ : p ∈ Var.eqnSet σ (divOf (Φ.C k) (rootExp S r)) (eqn (divOf (Φ.C k) (rootExp S r)) (under p)) :=
    Base.isEqn_eqn _ _
  obtain ⟨hm, h0, -⟩ := mets_conj _ _ _ _ _ _ _ x Φ k σ σ' _ p p' _ e h₁
  rw [lnRatio_eq_log, lnRatio_eq_log, hu, hm none, h0]

theorem exists_conj_homeo (Φ : s.Flag) (k : s.Comp) {σ σ' : D.what₂.LL →+* ℂ} {y : Pts (Φ.C k).Y σ}
    {y' : Pts (Φ.C k).Y σ'} (hy : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    ∃ ι : Pts (Φ.C k).Y σ' ≃ₜ Pts (Φ.C k).Y σ, IsConjMap ι ∧ ι y' = y := by
  have hσ' : σ' = (starRingEnd ℂ).comp σ := by
    have h1 := y'.2
    rw [hy, Category.assoc, y.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  have hσ : σ = (starRingEnd ℂ).comp σ' := by rw [hσ', ConjMet.conj_comp_conj]
  obtain ⟨ι, hι⟩ := GlobalTheory.ConjExph.exists_isConjMap (Φ.C k).Y (σ := σ) (σ' := σ') hσ
  obtain ⟨ι', hι'⟩ := GlobalTheory.ConjExph.exists_isConjMap (Φ.C k).Y (σ := σ') (σ' := σ) hσ'
  have cc : ∀ {τ τ' : D.what₂.LL →+* ℂ} (f : Pts (Φ.C k).Y τ' → Pts (Φ.C k).Y τ) (g : Pts (Φ.C k).Y τ → Pts (Φ.C k).Y τ'),
      IsConjMap f → IsConjMap g → ∀ z, g (f z) = z := fun f g hf hg z => Subtype.ext (by
    rw [hg, hf, ← Category.assoc, ConjMet.spMap_conj_conj, Category.id_comp])
  have c₁ := (GlobalTheory.ConjChart.continuous_and_exists_conj_chart _ _ _ (Φ.C k).Y.dim σ σ' ι hσ hι).1
  have c₂ := (GlobalTheory.ConjChart.continuous_and_exists_conj_chart _ _ _ (Φ.C k).Y.dim σ' σ ι' hσ' hι').1
  refine ⟨⟨⟨ι, ι', cc ι ι' hι hι', cc ι' ι hι' hι⟩, c₁, c₂⟩, hι, ?_⟩
  exact Subtype.ext (by
    show (ι y').1 = y.1
    rw [hι, hy, ← Category.assoc, ConjMet.spMap_conj_conj, Category.id_comp])

theorem reg_conj_of {x : ToroidalCompactificationData s} {Φ : s.Flag} (P : PolDat s Φ (metsOf x Φ) (refMet x Φ)) (k : s.Comp)
    {σ σ' : D.what₂.LL →+* ℂ} (u : D.what₂.Tau → Fin N → ℝ) (t : ℝ) {y : Pts (Φ.C k).Y σ} {y' : Pts (Φ.C k).Y σ'}
    (hy : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : P.reg k σ' u t y' = P.reg k σ u t y := by
  obtain ⟨ι, hι, hιy⟩ := exists_conj_homeo Φ k hy
  have hinv : ∀ z, z.1 = spMap (starRingEnd ℂ) ≫ (ι z).1 := fun z => by
    rw [hι z, ← Category.assoc, ConjMet.spMap_conj_conj, Category.id_comp]
  have hph : ∀ v : D.what₂.Tau → Fin N → ℝ,
      phW (metsOf x Φ) (refMet x Φ) k σ' v = phW (metsOf x Φ) (refMet x Φ) k σ v ∘ ι :=
    fun v => funext fun z => phW_conj x Φ k v (hinv z)
  have hoff : offBd Φ k σ' = ι ⁻¹' offBd Φ k σ := by
    ext z
    simp only [offBd, Set.mem_preimage, Set.mem_setOf_eq, under_eq_of_conj (hι z)]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => congrArg (_ * ·) ?_
  unfold PolDat.regFund
  split_ifs with hi
  · rw [hph, GlobalTheory.ShFam.RhoConj.rho_comp_conj _ _ σ σ' ι _ _ _ _ hι (P.om_kaehler k σ) (P.om_kaehler k σ')
      (P.om_conj k σ σ' ι hι) (P.exph_is k σ) (P.exph_is k σ') (P.exph_conj k σ σ' ι hι), hιy]
  · have hmem : y' ∈ offBd Φ k σ' ↔ y ∈ offBd Φ k σ := by rw [hoff, Set.mem_preimage, hιy]
    unfold extBd
    by_cases h : y ∈ offBd Φ k σ
    · rw [if_pos (hmem.2 h), if_pos h, hph, Function.comp_apply, hιy]
    · rw [if_neg (mt hmem.1 h), if_neg h, hph, Filter.limsup_comp, hoff,
        ι.isInducing.map_nhdsWithin_eq, Set.image_preimage_eq _ ι.surjective, hιy]

end GlobalTheory.RegConj

theorem GlobalTheory.Mean4O.Setup.reg_conj : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (σ σ' : D.what₂.LL →+* ℂ)
    (u : D.what₂.Tau → Fin O.N → ℝ) (t : ℝ) (y : Pts (O.var c) σ) (y' : Pts (O.var c) σ'),
    y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → O.met.reg c σ' u t y' = O.met.reg c σ u t y := by
  intro D O hO c σ σ' u t y y' hy
  obtain ⟨x, P, h⟩ := hO
  rw [h.reg_eq]
  exact GlobalTheory.RegConj.reg_conj_of P c u t hy
