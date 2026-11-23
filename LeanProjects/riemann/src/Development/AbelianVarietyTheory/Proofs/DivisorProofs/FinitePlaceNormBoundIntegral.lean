import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingPlaceExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingsSameNormConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstEqFalseOfMemSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtSpMapEqDrViaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPowerStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

theorem drAt_le_of_finN_le : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (a : ℝ), (∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ e y, finN Φ k la v e y f ≤ NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) ^ a) → ∀ (ι : AlgebraicClosure D.what₂.LL →+* ℂ_[p]) (y : AlgPt (Φ.C k).Y), drAt Φ k la p (spMap ι ≫ y.1) f ≤ (p : ℝ) ^ (-a) := by
  intro _ _ D A N j S κ s Φ k la f hf p _ a h ι y
  obtain ⟨v, e, hv, hι⟩ := GlobalTheory.T.p_adic_embedding_place_extension D.what₂.LL p ι
  have hio : ∀ b, ‖ioOf p e b‖ ≤ 1 ↔ b ∈ e.O := ioOf_le_one_iff p hv e
  have h1 := log_w_eq p e ι hι
  have h2 := log_w_eq p e (ioOf p e) hio
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hwp : e.w (p : AlgebraicClosure D.what₂.LL) = NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) := by
    simpa using e.w_alg (p : D.what₂.LL)
  have hwp1 : NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) < 1 := by
    have h4 := (FinitePlace.norm_lt_one_iff_mem D.what₂.LL v (p : 𝓞 D.what₂.LL)).2 hv
    rw [← FinitePlace.norm_embedding]
    simpa using h4
  have hwp0 : 0 < e.w (p : AlgebraicClosure D.what₂.LL) :=
    e.w.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  set c := -Real.log (e.w p) / Real.log p with hcdef
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hwp0 (hwp ▸ hwp1))) hlp
  have hnorm : ∀ b, ‖ι b‖ = ‖ioOf p e b‖ := by
    intro b
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · have e3 : Real.log ‖ι b‖ = Real.log ‖ioOf p e b‖ := by
        have := (h1 b).symm.trans (h2 b)
        exact mul_left_cancel₀ hc.ne' this
      exact Real.log_injOn_pos (norm_pos_iff.2 ((map_ne_zero _).2 hb)) (norm_pos_iff.2 ((map_ne_zero _).2 hb)) e3
  obtain ⟨σ, hσ, hσι⟩ := GlobalTheory.T.p_adic_embeddings_same_norm_conjugate D.what₂.LL p ι (ioOf p e) hnorm
  have hι' : ι = σ.toRingHom.comp (ioOf p e) := RingHom.ext fun b => (hσι b).symm
  have e1 : drAt Φ k la p (spMap ι ≫ y.1) f = drVia Φ k la p y.1 (ioOf p e) f := by
    rw [hι']
    have : spMap (σ.toRingHom.comp (ioOf p e)) = spMap σ.toRingHom ≫ spMap (ioOf p e) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [this, Category.assoc, GlobalTheory.T.drAt_spMap_eq_drVia D A N j S κ s Φ k la p _ σ.toRingHom, GlobalTheory.T.drVia_isometry_invariant D A N j S κ s Φ k la p σ hσ, GlobalTheory.T.drAt_spMap_eq_drVia D A N j S κ s Φ k la p _ (ioOf p e) y.1 f]
  have h3 := h v hv e y
  rw [GlobalTheory.T.finite_norm_eq_drVia_power D A N j S κ s Φ k la f hf p v hv e y] at h3
  have hwpc : NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) = (p : ℝ) ^ (-c) := by
    rw [← hwp, Real.rpow_def_of_pos (by linarith), hcdef]
    field_simp
    rw [Real.exp_log hwp0]
  rw [e1]
  have h0 := drVia_nonneg Φ k la p y.1 (ioOf p e) f
  refine (Real.rpow_le_rpow_iff h0 (Real.rpow_nonneg (by linarith) _) hc).1 (h3.trans_eq ?_)
  rw [hwpc, ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  ring_nf

end GlobalTheory.CovHt.Link
