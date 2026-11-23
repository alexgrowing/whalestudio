import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdThSympl

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

def perL (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun u := fun j => perC X x u (idx j)
  map_add' u v := by
    funext j
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext j
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

include idx in

theorem span_emb (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v) = ⊤ := by
  have h1 : (Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v)).map (perL X idx x) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_range_pv idx hs hx
  have hsurj : Function.Surjective (perL X idx x) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← h1]
    exact LinearMap.map_le_range
  have hd : Module.finrank ℝ (X.Ψ → Fin r → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    have := Fintype.card_congr idx
    simp only [Fintype.card_fin, Fintype.card_prod] at this
    simp only [Module.finrank_pi_fintype, finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, this]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hsurj
  apply Submodule.map_injective_of_injective hinj
  rw [h1, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

theorem im_hx_perC (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    (GlobalTheory.Dict.hx X bas idx x (fun j => perC X x u (idx j)) (fun j => perC X x v (idx j))).im =
      ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re := by
  let B₁ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (perL X idx x u) (perL X idx x v)).im)
    (fun u u' v => by simp only [Geo.Tor.hermForm, map_add, add_dotProduct, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, smul_dotProduct, smul_im])
    (fun u v v' => by simp only [Geo.Tor.hermForm, map_add, star_add, mulVec_add, dotProduct_add, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_im])
  let B₂ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re)
    (fun u u' v => by simp only [hermC, Pi.add_apply, add_mul, mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun u v v' => by simp only [hermC, Pi.add_apply, map_add, mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul, map_mul, conj_ofReal]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hB : B₁ = B₂ := by
    refine LinearMap.ext_on_range (span_emb idx hs hx) fun a => LinearMap.ext_on_range (span_emb idx hs hx) fun b => ?_
    have h1 : (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (pv X idx x a) (pv X idx x b)).im = (EF X a b : ℝ) :=
      im_hermForm_Hm idx hs hx a b
    refine h1.trans ?_
    rw [EF_def, TraceFormIndependence.trace_re X]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : τ.1 (herm X.Gm a b) = hermC τ.1 X.Gm (Data.emb τ.1 a) (Data.emb τ.1 b) := by
      simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, h2]
  rw [hx_eq_hermForm]
  exact LinearMap.congr_fun₂ hB u v

end Classical

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.StdRat.tauE_injective D h.choose_spec]

theorem sum_four {m n : ℕ} (c : ℂ) (G : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ b, 2 * (c * ∑ d, ∑ e, x d b * -G e d * conj (y e b)).re =
      -(2 * (c * ∑ a, ∑ b, ∑ e, ∑ d, (if a = b then (1 : ℂ) else 0) * conj (y e b) * G e d * x d a).re) := by
  rw [← Finset.mul_sum, ← re_sum, ← Finset.mul_sum, ← mul_neg, ← neg_re, ← mul_neg]
  congr 3
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb.symm]) (by simp), Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib, if_true]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem psi_symplOH_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV _ hM hs x hx v w hv
  subst hr
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.real_adele_ext_and_char D θ σ hσ _ (GlobalTheory.OrientedHeis.snd_symplO (y := w) (Or.inl hv))).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.OrientedHeis.valTau_symplO hθ τ v w] at e
  refine e.trans ?_
  congr 1
  rw [neg_mul, ← mul_neg, ← ofReal_neg]
  congr 2
  unfold zOf
  simp only [im_hx_perC idx hs hx]
  rw [Finset.sum_comm]
  have hb : Function.Bijective fun ρ : D.what₂.Tau => (⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩ : X.Ψ) :=
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hM.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  rw [← hb.sum_comp]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hk : -(X.κ0 / 2) = D.host.xi0 := by rw [hM.kap]; ring
  have hG : ∀ a b, tauE D ρ (X.Gm a b) = -tauE D ρ (W.gram b a) := fun a b => by
    rw [hM.model.1, ← map_neg]; rfl
  have h1 : ∀ a b, tauE D ρ (V.gram⁻¹ a b) = if a = b then 1 else 0 := fun a b => by
    rw [hV, inv_one, Matrix.one_apply]; split_ifs <;> simp
  simp only [realM_tauE, hk, hermC, hG, GlobalTheory.OrientedHeis.formAt, h1]
  exact (sum_four _ (fun e d => tauE D ρ (W.gram e d)) _ _).symm

theorem psi_symplOH_eq_of_isONFr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) :=
  fun D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx =>
    psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x (PIW.FdPA.orthonormal_domain r X x hx)

end GlobalTheory.AdThSympl

end
