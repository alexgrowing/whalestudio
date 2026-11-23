import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAMulEqZeroIffSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

theorem charR_hasDerivAt : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 →
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential

theorem biChar_contDiff : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) →
    (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) →
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter

section Phase

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

def phase (ψ : AddChar (AF F) ℂ) (M : ℝ →+ VA F N) (w : VA F N) (s : ℝ) : ℂ := ψ (⅟(2 : AF F) * symV w (M s))

theorem symV_add_left (w w' u : VA F N) : symV (w + w') u = symV w u + symV w' u := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_add_right (w u u' : VA F N) : symV w (u + u') = symV w u + symV w u' := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_zero_right (w : VA F N) : symV w 0 = 0 := by simp [symV]

theorem continuous_symV : Continuous fun p : VA F N × VA F N => symV p.1 p.2 := by
  unfold symV dotProduct
  fun_prop

theorem phase_add (M : ℝ →+ VA F N) (w : VA F N) (s s' : ℝ) :
    phase ψ M w (s + s') = phase ψ M w s * phase ψ M w s' := by
  simp only [phase, map_add, symV_add_right, mul_add, AddChar.map_add_eq_mul]

theorem phase_add_left (M : ℝ →+ VA F N) (w w' : VA F N) (s : ℝ) :
    phase ψ M (w + w') s = phase ψ M w s * phase ψ M w' s := by
  simp only [phase, symV_add_left, mul_add, AddChar.map_add_eq_mul]

theorem phase_zero (M : ℝ →+ VA F N) (w : VA F N) : phase ψ M w 0 = 1 := by
  simp [phase, symV_zero_right]

theorem continuous_phase (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) :
    Continuous fun p : VA F N × ℝ => phase ψ M p.1 p.2 := by
  have h1 : Continuous fun p : VA F N × ℝ => (p.1, M p.2) := by fun_prop
  have h2 : Continuous fun p : VA F N × ℝ => symV p.1 (M p.2) :=
    Continuous.comp (g := fun q : VA F N × VA F N => symV q.1 q.2) (f := fun p : VA F N × ℝ => (p.1, M p.2)) continuous_symV h1
  have h3 : Continuous fun p : VA F N × ℝ => ⅟(2 : AF F) * symV p.1 (M p.2) := continuous_const.mul h2
  exact hψ.comp h3

end Phase

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Crit

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem continuous_phase_right (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) :
    Continuous (phase ψ M w) := by
  have h : Continuous fun s : ℝ => ((w, s) : VA F N × ℝ) := by fun_prop
  exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2) (f := fun s : ℝ => ((w, s) : VA F N × ℝ))
    (continuous_phase hψ hM) h

theorem phase_hasDerivAt (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) (s : ℝ) :
    HasDerivAt (phase ψ M w) (deriv (phase ψ M w) 0 * phase ψ M w s) s :=
  charR_hasDerivAt _ (continuous_phase_right hψ hM w) (phase_add M w) (phase_zero M w) s

theorem contDiff_phase_deriv (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {k : ℕ}
    {L : (Fin k → ℝ) →+ VA F N} (hL : Continuous L) (u : VA F N) :
    ContDiff ℝ ∞ fun t => deriv (phase ψ M (u + L t)) 0 := by
  have e : (fun t => deriv (phase ψ M (u + L t)) 0) =
      fun t => deriv (phase ψ M u) 0 + deriv (phase ψ M (L t)) 0 := by
    funext t
    have hf : phase ψ M (u + L t) = fun s => phase ψ M u s * phase ψ M (L t) s := funext (phase_add_left M u (L t))
    have hd := ((phase_hasDerivAt hψ hM u 0).mul (phase_hasDerivAt hψ hM (L t) 0)).deriv
    simp only [phase_zero, mul_one, one_mul] at hd
    rw [hf]
    exact hd
  rw [e]
  have hQ : Continuous (Function.uncurry fun t s => phase ψ M (L t) s) := by
    have h : Continuous fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ) := by fun_prop
    exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2)
      (f := fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ)) (continuous_phase hψ hM) h
  exact contDiff_const.add (biChar_contDiff k (fun t s => phase ψ M (L t) s) hQ
    (fun t s s' => phase_add M (L t) s s') (fun t t' s => by simp only [map_add]; exact phase_add_left M _ _ s)
    (fun t => phase_zero M (L t)))

theorem hasDerivAt_lineV (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {f : VA F N → ℂ}
    {w : VA F N} {c : ℂ} (hd : HasDerivAt (fun s : ℝ => heisV ψ (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (phase ψ M w) 0 * f w) 0 := by
  have hp := phase_hasDerivAt hψ hM w 0
  have hne : ∀ s, phase ψ M w s ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * symV w (M s)) (-(⅟(2 : AF F) * symV w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
    have h0' : ψ (⅟(2 : AF F) * symV w (M s)) = 0 := h0
    rw [h0', zero_mul] at this
    exact one_ne_zero this
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisV ψ (M s) f w / phase ψ M w s := by
    funext s
    rw [heisV]
    exact (mul_div_cancel_left₀ _ (hne s)).symm
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisV ψ (M 0) f w = f w := by
    rw [heisV, map_zero, symV_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  rw [h1, phase_zero, mul_one]
  field_simp
  ring

theorem contDiff_of_heisV_closed (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (V : Set (VA F N → ℂ))
    (hc : ∀ f ∈ V, Continuous f)
    (hd : ∀ f ∈ V, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ V, ∀ w,
      HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (f' w) 0) :
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ VA F N), Continuous L → (∀ t, fin (L t).1 = 0 ∧ fin (L t).2 = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro f hf k L hL hLf u
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun G => ∃ f ∈ V, G = fun t => f (u + L t)
  refine GlobalTheory.Unf.MatCoef.contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h : Continuous fun t => u + L t := by fun_prop
    exact (hc f hf).comp h
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ VA F N := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    obtain ⟨f', hf', hD⟩ := hd f hf M ⟨hM, fun s => hLf _⟩
    refine ⟨2, ![fun _ => 1, fun t => -deriv (phase ψ M (u + L t)) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact (contDiff_phase_deriv hψ hM hL u).neg
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add, add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_lineV hψ hM (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end Crit

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}

theorem symplOHF_eq (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (w w' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ w w' = ⅟(2 : AF F) * symV (e w) (e w') := by
  rw [symplOHF, he, invOf_two_eq]

theorem heisOF_comp (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : WOF F E nS nT)
    (f : VA F N → ℂ) : heisOF σ JS JT ξ₀ ψ u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisOF, heisV, Function.comp_apply, symplOHF_eq he, map_add]

end Main

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem isThetaFunOF_thV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay F N B.ψ hR hψ Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add, symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h

end GlobalTheory.ThetaTransformF

end
