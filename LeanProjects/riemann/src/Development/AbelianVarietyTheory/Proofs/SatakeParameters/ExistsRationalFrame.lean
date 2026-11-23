import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI

noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_place {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[l]) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal ∧ ∀ x : K, v.valuation K x ≤ 1 → ‖ψ x‖ ≤ 1 := by
  have hint : ∀ a : 𝓞 K, ‖ψ (a : K)‖ ≤ 1 := fun a => norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)
  let P : Ideal (𝓞 K) :=
    { carrier := {a | ‖ψ (a : K)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        have e : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        simp only [Set.mem_ofPred_eq, e, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have e : ((c * a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        simp only [Set.mem_ofPred_eq, smul_eq_mul, e, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (hint c)).trans_lt ha }
  have hP : ∀ a : 𝓞 K, a ∈ P ↔ ‖ψ (a : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((l : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have : (((l : ℕ) : 𝓞 K) : K) = (l : K) := by simp
    rw [this, map_natCast]
    have h2 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h2, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hpr : P.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} h => ?_⟩
    · have : (1 : 𝓞 K) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at this
      simp at this
    · rw [hP, hP]
      rw [hP] at h
      by_contra hn
      push Not at hn
      have e : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [e, map_mul, norm_mul] at h
      exact absurd (one_le_mul_of_one_le_of_one_le hn.1 hn.2) (not_le.2 h)
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hl
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)
  refine ⟨⟨P, hpr, hne⟩, hl, fun x hx => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := ⟨P, hpr, hne⟩) x hx
  have hd : ‖ψ ((d : 𝓞 K) : K)‖ = 1 := le_antisymm (hint _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖ψ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖ψ x‖ * ‖ψ ((d : 𝓞 K) : K)‖ = ‖ψ (n : K)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hint n

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

theorem applyAt0_smul {Lt : Type} (N0 N1 l : ℕ) [Fact l.Prime] (a : ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    KM.applyAt0 N0 N1 l (a • Th) P = a • KM.applyAt0 N0 N1 l Th P := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.smul_monomial, map_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def rescale (E : KerEnt D Dx Tw)
    (t : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → ℂ_[D.what₂.places.resChar w])
    (ht : ∀ u μ w i c c', t u μ w i c c' ≠ 0) : KerEnt D Dx Tw :=
  { E with
    Th := fun u μ w i c c' => (E.un u μ w i c c' / t u μ w i c c') • E.Th u μ w i c c'
    un := t
    un_ne := ht
    kform := fun u μ w hw i hi c c' v v' h I => by
      rw [E.kform u μ w hw i hi c c' v v' h I, applyAt0_smul, map_smul, smul_eq_mul, ← mul_assoc,
        mul_div_cancel₀ _ (ht u μ w i c c')] }

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

def RamTie (Dx : DivX D) (Tp : TupTied D C nch) : Prop :=
  ∀ μ (l : ℕ), l.Prime → (l ∉ Dx.Qp μ ↔ ∀ v, OverP D.host l v → (Tp.xi μ).UnrAt v)

def FrameOf {u : D.what₂.Word} {μ : D.what₂.Tup} (g : Reps D u μ) (fr : Frames D u μ) {l : ℕ} [Fact l.Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]) {i : ℕ} (c : (D.chTw u μ).cls i) (y : (D.chTw u μ).Y i) : Prop :=
  ∀ τ, IsLatFrame lam D.host (embTau D τ) (g i c) (fr i y τ)

def UnTie (E : KerEnt D Dx Tw) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ y y', FrameOf (g u μ) (fr u μ) (E.lam w) c y ∧ FrameOf (g u μ) (fr u μ) (E.lam w) c' y' ∧
      E.un u μ w i c c' = lamV (E.lam w) (epsFr D u μ i c c' y y')

def EpsPowIn (D : D7) : Prop :=
  ∀ u μ i, i < D.R.m → ∀ c c', ∃ n : ℕ, 0 < n ∧ eps D u μ i c c' ^ n ∈ Set.range D.what₂.embLL

def UnitAtLam (Tp : TupTied D C nch) (lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (u : D.what₂.Word) (μ : D.what₂.Tup) (g : Reps D u μ) (fr : Frames D u μ) : Prop :=
  ∀ w : D.what₂.places.Pl, PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
      (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)),
      FrameOf g fr (lam w) c y → FrameOf g fr (lam w) c' y' → UnitAt (lam w) (epsFr D u μ i c c' y y')

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
