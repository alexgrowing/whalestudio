import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj

noncomputable section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev thLevel (l : Level H) {R : ℕ} (hR : R ^ 2 ∣ l.M) : Level H :=
  { l with A := R ^ 2, A_pos := Nat.pos_of_dvd_of_pos hR (lt_of_lt_of_le (by norm_num) l.three_le) }

theorem zeta_mem_of_dvd (c : Coeff l) {d : ℕ} (hd : d ∣ l.M) : zeta d ∈ c.F := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  obtain ⟨k, hk⟩ : d ∣ l.M' := hd.trans (Nat.dvd_lcm_left _ _)
  have hd0 : (d : ℂ) ≠ 0 := by
    rintro h
    have : d = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hk; omega
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h
    have : k = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hk; omega
  have : zeta d = zeta l.M' ^ k := by
    unfold zeta
    rw [← Complex.exp_nat_mul, hk]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem c.zeta_mem k

abbrev thCoeff (c : Coeff l) {R : ℕ} (hR : R ^ 2 ∣ l.M) : Coeff (thLevel l hR) :=
  ⟨c.F, c.fin, c.conj, zeta_mem_of_dvd c (Nat.lcm_dvd dvd_rfl hR), by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro z (rfl | rfl)
    · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
    · exact zeta_mem_of_dvd c hR⟩

def IsKeyFour (Xo : Moduli Dw l) (c : Coeff l) (K : Rul Xo c) : Prop :=
  IsUnit K ∧ K ∈ GlobalTheory.AllWt.secZ Xo c (fun i => 4 * GlobalTheory.ShFam.keyEx Dw i)

def UnitFr {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop := ∀ τ i, ‖dmin X.Gm y τ i‖ = 1

def TauExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (x : ℝ) (Z : Comp Xo c),
    CompLaws U h e → l.A = 1 → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) →
  ∀ (R R₁ : ℕ) (hR : R ^ 2 ∣ l.M), 2 ≤ R₁ → R₁ ∣ R →
  ∀ (Xo₂ : Moduli Dw (thLevel l hR)) (π : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t π),
    IsLevelMap Xo₂ Xo π m →
  ∀ nab : NabV Xo₂ (thCoeff c hR), IsNab Xo₂ (thCoeff c hR) nab →
  ∀ (n N : ℕ) (xs : Fin N → Fin n → Dw.La) (t : Fin N → Rul Xo₂ (thCoeff c hR)) (b : Fin N → 𝓞 c.F)
    (t₀ : Rul Xo₂ (thCoeff c hR)),
    (∀ i (u : Dw.La), ∃ w ∈ Submodule.span (𝓞 E) (Set.range (xs i)), ∃ v : Dw.La, u = w + R₁ • v) →
    (∀ i, t i ∈ sec Xo₂ (thCoeff c hR) (fun _ => 0) n ∧ Ref.IsThConst Xo₂ (thCoeff c hR) nab R (xs i) (t i)) →
    t₀ = ∑ i, algebraMap c.F (Rul Xo₂ (thCoeff c hR)) (b i : c.F) * t i →
    (∃ (k : Type) (_ : Field k) (_ : Algebra c.F k) (y₂ : FrPt Xo₂ (thCoeff c hR) k) (y : FrPt Xo c k),
      FrAbove m y₂ y ∧ evR Xo c (e Z) y = 1 ∧ evR Xo₂ (thCoeff c hR) t₀ y₂ ≠ 0) →
  ∀ (P : ℝ) (rh : ∀ σ k, Frame ((U σ).X k).Ψ r → ℝ),
    (∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∀ y ∈ ((U σ).X k).dom, ∀ g ∈ Bor ((U σ).X k).Ψ r,
      ∀ hy : rmul y g ∈ ((U σ).X k).dom, UnitFr ((U σ).X k) (rmul y g) →
      ∀ y₂ : FrPt Xo₂ (thCoeff c hR) (CAt σ), FrAbove m y₂ ((U σ).un k ⟨rmul y g, hy⟩) →
        ‖toC (evR Xo₂ (thCoeff c hR) t₀ y₂)‖ ≤ Real.exp (P - rh σ k y / 2)) →
  ∀ (K : Rul Xo c) (β : ℕ → ℝ) (RK : ℝ), IsKeyFour Xo c K →
    (∀ p : ℕ, p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal →
      ∀ y : (Ref.pjSys Xo c).Pt la, ((-(ramOverZ la * β p) : ℝ) : EReal) ≤ (Ref.pjSys Xo c).val y K) →
    (∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∀ y ∈ ((U σ).X k).dom, UnitFr ((U σ).X k) y →
      lieFacZ Dw x (fun _ => 4) * ‖rdU (U σ) K k y‖ ≤ Real.exp RK) →
  ∃ τ ∈ secZ Xo c (fun _ => 4 * (n : ℤ)),
    (∀ (p : TRing c.F) (y₂ : FrPt Xo₂ (thCoeff c hR) p.R) (y : FrPt Xo c p.R), FrAbove m y₂ y →
      τ p y = t₀ p y₂ ^ 8 * K p y ^ n) ∧
    evC h Z τ ≠ 0 ∧
    (∀ p : ℕ, p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal →
      ∀ y : (Ref.pjSys Xo c).Pt la,
        ((8 * ((R : ℝ) ^ 2)⁻¹ * Ref.phU Xo c la y - ramOverZ la * (n * β p) : ℝ) : EReal) ≤
          (Ref.pjSys Xo c).val y τ) ∧
    ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∀ y ∈ ((U σ).X k).dom,
      lieFacZ Dw x (fun _ => 4 * (n : ℤ)) *
          ((U σ).X k).pnorm (laZ (U σ) (fun _ => 4 * (n : ℤ)) k) (rdU (U σ) τ k) y ≤
        Real.exp (4 * (2 * P - rh σ k y) + n * RK)

namespace TauTest

variable {Xo : Moduli Dw l} {c : Coeff l}

open HostModel in

def sqLevel (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Level H where
  M := (H.d + 4) ^ 2
  three_le := by nlinarith [H.d_prime.two_le]
  odd := (level H 1 one_pos).odd.pow
  Mb := Ideal.span {(2 - H.rt) ^ 2}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, pow_mem (sub_mem (ofNat_mem _ 2) (rt_mem_adjoin H)) 2⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [← Ideal.span_singleton_pow, Ideal.map_pow, map_bar_span_two_sub_rt, ← mul_pow,
      Ideal.span_singleton_mul_span_singleton, two_sub_rt_mul_two_add_rt, Ideal.span_singleton_pow, Nat.cast_pow]
  coprime := by
    rw [← Ideal.span_singleton_pow, Ideal.map_pow, map_bar_span_two_sub_rt, ← Ideal.isCoprime_iff_sup_eq]
    exact ((Ideal.isCoprime_span_singleton_iff _ _).2 (isCoprime_two_sub_rt_two_add_rt H)).pow
  A := 1
  A_pos := one_pos

end TauTest

end GlobalTheory.CompanionTheory.Ar.Rec
