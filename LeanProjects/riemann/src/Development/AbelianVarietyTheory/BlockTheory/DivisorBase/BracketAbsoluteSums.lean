import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalRingCardinality.DataMink

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlacesAboveMainDegree

open Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits NumberField

theorem finite_over (D : D7) (p : ℕ) : {w : D.what₂.places.Pl | D.what₂.places.resChar w = p}.Finite := by
  by_cases hp : p = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    intro w hw
    exact absurd (hw.trans hp) (D.what₂.places.resChar_prime w).ne_zero
  have hI : (Ideal.span {(p : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine Set.Finite.subset ((Ideal.finite_factors hI).preimage D.plEq.injective.injOn) ?_
  intro w hw
  have hw' : D.what₂.places.resChar w = p := hw
  have h1 := D.what₂.places.val_resChar w
  have h0 : ((p : ℕ) : D.what₂.LL) ≠ 0 := by exact_mod_cast hp
  rw [hw', D.val_eq w _ h0] at h1
  have h2 : vAdd (D.plEq w) ((p : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
  have h3 := D.what₂.places.ramIdx_pos w
  show (D.plEq w).asIdeal ∣ _
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd (K := D.what₂.LL)]
  refine lt_of_le_of_ne (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) (fun h => ?_)
  unfold vAdd at h2
  have h4 : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL (p : 𝓞 D.what₂.LL)) = ((p : ℕ) : D.what₂.LL) := map_natCast _ _
  have h5 : (D.plEq w).valuation D.what₂.LL ((p : ℕ) : D.what₂.LL) = 1 := h4 ▸ h
  rw [h5, WithZero.log_one] at h2
  omega

def plAbove (D : D7) (p : ℕ) : Finset D.what₂.places.Pl := (finite_over D p).toFinset

def Dpi (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ : D.what₂.Tau, nuAbs D u j τ

open Classical in

def mainDeg {D : D7} (L : SizeData₂ D) (j : ℕ) : ℝ :=
  (∑ t : D.host.TT, (L.aT t : ℝ)) + ∑ ρ ∈ Finset.univ.filter (fun ρ => ρ ∉ topsOf D.host D.eTau), wj D j ρ

def errDeg {D : D7} (L : SizeData₂ D) : ℝ :=
  (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + G.Nm D ^ 2 + (D.R.m : ℝ) * D.R.t * L.etaSz) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x

def bracketT (D : D7) (u : D.what₂.Word) : ℝ :=
  2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) + (D.R.f : ℝ) * G.Nm D +
    (D.host.TT.card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

def Off (D : D7) (u : D.what₂.Word) (p : ℕ) : Prop :=
  p ≠ D.host.g 0 ∧ p ≠ D.host.g 1 ∧ p ≠ (D.mem u).A.T ∧ p ≠ D.host.d

def InertLow {D : D7} (L : SizeData₂ D) (p : ℕ) : Prop :=
  (G.IsResidueClassZero D p ∨ G.IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n

def absSum {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (S : Finset D.what₂.places.Pl) : ℝ :=
  ∑ w ∈ S, SizeData₂.sz w |Eval L X K c u j w|

structure SizesAtLift {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (C : ℝ) (u : D.what₂.Word) (j : ℕ) :
    Prop where

  deg : |Dpi D u j - (fockDeg D j : ℝ) - mainDeg L j| ≤ C * errDeg L

  sumT_eq : ∑ w ∈ plAbove D (D.mem u).A.T, SizeData₂.sz w (Eval L X K c u j w) =
    bracketT D u * Real.log ((D.mem u).A.T : ℝ)

  sumT_le : absSum L X K c u j (plAbove D (D.mem u).A.T) ≤ C * L.B0

  cTop : ∀ t : G.HH D, t ∈ D.host.TT →
    ctD D u j t * Real.log D.host.d ≤ 2 * (L.sc.b + 2 * D.R.k * L.sc.b') * Real.log D.host.d

  cOther : ∀ t : G.HH D, t ∉ D.host.TT →
    ctD D u j t * Real.log D.host.d ≤ 4 * D.R.k * L.sc.b' * Real.log D.host.d

  absD : ∀ w ∈ plAbove D D.host.d,
    |Eval L X K c u j w| ≤ (D.host.TT.card : ℝ) * L.sc.b + (D.R.f : ℝ) * D.R.k * L.sc.b'

  sumD : absSum L X K c u j (plAbove D D.host.d) ≤ 3 * (D.R.f : ℝ) * D.R.m * L.sc.b
  sumD_le : absSum L X K c u j (plAbove D D.host.d) ≤ L.B0

  sumInert : ∀ S : Finset D.what₂.places.Pl,
    (∀ w ∈ S, Off D u (D.what₂.places.resChar w) ∧ InertLow L (D.what₂.places.resChar w)) →
      absSum L X K c u j S ≤ C * L.B0

  sumRest : ∀ S : Finset D.what₂.places.Pl,
    (∀ w ∈ S, Off D u (D.what₂.places.resChar w) ∧ ¬ InertLow L (D.what₂.places.resChar w)) →
      absSum L X K c u j S ≤ C * L.B0

structure TypeAtLift {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ) : Prop where

  loss : ∀ (i : Fin 2), ∀ w ∈ plAbove D (D.host.g i), Eval L X K c u j w =
    Fval L j w + vNN X i u j w + c.g * (D.R.f : ℝ) * (G.Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)

  pair : ∀ (i : Fin 2), ∀ w ∈ plAbove D (D.host.g i),
    vNN X i u j w + vNN X i u j (D.what₂.places.conj w) = Dpi D u j

def ItemsAt {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (C : ℝ) : Prop :=
  ∀ u : D.what₂.Word, ∀ j ∈ SizeData₂.lifts D, SizesAtLift L X K c C u j ∧ TypeAtLift L X K c u j

def GamDvd (D : D7) : Prop := ∀ u, (D.mem u).C.DGam ∣ minkM (2 * D.R.f * D.R.N D.R.m)

def ItemsWith {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), GamDvd (Fm.D x i) →
    ItemsAt (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err C

def LossItems {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ItemsWith Fm C

def LossItemsAll {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ItemsAt (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err C

def LossItemsAbs (𝒞 : FamClass) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), 𝒞 Fm → ItemsWith Fm C

def ShiftBound : Prop :=
  ∀ (l d : ℕ) [NeZero d] (Ds Es : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) → (∀ s, 0 ≤ Es s) →
    |lpF l d (fun s => Ds s + Es s) - lpF l d Ds| ≤ ∑ s, Es s

def ShiftSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ C : ℝ, ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
    C * (exch (Fm.D x i) * (Fm.L x i).sc.X'' (Fm.D x i).R.n) ≤ (Fm.L x i).sc.b

theorem GamDvd.ne_zero {D : D7} (h : GamDvd D) (u : D.what₂.Word) : (D.mem u).C.DGam ≠ 0 := by
  refine ne_zero_of_dvd_ne_zero ?_ (h u)
  unfold minkM Formalism.HermitianLatticeCounting.S6.minkowskiM
  refine Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ ?_
  have := (Finset.mem_filter.1 hp).2
  exact this.ne_zero

end GlobalTheory.IndefiniteRowSideFullHecke.PlacesAboveMainDegree

end
