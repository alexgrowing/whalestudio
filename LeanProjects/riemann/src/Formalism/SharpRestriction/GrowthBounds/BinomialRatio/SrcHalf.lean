import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def MonoAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p r : ℕ) [NeZero r] {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (b : SegBlock s r) (m m' : ℝ), m ≤ m' →
    (blockData p S aTop aPlus m' b).SSZ O (r := r) ≤ (blockData p S aTop aPlus m b).SSZ O (r := r)

def PlaneAt : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (m : ℕ) (φ : WF p n' ≃+* W) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e e' : Edge W Qq (m + 1)), IsFractionRing W Qq →
    IsGLW g → IsGLW g' → IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    IsEdgeBasis p 1 e' (h * ((matQ φ g')⁻¹).transpose) → ratPlane p n' 1 g' = ratPlane p n' 1 g → e' = e

def SymIntAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
    (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)).SSZ O
      (r := X.m)) →
    InA (O := O) (symFam (KK O) X.p C0 CE1 CE2 X β s)

theorem scale_one_mem {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {M : Submodule O V} {x : V} (hx : x ∈ scale (1 : Kf) M) : x ∈ M := by
  simp only [scale, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem srcHalf_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc H : ℝ} (hCm : 13 ≤ Cm) (hCt : 30 ≤ Ct)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (h44 : Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : MonoAt) (hP : PlaneAt) (hI : SymIntAt C0 CE1 CE2) :
    SrcHalfAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  intro X _ _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1 φ hφ h Θ hΘ e he hsrc g hg hgE β hβ s hs
  letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have St := hstd X hD1 hH hc
  have hw0 : w ≠ 0 := hS.2.1.ne_zero
  haveI : IsFractionRing O Kf := hS.1.frac_O

  have hmar : 13 * X.k * X.N1 * X.Q * (X.c : ℝ) + 12 * (X.c : ℝ) ≤ X.m0 Cm := by
    have hk : 0 ≤ X.k := by unfold Loc.k; positivity
    have hQ : 0 ≤ X.Q := by unfold Loc.Q; positivity
    have h1 : 0 ≤ X.k * X.N1 * X.Q * (X.c : ℝ) := by positivity
    unfold Loc.m0 m0G4 m1G4
    nlinarith
  have hs' : ∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
      (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + 12 * (X.c : ℝ)) (β j)).SSZ O (r := X.m) := fun j =>
    hM O X.p X.m _ _ _ (β j) _ _ hmar (hs j)
  obtain ⟨F, hFP, hA, hcong, hg'⟩ := h44 X O (dvrOfStd hS) (dvrOfStd_sq hS) hD1 hH hc (12 * (X.c : ℝ)) (Or.inr rfl)
    g hg β hβ s hs'
  let F' : ↥((Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)).restrictScalars O) := ⟨F, hFP⟩
  refine ⟨F', ?_, hcong⟩
  obtain ⟨h1, h2, h3⟩ := hΘ
  set o := ∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j) with ho
  have hot : o ≤ ⌊X.t0 C0 Ct⌋₊ := Nat.le_floor (ord_all St hCt β hβ)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hAo : InA (O := O) (((w ^ o : O) • F' : ↥((Pol (KK O) (ι := X.TT × Bool) (X.m + 1)
        (hhDegs X.TT X.aT X.bT)).restrictScalars O)) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) := by
      have : (((w ^ o : O) • F' : ↥((Pol (KK O) (ι := X.TT × Bool) (X.m + 1)
          (hhDegs X.TT X.aT X.bT)).restrictScalars O)) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) =
          C (algebraMap O (KK O) ((dvrOfStd hS).w ^ o)) * F := by
        rw [Submodule.coe_smul, Algebra.smul_def, MvPolynomial.algebraMap_apply]
        rfl
      rw [this]; exact hA
    have hmem := (h1 _).1 hAo
    rw [map_smul] at hmem
    rw [hsrc]
    have hne : algebraMap O Kf w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O Kf)).2 hw0
    have key : ∀ v : ↥(VHH (m := X.m) Kf X.TT X.aT X.bT),
        (algebraMap O Kf w ^ (-(⌊X.t0 C0 Ct⌋₊ : ℤ))) • ((w ^ ⌊X.t0 C0 Ct⌋₊ : O) • v) = v := by
      intro v
      rw [← algebraMap_smul Kf (w ^ ⌊X.t0 C0 Ct⌋₊) v, smul_smul, map_pow, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul]
    refine ⟨(w ^ (⌊X.t0 C0 Ct⌋₊ - o)) • ((w ^ o) • Θ F'), ?_, ?_⟩
    · exact Submodule.smul_mem _ _ hmem
    · show (algebraMap O Kf w ^ (-(⌊X.t0 C0 Ct⌋₊ : ℤ))) • ((w ^ (⌊X.t0 C0 Ct⌋₊ - o)) • ((w ^ o) • Θ F')) = Θ F'
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hot]
      exact key _
  ·
    have hint : InWjRg X.p X.n' O w 1 (hhLetters X.TT) g F 0 := by
      intro mm
      obtain ⟨a, ha⟩ := hI X O _ β s hs' mm
      obtain ⟨b, hb⟩ := hcong mm
      refine ⟨a + w ^ X.c * b, ?_⟩
      have e1 := congrArg (fun P => P) (sub_add_cancel (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g F)
        (symFam (KK O) X.p C0 CE1 CE2 X β s))
      rw [pow_zero, one_mul, map_add, ← ha]
      have : (dvrOfStd hS).w = w := rfl
      rw [this] at hb
      rw [← hb, ← MvPolynomial.coeff_add, add_sub_cancel]
    have := (h2 g hg e hgE F' 0).1 hint
    have h0 : (algebraMap O Kf w ^ ((0 : ℕ) : ℤ)) = 1 := by simp
    rw [h0] at this
    exact scale_one_mem this
  ·
    refine (Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hh => ?_
    obtain ⟨he', hsrc', hne⟩ := hh
    obtain ⟨g', hg'1, hg'E⟩ := h3 e' he' (hsrc'.trans hsrc)
    have hpl : ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g := fun heq =>
      hne (hP X.p X.n' W Qq X.m φ h g g' e e' hS.1.frac_alt hg hg'1 hgE hg'E heq)
    have := hg' g' hg'1 hpl
    exact (h2 g' hg'1 e' hg'E F' X.c).1 this

end Formalism.MainNotions.ColumnSystems.Pf
