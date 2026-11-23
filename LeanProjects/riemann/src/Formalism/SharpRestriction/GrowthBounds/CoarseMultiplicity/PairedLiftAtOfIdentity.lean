import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Beyond44OfRestRawTail
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def TestFlatAt1 : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
    letI : Algebra (WF p n') O := algOfIdent jO φ
    ∃ (h h' : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
      (Θ Θ' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT))
      (Ξ : ↥(VHH (m := m) Kf TT aT bT) →ₗ[Kf] Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT)),
      (IsFlatTheta ι σ jO w φ TT aT bT h Θ ∧ e.src = colSpan W h ∧
        IsEdgeBasis p 1 e (h * ((matQ φ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')))⁻¹).transpose)) ∧
      (IsEdge p n' 1 e.dual ∧ IsFlatTheta ι σ jO w φ TT aT bT h' Θ' ∧ e.dual.src = colSpan W h' ∧
        IsEdgeBasis p 1 e.dual (h' * ((matQ φ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')))⁻¹).transpose)) ∧
      (∀ (t c : ℕ), ∀ v ∈ CCe p ι σ w TT aT bT t c e.dual, Ξ v ∈ CCe' p ι σ w TT aT bT t c e) ∧
      (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
        liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ∈
            Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ∧
      ∀ (F F' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (y : O),
        zTen (KK O) p m TT aT bT *
          fock (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
              (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)))
            (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
              (F' : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O))) =
          algebraMap O (KK O) y →
        beHH (m := m) p TT aT bT (Θ F) (Ξ (Θ' F')) = algebraMap O Kf y

section
open Formalism.GradedWeylDivisibility TF
open Formalism.L2.G.Model (dE dual_edgeBasis pQ_ne edgeBasis dual_edge Th0)

theorem testFlatAt1 : TestFlatAt1 := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS φ hφ m TT aT bT hm e he
  letI : Algebra (WF p n') O := algOfIdent jO φ
  obtain ⟨b, hb⟩ := edgeBasis hS m 1 e he
  have hb' := dual_edgeBasis p 1 (pQ_ne hS) e b hb
  obtain ⟨Θ, hΘ1, hΘ2⟩ := flatTheta hS φ hφ m TT aT bT hm b hb.1
  obtain ⟨Θ', hΘ1', hΘ2'⟩ := flatTheta hS φ hφ m TT aT bT hm _ hb'.1
  obtain ⟨thK, hthK⟩ := exists_thK Kf hm (vecH TT) (hhDegs TT aT bT)
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (settingCZ p n' W Qq O Kf ι σ jO w hS).2
  have hMD : MultDiv O p (kapZ p m TT aT bT) (k := m + 1) (hhDegs TT aT bT) :=
    multDiv_kapFl O p hpO (k := m + 1) (hhDegs TT aT bT)
  refine ⟨b, _, Θ, Θ', XiH thK (zK Kf p (kapZ p m TT aT bT) TT aT bT),
    ⟨hΘ1, hb.2.1, by rw [mul_matQ_one]; exact hb⟩,
    ⟨(dual_edge hS m 1 e he).1, hΘ1', hb'.2.1, by rw [mul_matQ_one]; exact hb'⟩,
    fun t c v hv => Xi_CC thK hS hm hthK _ hMD e he t c v hv,
    fun F => lift_Pol hS φ hφ m TT aT bT 1 (isGLW_one _) F.1 F.2,
    fun F F' y hy => pairing thK hS φ hφ hthK b hb.1 hb'.1 Θ Θ' hΘ2 hΘ2' F F' y hy⟩

end

def SrcHalfAt1 (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ φ : WF X.p X.n' ≃+* W, IsWittIdent σ φ →
    ∀ (h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) Qq) Θ, IsFlatTheta ι σ jO w φ X.TT X.aT X.bT h Θ →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e → e.src = colSpan W h →
      IsEdgeBasis X.p 1 e (h * ((matQ φ (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')))⁻¹).transpose) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (X.m0 Cm) (β j)).SSZ O (r := X.m)) →
      ∃ F, Θ F ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        (letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
         InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c)

theorem srcHalf1_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc H : ℝ} (hCm : 13 ≤ Cm) (hCt : 30 ≤ Ct)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (h44 : CoarseMultiplicityAtIdentity C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : MonoAt) (hP : PlaneAt) (hI : SymIntAt C0 CE1 CE2) :
    SrcHalfAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  intro X _ _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1 φ hφ h Θ hΘ e he hsrc hgE β hβ s hs
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
  have h44' := h44 X O (dvrOfStd hS) (dvrOfStd_sq hS) hD1 hH hc (12 * (X.c : ℝ)) (Or.inr rfl) β hβ s hs'
  have hg : IsGLW (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) := TF.isGLW_one _
  generalize hg1 : (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) = g at hgE h44' hg ⊢
  obtain ⟨F, hFP, hA, hcong, hg'⟩ := h44'
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

theorem paired_lift_at_of_identity {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ} (hW : WittIdent) (hT : TestFlatAt1)
    (hSrc : SrcHalfAt1 C0 CYb Cde Ck CD Cb CE1 CE2 13 Ct Cc) (hForm : FormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) :
    PairLiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1 e he
  haveI : Fact X.p.Prime := ⟨hS.1.prime⟩
  haveI := hS.1.frac_O
  obtain ⟨φ, hφ⟩ := hW X.p X.n' W Qq O Kf ι σ jO w hS.1
  letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
  have hm : 1 ≤ X.m := Nat.one_le_iff_ne_zero.2 (NeZero.ne X.m)
  obtain ⟨h, h', Θ, Θ', Ξ, ⟨hΘ, hsrc, hgE⟩, ⟨he', hΘ', hsrc', hgE'⟩, hΞ, hPol, hpair⟩ :=
    hT X.p X.n' W Qq O Kf ι σ jO w hS.1 φ hφ X.m X.TT X.aT X.bT hm e he
  obtain ⟨κ, s, s', hκ, hmem, hform⟩ := hForm X W Qq O Kf ι σ jO w hS hH hc hc1

  have hF : ∀ (β : GlobalTheory X) (u : Vecs O C0 CE1 CE2 X), ∃ Fv : ↥(VHH (m := X.m) Kf X.TT X.aT X.bT),
      (¬ (KeptAll C0 CE1 CE2 X β ∧ FamOK O C0 CE1 CE2 Cm X β u) → Fv = 0) ∧
      (KeptAll C0 CE1 CE2 X β → FamOK O C0 CE1 CE2 Cm X β u →
        Fv ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        ∃ F, Fv = Θ F ∧ InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) -
            symFam (KK O) X.p C0 CE1 CE2 X β (s β u)) X.c) := by
    intro β u
    by_cases hk : KeptAll C0 CE1 CE2 X β ∧ FamOK O C0 CE1 CE2 Cm X β u
    · obtain ⟨F, hF1, hF2⟩ := hSrc X W Qq O Kf ι σ jO w hS hH hc hc1 φ hφ h Θ hΘ e he hsrc hgE β hk.1 (s β u)
        (hmem β u hk.1 hk.2).1
      exact ⟨Θ F, fun hn => absurd hk hn, fun _ _ => ⟨hF1, F, rfl, hF2⟩⟩
    · exact ⟨0, fun _ => rfl, fun a b => absurd ⟨a, b⟩ hk⟩
  have hG : ∀ (β : GlobalTheory X) (u : Vecs O C0 CE1 CE2 X), ∃ Gv : Module.Dual Kf ↥(VHH (m := X.m) Kf X.TT X.aT X.bT),
      (¬ (KeptAll C0 CE1 CE2 X β ∧ FamOK O C0 CE1 CE2 Cm X β u) → Gv = 0) ∧
      (KeptAll C0 CE1 CE2 X β → FamOK O C0 CE1 CE2 Cm X β u →
        Gv ∈ CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        ∃ F, Gv = Ξ (Θ' F) ∧ InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) -
            symFam (KK O) X.p C0 CE1 CE2 X β (s' β u)) X.c) := by
    intro β u
    by_cases hk : KeptAll C0 CE1 CE2 X β ∧ FamOK O C0 CE1 CE2 Cm X β u
    · obtain ⟨F, hF1, hF2⟩ := hSrc X W Qq O Kf ι σ jO w hS hH hc hc1 φ hφ h' Θ' hΘ' e.dual he' hsrc' hgE' β
        hk.1 (s' β u) (hmem β u hk.1 hk.2).2
      exact ⟨Ξ (Θ' F), fun hn => absurd hk hn, fun _ _ => ⟨hΞ _ _ _ hF1, F, rfl, hF2⟩⟩
    · exact ⟨0, fun _ => rfl, fun a b => absurd ⟨a, b⟩ hk⟩
  choose Fv hFv0 hFv using hF
  choose Gv hGv0 hGv using hG
  refine ⟨κ, Fv, Gv, hκ, ?_, ?_⟩
  · intro β u hu
    by_cases hk : KeptAll C0 CE1 CE2 X β
    · exact ⟨(hFv β u hk hu).1, (hGv β u hk hu).1⟩
    · rw [hFv0 β u fun hh => hk hh.1, hGv0 β u fun hh => hk hh.1]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  · intro β u β' u' hu hu' a ha
    have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
    by_cases hk : KeptAll C0 CE1 CE2 X β
    · by_cases hk' : KeptAll C0 CE1 CE2 X β'
      · obtain ⟨-, F, hF1, hF2⟩ := hFv β u hk hu
        obtain ⟨-, F', hF1', hF2'⟩ := hGv β' u' hk' hu'
        obtain ⟨ν, hν⟩ := hform β u β' u' hk hk' hu hu' a ha _ (hPol F) _ (hPol F') hF2 hF2'
        exact ⟨ν, by rw [hF1, hF1']; exact hpair F F' _ hν⟩
      · refine ⟨0, ?_⟩
        rw [hGv0 β' u' fun hh => hk' hh.1]
        have hne : β ≠ β' := fun hh => hk' (hh ▸ hk)
        rw [if_neg hne]
        simp [beHH]
    · refine ⟨0, ?_⟩
      rw [hFv0 β u fun hh => hk hh.1]
      obtain ⟨j0, hj0⟩ := not_forall.1 hk
      have hu0 : u j0 = 0 := famOK_zero hu hj0
      have ha0 : a j0 = 0 := by
        have := ha j0
        rw [hu0, segForm_zero_left] at this
        exact hinj (by rw [← this, map_zero])
      have hprod : ∏ j, a j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) ha0
      rw [hprod]
      simp [beHH]

theorem paired_lifts_of_identity (hW : WittIdent) (hRT : RestRawTail1) (hForm : RestForm) : RestPairLift := by
  have hAll := TransportedAlt.and (TransportedAlt.and (TransportedAlt.and hRT restKeptBL) hForm) thr_std
  refine TransportedAlt.mono ?_ hAll
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨hR, hK⟩, hF⟩, -, hstd⟩
  refine ⟨30, by norm_num, fun Ct hCt => ?_⟩
  exact paired_lift_at_of_identity hW testFlatAt1
    (srcHalf1_of (le_refl 13) hCt hstd (lemma44_identity_of_raw_tail hR hK) monoAt planeAt (symIntAt C0 CE1 CE2)) hF

end Formalism.MainNotions.ColumnSystems.Pf
