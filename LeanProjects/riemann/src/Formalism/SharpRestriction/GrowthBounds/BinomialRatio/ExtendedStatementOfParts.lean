import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds
import Formalism.PolynomialDimension.MultinomialKLog

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

abbrev Lj (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc)
    [NeZero X.m] (j : Fin (numSeg X.TT)) : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) :=
  segLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm)

abbrev rkj (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc)
    [NeZero X.m] (j : Fin (numSeg X.TT)) : ℕ :=
  segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm)

def RkAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ j, Module.finrank O (Lj O C0 CE1 CE2 Cm X j) = rkj O C0 CE1 CE2 Cm X j

def BlockDiag {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {r s t : ℕ}
    (form : SegVs O r s t → SegVs O r s t → KK O) (L : Submodule O (SegVs O r s t)) (g : ℕ) (D : ℝ) : Prop :=
  ∃ (x y : Fin g → SegVs O r s t) (β : Fin g → SegBlock s r) (z : Fin g → O),
    (∀ i, x i ∈ L ∧ y i ∈ L) ∧ (∀ i b, b ≠ β i → x i b = 0 ∧ y i b = 0) ∧ (∀ i, z i ≠ 0 ∧ vLEO p (z i) D) ∧
      ∀ i l, form (x i) (y l) = if i = l then algebraMap O (KK O) (z i) else 0

def PartnersToFactorsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (Module.finrank O L₁) Dj

def LiftAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (Dj : Fin (numSeg X.TT) → ℝ) (g : Fin (numSeg X.TT) → ℕ), (∀ j, 0 ≤ Dj j) →
    (∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (g j) (Dj j)) →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      FactorsLE X.p (beHH (m := X.m) X.p X.TT X.aT X.bT)
        (CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) (CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e)
        (∏ j, g j) ((∑ j, Dj j) + 4 * X.kap0)

def LiftVecAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (Dj : Fin (numSeg X.TT) → ℝ) (g : Fin (numSeg X.TT) → ℕ), (∀ j, 0 ≤ Dj j) →
    (∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (g j) (Dj j)) →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      ∃ (F : (∀ j, Fin (g j)) → VHH (m := X.m) Kf X.TT X.aT X.bT)
        (G : (∀ j, Fin (g j)) → Module.Dual Kf (VHH (m := X.m) Kf X.TT X.aT X.bT)) (δ : (∀ j, Fin (g j)) → O),
        (∀ I, F I ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        (∀ I, G I ∈ CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        (∀ I, δ I ≠ 0 ∧ vLEO X.p (δ I) ((∑ j, Dj j) + 4 * X.kap0)) ∧
        ∀ I J, ∃ ν : O, beHH (m := X.m) X.p X.TT X.aT X.bT (F I) (G J) =
          algebraMap O Kf ((if I = J then δ I else 0) + w ^ X.c * ν)

theorem kapP_nonneg {C0 Cde CE1 CE2 Cm Ckap H : ℝ} {X : Loc} (h : Std C0 Cde CE1 CE2 H X) (hCm : 0 ≤ Cm)
    (hCk : 0 ≤ Ckap) : 0 ≤ X.kapP C0 CE1 CE2 Cm Ckap := by
  have hk : 0 ≤ X.k := by unfold Loc.k; positivity
  have hQ : 0 ≤ X.Q := by unfold Loc.Q; positivity
  have hN : 0 ≤ X.N := by unfold Loc.N; positivity
  have hY : 0 ≤ X.Y := le_trans zero_le_one h.Y1
  have hm0 : 0 ≤ X.m0 Cm := by unfold Loc.m0 m0G4 m1G4; positivity
  have hE := h.E0nn
  have hb := h.bpos.le
  unfold Loc.kapP kappaMarginBound
  positivity

theorem Ne_pos {p n' k : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n') (hk : 1 ≤ k) : 0 < gaussianNumber (p ^ n') k := by
  have h1 : (1 : ℝ) < ((p ^ n' : ℕ) : ℝ) := by
    have : 1 < p ^ n' := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  unfold gaussianNumber
  apply div_pos
  · have := one_lt_pow₀ h1 (n := k) (by omega)
    linarith
  · linarith

theorem extended_statement_of_parts {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc H : ℝ} (hCm : 0 ≤ Cm) (hCk : 0 ≤ Ckap)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hRk : RkAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (hL1 : PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc)
    (hLift : LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc)
    (hA2 : ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc) :
    HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc Dj kT hDj hcD e he
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have hs := hstd X hD1 hH hc
  have hkap := kapP_nonneg hs hCm hCk
  have hm0 : 0 ≤ X.m0 Cm := by
    have hk : 0 ≤ X.k := by unfold Loc.k; positivity
    have hQ : 0 ≤ X.Q := by unfold Loc.Q; positivity
    unfold Loc.m0 m0G4 m1G4; positivity
  have hNe : 0 < gaussianNumber (X.p ^ X.n') (X.m + 1) :=
    Ne_pos (by have := hS.1.five_le; omega) (by have := hS.1.two_le; omega) (by omega)

  choose L₁ hL₁ using fun j => (hDj j).2.2
  have hF : ∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j)
      (Module.finrank O (L₁ j)) (Dj j) := fun j =>
    hL1 X W Qq O Kf ι σ jO w hS hH hc j (Dj j) (L₁ j) (hDj j).1 (hL₁ j).1
  have hT := hLift X W Qq O Kf ι σ jO w hS hH hc Dj (fun j => Module.finrank O (L₁ j)) (fun j => (hDj j).1) hF hcD e he
  refine ⟨∏ j, Module.finrank O (L₁ j), ?_, hT⟩
  have hrank := hA2 X W Qq O Kf ι σ jO w hS hH hc (X.m0 Cm) hm0
  have hg : ∀ j, (1 - kT j) * (rkj O C0 CE1 CE2 Cm X j : ℝ) ≤ (Module.finrank O (L₁ j) : ℝ) := fun j => by
    have := (hL₁ j).2
    rwa [hRk X W Qq O Kf ι σ jO w hS hH hc j] at this
  have hdim : (0 : ℝ) ≤ (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ j, kT j := Finset.sum_nonneg fun j _ => (hDj j).2.1
  rw [div_le_iff₀ hNe]
  by_cases hall : ∀ j, kT j ≤ 1
  · by_cases hs1 : ∑ j, kT j ≤ 1
    · have hsp := Formalism.CountingSumsFrames.Top.shareProd (numSeg X.TT) kT (fun j => Module.finrank O (L₁ j))
        (fun j => rkj O C0 CE1 CE2 Cm X j) (fun j => ⟨(hDj j).2.1, hall j⟩) hg
      have hrank' : (1 - X.kapP C0 CE1 CE2 Cm Ckap) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤
          gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ) := by
        push_cast
        exact hrank
      have h1 : (1 - ∑ j, kT j) * ((1 - X.kapP C0 CE1 CE2 Cm Ckap) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ)) ≤
          (1 - ∑ j, kT j) * (gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrank' (by linarith)
      have h2 : gaussianNumber (X.p ^ X.n') (X.m + 1) * ((1 - ∑ j, kT j) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ)) ≤
          gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsp hNe.le
      have h3 : 0 ≤ (∑ j, kT j) * X.kapP C0 CE1 CE2 Cm Ckap * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) := by positivity
      nlinarith [h1, h2, h3]
    · have h0 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) ≤ 0 := by linarith [not_le.mp hs1]
      have h1 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0 hdim
      have h2 : (0 : ℝ) ≤ ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) * gaussianNumber (X.p ^ X.n') (X.m + 1) := by positivity
      linarith
  · push Not at hall
    obtain ⟨j0, hj0⟩ := hall
    have hle : kT j0 ≤ ∑ j, kT j := Finset.single_le_sum (fun j _ => (hDj j).2.1) (Finset.mem_univ j0)
    have h0 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) ≤ 0 := by linarith
    have h1 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hdim
    have h2 : (0 : ℝ) ≤ ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) * gaussianNumber (X.p ^ X.n') (X.m + 1) := by positivity
    linarith

def RestRk : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => RkAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

def PartnersToFactors : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

def RestLift : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

def RestLiftVec : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

theorem thr_std : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => 0 ≤ Cm ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 h3 _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨by linarith, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem restExt_of {D : Formalism.BasicNotions.D7} (hRk : RestRk) (hL1 : PartnersToFactors) (hLift : RestLift) (hA2 : RemainderSegmentBoundSecond D) :
    RestExt D := by
  refine TransportedAlt.mono ?_ ((((thr_std.and hRk).and hL1).and hLift).and hA2)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨⟨⟨hCm, hstd⟩, rk⟩, l1⟩, ⟨Ct0, hCt0, lift⟩⟩, ⟨Ck0, hCk0, a2⟩⟩
  exact ⟨Ck0, Ct0, hCk0, hCt0, fun Ckap Ct h1 h2 =>
    extended_statement_of_parts hCm (le_trans hCk0.le h1) hstd rk l1 (lift Ct h2) (a2 Ckap h1)⟩

end Formalism.MainNotions.ColumnSystems.Pf
