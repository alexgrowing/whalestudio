import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcBasic
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

namespace A1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_add' {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    cmpD W T (x + y) = cmpD W T x + cmpD W T y := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).add_mem hx hy)]
  rw [← map_add]
  rfl

theorem cmpD_sum' {ι : Type} (s : Finset ι) (y : ι → W.DD T) (hy : ∀ k ∈ s, y k ∈ W.N T) :
    cmpD W T (∑ k ∈ s, y k) = ∑ k ∈ s, cmpD W T (y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact map_zero (W.cmp T)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cmpD_add' W T (hy a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun k hk => hy k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hy k (Finset.mem_insert_of_mem hk)]

theorem cmpD_smul_letter' (i : ZMod n) (a : LetA O n) {w : W.DD T} (hw : w ∈ W.N T)
    (hwi : (letE i : LetA O n) • w = w) :
    cmpD W T (a • w) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem a hw)]
  exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i a w hw hwi

end A1

theorem arc_single_type_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hone : ∀ s < (arcOf b w S η up size).len c, up (c - (s : ZMod n)) = up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  have hbas := arcBasic W F hB
  dsimp only at hbas
  obtain ⟨hOK, -, -, -, hσ⟩ := hbas
  have hl : 5 ≤ PD.p := by have := hB.1; omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    by_cases h : up (c - (s : ZMod n)) = true <;> simp [arcOf, h, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
  refine ⟨rr + (arcOf b w S η up size).σ PD.p, by push_cast; linarith, ?_⟩
  cases hup : up c
  ·
    have hdn : ∀ s < (arcOf b w S η up size).len c,
        (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n))) := by
      intro s hs
      have h1 : up (c - (s : ZMod n)) = false := (hone s hs).trans hup
      simp [arcOf, h1]
    have hnn : nnDen W (arcOf b w S η up size) c = 1 := by
      unfold nnDen prodTy
      apply Finset.prod_eq_one
      intro s hs
      rw [hdn s (Finset.mem_range.1 hs)]
      simp
    have hcut' : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) ∈ (arcOf b w S η up size).cuts :=
      (hOK.2.2.1 c hc).2.2.1
    obtain ⟨d₁, b₁, sol₁, hb₁⟩ :=
      hHF hcase hl _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
    obtain ⟨x₁, hx₁, hx₁eq⟩ := hArcL hcase T₁ T₂ F hsur _ rr ((arcOf b w S η up size).len c)
      (hkill _ hcut') (bb k₀) (hbb.1.1 k₀)
    obtain ⟨a, ⟨-, hxa⟩, -⟩ := hb₁.1.2 x₁ hx₁
    have hb₁N : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hb₁.1.1 m).1.1
    have hb₁l : ∀ m, (letE (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
      fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T₁ _ (hb₁.1.1 m).2
    have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) • cmpD W T₁ (b₁ m) := by
      rw [hxa, A1.cmpD_sum' W T₁ _ _ (fun m _ => (W.N T₁).smul_mem _ (hb₁N m))]
      exact Finset.sum_congr rfl fun m _ =>
        A1.cmpD_smul_letter' W T₁ _ (a m) (hb₁N m) (hb₁l m)
    have e1 : dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m => PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) =
        ((φVB PD (LL := LL) (V := T₁.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₁ x₁) := by
      rw [hcmp, map_sum]
      simp only [map_smul]
      rfl
    have e2 : dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) =
        ((φVB PD (LL := LL) (V := T₂.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₂ (bb k₀)) := by
      unfold dv
      rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (by simp)]
      simp
    have hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m =>
        PowerSeries.constantCoeff (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))))) =
        ((PD.p : LL) ^ rr) • dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
      rw [e1, e2, hx₁eq]
    refine liftsAt_thin_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hW₁ hW₂ hbb ∅ (by simp) b₁ sol₁ hb₁ _ rr (by simp) hpr f ?_ ?_ ?_
    · have h := hf.1
      rw [hnn] at h
      rw [Finset.prod_empty]
      exact h
    · intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf.2 s hs bs hbs
      rw [hnn] at hx
      exact ⟨κ, x, by rw [Finset.prod_empty]; exact hx⟩
    · intro s hs _ bs hbs
      rw [hdn s hs] at hbs
      simp at hbs
  ·
    refine liftsAt_thick_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ f hf.1 ?_
    intro s hs bs hbs
    have h1 : up (c - (s : ZMod n)) = true := (hone s hs).trans hup
    simp [arcOf, h1] at hbs

end Formalism.MainNotions.N.FrobeniusPowerSeries
