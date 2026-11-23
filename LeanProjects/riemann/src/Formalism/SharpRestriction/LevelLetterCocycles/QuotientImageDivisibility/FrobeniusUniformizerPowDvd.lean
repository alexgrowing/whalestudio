import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Ev

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_add {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x + y) = Formalism.MainNotions.ArcLiftingSetup.cmpD W T x + Formalism.MainNotions.ArcLiftingSetup.cmpD W T y := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).add_mem hx hy)]
  rw [← map_add]
  rfl

theorem cmpD_sum {ι : Type} (s : Finset ι) (y : ι → W.DD T) (hy : ∀ k ∈ s, y k ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (∑ k ∈ s, y k) = ∑ k ∈ s, Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y k) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact map_zero (W.cmp T)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cmpD_add W T (hy a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun k hk => hy k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hy k (Finset.mem_insert_of_mem hk)]

theorem cmpD_smul_letter (i : ZMod n) (a : LetA O n) {w : W.DD T} (hw : w ∈ W.N T)
    (hwi : (letE i : LetA O n) • w = w) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (a • w) =
      algebraMap O LL (PowerSeries.constantCoeff (a i)) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem a hw)]
  exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i a w hw hwi

end Ev

section Div

variable {W : LocWach PD LL O v n}

theorem frobenius_uniformizer_pow_dvd [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {c : ZMod n} {a : LetA O n}
    (ha : a ∈ W.AΔ) (hc : (letE c : LetA O n) * a = a) (h0 : PowerSeries.constantCoeff (a c) = 0) :
    ∃ g ∈ W.AΔ, a = W.π₀ * g := by
  obtain ⟨f, hf, -⟩ := hR.2.1 a ha
  have hπc : ∀ i, PowerSeries.constantCoeff (W.π₀ i) = 0 := fun i =>
    Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
  have hsub : ∀ i, HasSubst (W.π₀ i) := fun i => HasSubst.of_constantCoeff_zero' (hπc i)
  have hfc : PowerSeries.constantCoeff (f c) = 0 := by
    rw [← Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (hπc c) (f c), ← hf c]; exact h0
  obtain ⟨g', hg'⟩ := PowerSeries.X_dvd_iff.mpr hfc
  set g : LetA O n := fun i => if i = c then subst (W.π₀ i) g' else 0 with hgdef
  have hag : a = W.π₀ * g := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.mul_apply, hgdef, if_pos rfl]
      rw [hf i, hg', subst_mul (hsub i), subst_X (hsub i)]
      simp
    · have : a i = ((letE c : LetA O n) * a) i := by rw [hc]
      rw [this]
      simp [letE, Pi.single_eq_of_ne hi, hgdef, hi]
  refine ⟨g, ?_, hag⟩
  refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (W := W) hR.1 (fun i => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
  rw [← hag]; exact ha

end Div

section Ker

theorem letE_sq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_osmul (o : O) {w : W.DD T} (hw : w ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (o • w) = algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw]
  have h2 : o • w ∈ W.N T := by
    rw [← algebraMap_smul (LetA O n) o w]; exact (W.N T).smul_mem _ hw
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T h2]
  have e : (⟨o • w, h2⟩ : ↥(W.N T)) = o • (⟨w, hw⟩ : ↥(W.N T)) := rfl
  rw [e, W.cmp_smul]

theorem ker_NDl [IsDomain O] (c : ZMod n) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {x : W.DD T}
    (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T c) (h0 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T x = 0) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 x := by
  have hx' : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x := hx
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T c hmod
  have hxi : Formalism.MainNotions.LiftingTheory.InNΔi W T c x :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T c ⟨hx'.1, hx'.2.2⟩ hx'.2.1
  obtain ⟨a, ⟨ha, hxa⟩, -⟩ := hb.2 x hxi
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE c : LetA O n) • b k = b k := fun k =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c (hb.1 k).2
  have hsum : ∑ k, algebraMap O LL (PowerSeries.constantCoeff ((a k) c)) •
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) = 0 := by
    rw [← h0, hxa, cmpD_sum W T _ _ (fun k _ => (W.N T).smul_mem _ (hbN k))]
    exact Finset.sum_congr rfl fun k _ => (cmpD_smul_letter W T c (a k) (hbN k) (hbl k)).symm
  have hcc := Formalism.MainNotions.UnusedSlot80.ArcF.cmp_indepO W T h3 hmod c b hb _ hsum
  choose g hgΔ hg using fun k => frobenius_uniformizer_pow_dvd hR (ha k).1 (ha k).2 (hcc k)
  refine ⟨∑ k, g k • b k, Submodule.sum_mem _ fun k _ => (W.N T).smul_mem _ (hbN k),
    fun δ hδ => ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun k _ =>
      (Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T (hgΔ k) (hb.1 k).1).2 δ hδ
  · rw [pow_one, hxa, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hg k, mul_smul]

theorem cmpD_mem_NDl (i : ZMod n) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {x : W.DD T}
    (hx : x ∈ W.N T) (hxi : (letE i : LetA O n) • x = x) :
    ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i, Formalism.MainNotions.ArcLiftingSetup.cmpD W T x = Formalism.MainNotions.ArcLiftingSetup.cmpD W T y := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hmod
  obtain ⟨a, ha, -⟩ := huniq x hx
  have hE := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i
  set b' : Fin r → W.DD T := fun j => (letE i : LetA O n) • b j with hb'
  have hb'Δ : ∀ j, b' j ∈ W.NΔ T := fun j => Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hE (hb j)
  have hb'l : ∀ j, (letE i : LetA O n) • b' j = b' j := fun j => by
    simp only [hb', smul_smul, letE_sq]
  have hxs : x = ∑ j, a j • b' j := by
    conv_lhs => rw [← hxi, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hb', smul_smul, mul_comm]
  set y : W.DD T := ∑ j, (PowerSeries.constantCoeff ((a j) i)) • b' j with hy
  have hyN : ∀ j, (PowerSeries.constantCoeff ((a j) i)) • b' j ∈ W.N T := fun j => by
    rw [← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ (hb'Δ j).1
  refine ⟨y, ⟨Submodule.sum_mem _ fun j _ => hyN j, ?_, ?_⟩, ?_⟩
  · rw [hy, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_comm, hb'l j]
  · intro δ hδ
    rw [hy, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, (hb'Δ j).2 δ hδ]
  · rw [hxs, cmpD_sum W T _ _ (fun j _ => (W.N T).smul_mem _ (hb'Δ j).1), hy,
      cmpD_sum W T _ _ (fun j _ => hyN j)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [cmpD_smul_letter W T i (a j) (hb'Δ j).1 (hb'l j), cmpD_osmul W T _ (hb'Δ j).1]

end Ker

end Formalism.MainNotions.N.Pv.LocalLengthBound
