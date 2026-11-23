import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module Formalism.MainNotions.UnusedSlot80

section SecMap

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def InPi0Lattice (T : LocLat G Qp LL O) (c : ZMod n) (x : W.DD T) : Prop :=
  ∃ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c x' ∧ x = W.π₀ • x'

theorem inPi0Lattice_sub (T : LocLat G Qp LL O) (c : ZMod n) {x y : W.DD T}
    (hx : InPi0Lattice W T c x) (hy : InPi0Lattice W T c y) : InPi0Lattice W T c (x - y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' - y', Relay2.InNΔi_sub W T c hx' hy', (smul_sub _ _ _).symm⟩

theorem inPi0Lattice_add (T : LocLat G Qp LL O) (c : ZMod n) {x y : W.DD T}
    (hx : InPi0Lattice W T c x) (hy : InPi0Lattice W T c y) : InPi0Lattice W T c (x + y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' + y', Relay2.InNΔi_add W T c hx' hy', (smul_add _ _ _).symm⟩

theorem inPi0Lattice_smul_invariant (T : LocLat G Qp LL O) (c : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ)
    {x : W.DD T} (hx : InPi0Lattice W T c x) : InPi0Lattice W T c (a • x) := by
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨a • x', Relay2.InNΔi_smul W T c ha hx', smul_comm _ _ _⟩

theorem inPi0Lattice_smul_scalar (T : LocLat G Qp LL O) (c : ZMod n) (o : O)
    {x : W.DD T} (hx : InPi0Lattice W T c x) : InPi0Lattice W T c (o • x) := by
  rw [← algebraMap_smul (LetA O n) o x]
  exact inPi0Lattice_smul_invariant W T c (W.AΔ.algebraMap_mem o) hx

theorem inPi0Lattice_sum (T : LocLat G Qp LL O) (c : ZMod n) {ι : Type} (s : Finset ι)
    (f : ι → W.DD T) (hf : ∀ i ∈ s, InPi0Lattice W T c (f i)) :
    InPi0Lattice W T c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Relay2.InNΔi_zero W T c, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inPi0Lattice_add W T c (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inPi0Lattice_map {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) {x : W.DD T}
    (hx : InPi0Lattice W T c x) : InPi0Lattice W T' c (W.map F x) := by
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨W.map F x', Relay2.InNΔi_map W F hT hT' c hx', Relay2.mapA_smul W F _ _⟩

theorem frameVector_mem_lattice (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c (b j)) (y : Fin d → O) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T c (Formalism.MainNotions.LiftingTheory.vecB W T b y) :=
  Relay2.InNΔi_sum W T c _ _ fun j _ => Relay2.InNΔi_osmul W T c _ (hb j)

theorem inPi0Lattice_series_trunc (T : LocLat G Qp LL O) (c : ZMod n) (hπ : W.π₀ ∈ W.AΔ) {d : ℕ}
    (b : Fin d → W.DD T) (hb : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c (b j)) (y : ℕ → Fin d → O)
    (M : ℕ) (hM : 1 ≤ M) :
    InPi0Lattice W T c ((∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r)) -
      Formalism.MainNotions.LiftingTheory.vecB W T b (y 0)) := by
  induction M, hM using Nat.le_induction with
  | base => exact ⟨0, Relay2.InNΔi_zero W T c, by simp⟩
  | succ M hM ih =>
    obtain ⟨x', hx', hxe⟩ := ih
    refine ⟨x' + W.π₀ ^ (M - 1) • Formalism.MainNotions.LiftingTheory.vecB W T b (y M),
      Relay2.InNΔi_add W T c hx' (Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ _)
        (frameVector_mem_lattice W T c b hb (y M))), ?_⟩
    rw [Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ', Nat.sub_add_cancel hM, ← hxe]
    abel

theorem frameVector_single (T : LocLat G Qp LL O) (hinj : Function.Injective (algebraMap O LL))
    {d : ℕ} (b : Fin d → W.DD T) (m : Fin d) (κ : ℕ) (y : Fin d → O)
    (hy : ∀ j, algebraMap O LL (y j) = (PD.p : LL) ^ κ * (Pi.single m (1 : LL) : Fin d → LL) j) :
    Formalism.MainNotions.LiftingTheory.vecB W T b y = (((PD.p : ℕ) : O) ^ κ) • b m := by
  have hy' : y = Pi.single m (((PD.p : ℕ) : O) ^ κ) := by
    funext j
    apply hinj
    rw [hy j]
    by_cases h : j = m
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [Formalism.MainNotions.LiftingTheory.vecB, hy', Finset.sum_eq_single m]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem exists_l_pow_integral (hvl : v (PD.p : LL) = 1) (x : LL) : ∃ t : ℕ, ∀ t', t ≤ t' → 0 ≤ v ((PD.p : LL) ^ t' * x) := by
  by_cases hx : x = 0
  · exact ⟨0, fun t' _ => by rw [hx, mul_zero, AddValuation.map_zero]; exact le_top⟩
  · have hne : v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    refine ⟨⌈-q⌉₊, fun t' ht' => ?_⟩
    rw [AddValuation.map_mul, AddValuation.map_pow, hvl, ← hq, ← WithTop.coe_one,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have h1 := Nat.le_ceil (-q)
    have h2 : (⌈-q⌉₊ : ℚ) ≤ t' := by exact_mod_cast ht'
    rw [nsmul_eq_mul, mul_one]
    linarith

theorem frobenius_pow_mem_pullback (T : LocLat G Qp LL O) (c : ZMod n) (j k : ℕ) :
    ∀ y ∈ Pp W T c j, ((W.φD T) ^ k) y ∈ Pp W T c (k + j) := by
  refine Relay2.Pp_ind W T c j _ (by rw [map_zero]; exact (Pp W T c (k + j)).zero_mem)
    (fun x y hx hy => by rw [map_add]; exact (Pp W T c (k + j)).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Pp W T c (k + j)).neg_mem hx) ?_
  intro a ha x hx
  rw [Relay2.φpow_smul, ← Module.End.mul_apply, ← pow_add]
  exact Relay2.Pp_gen W T c (k + j) (PhiPowers.φA_pow_mem_AΔ W ha k) hx

theorem inFP_frobenius_pow (T : LocLat G Qp LL O) (c : ZMod n) (j k : ℕ) (f : LetA O n) {z : W.DD T}
    (hz : InFP W T c j f z) : InFP W T c (k + j) ((W.φA ^ k) f) (((W.φD T) ^ k) z) := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨_, frobenius_pow_mem_pullback W T c j k y hy, Relay2.φpow_smul W T k f y⟩

theorem inFP_of_mul_unit (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f u : LetA O n)
    (hu : u ∈ W.AΔ) {z : W.DD T} (hz : InFP W T c e (f * u) z) : InFP W T c e f z := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨u • y, Relay2.Pp_smul W T c e hu y hy, mul_smul _ _ _⟩

theorem smul_pow_difference_identity {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (L Λ : R)
    (X S1 S2 : M) (a b c d : ℕ) :
    L ^ (a + b) • (L ^ (c + d) • Λ • X - S2) =
      L ^ (b + d) • (L ^ a • (L ^ c • Λ • X - S1)) + L ^ a • (L ^ b • (L ^ d • S1 - S2)) := by
  module

end SecMap

section SecMapMain

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem arc_section_map (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hArc : 5 ≤ PD.p → ArcCore W) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore W := by
  intro hCA hp5 A hA c hc e hje hel T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d b sol hb
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hCA T₂ hW₂.1).1
  have hπ : W.π₀ ∈ W.AΔ := h9.1
  have hC := Relay2.ctx_of W hinj hO2 hP9 hH hTr hCA T₂ hW₂.1
  refine ⟨fun x hx => Relay2.inMultiple_map W F hW₁.1 hW₂.1 c' e 1 hx, ?_⟩

  have hFb : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' (W.map F (b₁ m)) :=
    fun m => Relay2.InNΔi_map W F hW₁.1 hW₂.1 c' (hb₁.1.1 m)
  choose β hβ using fun m => (hb.1.2 _ (hFb m)).exists
  let μ : Fin d₁ → Fin d → O := fun m k => PowerSeries.constantCoeff (β m k c')
  have hbN : ∀ k, b k ∈ W.N T₂ := fun k => (hb.1.1 k).1.1
  have hbl : ∀ k, (letE c' : LetA O n) • b k = b k := fun k => Relay2.InNΔi_letter W T₂ c' (hb.1.1 k)

  have hii : ∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ e b₁ (Pi.single m 1)) = dvO W T₂ e b (μ m) := by
    intro m
    have hb1N : b₁ m ∈ W.N T₁ := (hb₁.1.1 m).1.1
    have hx : W.map F (b₁ m) ∈ W.N T₂ := (hFb m).1.1
    have hsumN : ∑ k, β m k • b k ∈ W.N T₂ := (hβ m).2 ▸ hx
    have e1 : dv W T₁ e b₁ (Pi.single m 1) =
        ((φVB PD (LL := LL) (V := T₁.V)) ^ e) (cmpD W T₁ (b₁ m)) := by
      unfold dv
      rw [Finset.sum_eq_single m]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp
    rw [e1, ArcC.crisMap_φVB_pow, ArcF.cmpD_of_mem W T₁ hb1N]
    have h1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (W.cmp T₁ ⟨b₁ m, hb1N⟩) = W.cmp T₂ ⟨W.map F (b₁ m), hx⟩ :=
      (W.cmp_map F hW₁.1 hW₂.1 ⟨b₁ m, hb1N⟩ hx).symm
    have h2 : (⟨W.map F (b₁ m), hx⟩ : ↥(W.N T₂)) = ⟨∑ k, β m k • b k, hsumN⟩ := Subtype.ext (hβ m).2
    rw [h1, h2, ArcF.cmp_sum_letter W T₂ c' b hbN hbl (β m) hsumN, map_sum]
    unfold dvO dv
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ArcF.cmpD_of_mem W T₂ (hbN k)]
  refine ⟨μ, hii, ?_⟩

  intro x g hx hg hrep
  obtain ⟨κ, κ', Hh₁, a₁, hHh₁, ha₁, hX⟩ := hrep
  have hM1 : 1 ≤ A.M PD.p := Relay2.M_pos A PD.p
  have hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p := Relay2.arith_M PD.p A.G₀ A.h PD.hp.two_le hA.2.2.2.2.2.1

  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ (k : Fin d) (r : Fin (A.M PD.p)) (j : Fin d),
      0 ≤ v ((PD.p : LL) ^ (κ + t) * sol k r j) := by
    choose tf htf using fun (q : Fin d × Fin (A.M PD.p) × Fin d) =>
      exists_l_pow_integral (v := v) (PD := PD) W.v_l (sol q.1 q.2.1 q.2.2)
    refine ⟨∑ q, tf q, fun k r j => htf (k, r, j) _ ?_⟩
    exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (k, r, j)))
      (Nat.le_add_left _ _)
  choose y₂ hy₂ using fun (k : Fin d) (r : Fin (A.M PD.p)) (j : Fin d) => hO2 _ (ht k r j)
  let Y : Fin d → ℕ → Fin d → O := fun k r j => if h : r < A.M PD.p then y₂ k ⟨r, h⟩ j else 0
  have hY : ∀ k, ∀ r < A.M PD.p, ∀ j, algebraMap O LL (Y k r j) = (PD.p : LL) ^ (κ + t) * sol k r j := by
    intro k r hr j
    simp only [Y, dif_pos hr]
    exact hy₂ k ⟨r, hr⟩ j
  let Hh : Fin d → W.DD T₂ := fun k =>
    ∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₂ b (Y k r)
  have hHh : ∀ k, IsHorTr W T₂ b sol (A.M PD.p) (κ + t) k (Hh k) := fun k => ⟨Y k, hY k, rfl⟩

  let E : Fin d₁ → W.DD T₂ := fun m => lA W ^ t • W.map F (Hh₁ m) - ∑ k, μ m k • Hh k
  have hEsol : ∀ m, Relay2.SolOK W T₂ c' (A.M PD.p) 0 0 (E m) := by
    intro m
    obtain ⟨y₁, hy₁, hH₁⟩ := hHh₁ m

    have hy₁0 : ∀ j, algebraMap O LL (y₁ 0 j) = (PD.p : LL) ^ κ * (Pi.single m (1 : LL) : Fin d₁ → LL) j := by
      intro j; rw [hy₁ 0 hM1 j, (hb₁.2 m).2]
    have hv₁ := frameVector_single W T₁ hinj b₁ m κ (y₁ 0) hy₁0
    have hD1 : InPi0Lattice W T₁ c' (Hh₁ m - (((PD.p : ℕ) : O) ^ κ) • b₁ m) := by
      rw [hH₁, ← hv₁]; exact inPi0Lattice_series_trunc W T₁ c' hπ b₁ hb₁.1.1 y₁ _ hM1
    have hD2 : ∀ k, InPi0Lattice W T₂ c' (Hh k - (((PD.p : ℕ) : O) ^ (κ + t)) • b k) := by
      intro k
      have hyk0 : ∀ j, algebraMap O LL (Y k 0 j) = (PD.p : LL) ^ (κ + t) * (Pi.single k (1 : LL) : Fin d → LL) j := by
        intro j; rw [hY k 0 hM1 j, (hb.2 k).2]
      rw [← frameVector_single W T₂ hinj b k (κ + t) (Y k 0) hyk0]
      exact inPi0Lattice_series_trunc W T₂ c' hπ b hb.1.1 (Y k) _ hM1
    have hD3 : InPi0Lattice W T₂ c' (W.map F (b₁ m) - ∑ k, μ m k • b k) := by
      rw [(hβ m).2, ← Finset.sum_sub_distrib]
      refine inPi0Lattice_sum W T₂ c' _ _ fun k _ => ?_
      obtain ⟨a₀, tt, htt, hsplit⟩ := Formalism.MainNotions.LiftingTheory.invariants_eq_constants_add_uniformizer W h9 (β m k) ((hβ m).1 k).1
      have hμ : μ m k = a₀ c' := by
        show PowerSeries.constantCoeff (β m k c') = a₀ c'
        rw [hsplit, Pi.add_apply, Pi.mul_apply, map_add, map_mul, Formalism.MainNotions.LiftingTheory.uniformizer_constantCoeff_zero W h9 c', zero_mul,
          add_zero, PowerSeries.constantCoeff_C]
      have hCl : ((fun j => PowerSeries.C (a₀ j)) : LetA O n) * letE c' =
          algebraMap O (LetA O n) (a₀ c') * letE c' := by
        funext j
        by_cases h : j = c'
        · subst h; simp [letE]
        · simp [letE, h]
      refine ⟨tt • b k, Relay2.InNΔi_smul W T₂ c' htt (hb.1.1 k), ?_⟩
      have e1 : ((fun j => PowerSeries.C (a₀ j)) : LetA O n) • b k = a₀ c' • b k := by
        conv_lhs => rw [← hbl k]
        rw [smul_smul, hCl, ← smul_smul, hbl k, algebraMap_smul]
      rw [hsplit, add_smul, e1, hμ, mul_smul]
      abel
    refine ⟨?_, ?_⟩
    · have key : E m = lA W ^ t • (W.map F (Hh₁ m) - (((PD.p : ℕ) : O) ^ κ) • W.map F (b₁ m)) -
          ∑ k, μ m k • (Hh k - (((PD.p : ℕ) : O) ^ (κ + t)) • b k) +
          (((PD.p : ℕ) : O) ^ (κ + t)) • (W.map F (b₁ m) - ∑ k, μ m k • b k) := by
        simp only [E]
        rw [← Relay2.lsmul_eq, ← Relay2.lsmul_eq]
        simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, ← pow_add]
        rw [show t + κ = κ + t by omega]
        simp only [mul_comm (μ m _)]
        abel
      rw [key]
      refine inPi0Lattice_add W T₂ c' (inPi0Lattice_sub W T₂ c' ?_ ?_) ?_
      · exact inPi0Lattice_smul_invariant W T₂ c' (W.AΔ.pow_mem (Relay2.lA_mem W) t)
          (by have h := inPi0Lattice_map W F hW₁.1 hW₂.1 c' hD1; rwa [map_sub, ArcC.map_smulO] at h)
      · exact inPi0Lattice_sum W T₂ c' _ _ fun k _ => inPi0Lattice_smul_scalar W T₂ c' _ (hD2 k)
      · exact inPi0Lattice_smul_scalar W T₂ c' _ hD3
    · obtain ⟨x₁, hx₁, ex₁⟩ := (hb₁.2 m).1 (A.M PD.p) κ y₁ hy₁
      choose x₂ hx₂ ex₂ using fun k => (hb.2 k).1 (A.M PD.p) (κ + t) (Y k) (hY k)
      rw [← hH₁, smul_zero, sub_zero] at ex₁
      have ex₂' : ∀ k, W.γ T₂ (Hh k) - Hh k = W.π₀ ^ A.M PD.p • x₂ k := by
        intro k; have := ex₂ k; rw [smul_zero, sub_zero] at this; exact this
      refine ⟨lA W ^ t • W.map F x₁ - ∑ k, μ m k • x₂ k,
        Relay2.InNΔi_sub W T₂ c' (Relay2.InNΔi_lsmul W T₂ c' t (Relay2.InNΔi_map W F hW₁.1 hW₂.1 c' hx₁))
          (Relay2.InNΔi_sum W T₂ c' _ _ fun k _ => Relay2.InNΔi_osmul W T₂ c' _ (hx₂ k)), ?_⟩
      have hγF : W.γ T₂ (W.map F (Hh₁ m)) = W.map F (W.γ T₁ (Hh₁ m)) := (W.map_γ F W.gam _).symm
      have eγ₁ : W.γ T₁ (Hh₁ m) = Hh₁ m + W.π₀ ^ A.M PD.p • x₁ := by rw [← ex₁]; abel
      have eγ₂ : ∀ k, W.γ T₂ (Hh k) = Hh k + W.π₀ ^ A.M PD.p • x₂ k := fun k => by rw [← ex₂' k]; abel
      simp only [E, smul_zero, sub_zero, map_sub, Relay2.γ_lsmul, map_sum, map_smul, hγF, eγ₁, eγ₂,
        map_add, Relay2.mapA_smul, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      have hc1 : lA W ^ t • W.π₀ ^ A.M PD.p • W.map F x₁ = W.π₀ ^ A.M PD.p • lA W ^ t • W.map F x₁ :=
        smul_comm _ _ _
      have hc2 : ∀ k, μ m k • W.π₀ ^ A.M PD.p • x₂ k = W.π₀ ^ A.M PD.p • μ m k • x₂ k :=
        fun k => smul_comm _ _ _
      rw [hc1, Finset.sum_congr rfl fun k _ => hc2 k]
      abel

  have hzero : Relay2.SolOK W T₂ c' (A.M PD.p) 0 0 0 :=
    ⟨⟨0, Relay2.InNΔi_zero W T₂ c', (smul_zero _).symm⟩, 0, Relay2.InNΔi_zero W T₂ c', by simp⟩
  choose K hK using fun m => Relay2.solOK_cong W T₂ hC c' A.j (2 * A.G₀) (A.M PD.p) hM (hEsol m) hzero
  obtain ⟨u, hu, hφJJ⟩ := (hArc hp5 hCA hp5 A hA c hc e hje hel).1
  have hEP : ∀ m, InFP W T₂ c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e ^ 2)
      (lA W ^ K m • ((W.φD T₂) ^ e) (E m)) := by
    intro m
    have h1 := inFP_frobenius_pow W T₂ c' A.j (e - A.j) _ (hK m)
    rw [Nat.sub_add_cancel hje, hφJJ, map_zero, sub_zero, Relay2.φpow_lsmul, ← Module.End.mul_apply,
      ← pow_add, Nat.sub_add_cancel hje] at h1
    exact inFP_of_mul_unit W T₂ c' e _ u hu h1
  have hXF := Relay2.inMultiple_map W F hW₁.1 hW₂.1 c' e _ hX
  simp only [Relay2.mapA_smul, map_sub, map_sum, Relay2.map_φpow] at hXF
  have hA : ∑ m, a₁ m • ((W.φD T₂) ^ e) (E m) =
      lA W ^ t • ∑ m, a₁ m • ((W.φD T₂) ^ e) (W.map F (Hh₁ m)) -
        ∑ k, (∑ m, a₁ m * algebraMap O (LetA O n) (μ m k)) • ((W.φD T₂) ^ e) (Hh k) := by
    have h1 : ∀ m, a₁ m • ((W.φD T₂) ^ e) (E m) =
        lA W ^ t • (a₁ m • ((W.φD T₂) ^ e) (W.map F (Hh₁ m))) -
          ∑ k, (a₁ m * algebraMap O (LetA O n) (μ m k)) • ((W.φD T₂) ^ e) (Hh k) := by
      intro m
      simp only [E, map_sub, Relay2.φpow_lsmul, map_sum, map_smul, smul_sub, Finset.smul_sum]
      congr 1
      · exact smul_comm _ _ _
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← algebraMap_smul (LetA O n) (μ m k), smul_smul]
    rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul]
  refine ⟨κ + t, κ' + ∑ m, K m, Hh, fun k => ∑ m, a₁ m * algebraMap O (LetA O n) (μ m k), hHh,
    fun k => ⟨?_, ?_⟩, ?_⟩
  · exact W.AΔ.sum_mem fun m _ => W.AΔ.mul_mem (ha₁ m).1 (W.AΔ.algebraMap_mem _)
  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, (ha₁ m).2, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · have hS : ∀ m, InFP W T₂ c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e ^ 2)
        (a₁ m • (lA W ^ (∑ m, K m) • ((W.φD T₂) ^ e) (E m))) := by
      intro m
      have hle : K m ≤ ∑ m, K m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
      rw [show ∑ m, K m = (∑ m, K m - K m) + K m by omega, pow_add, mul_smul]
      exact Relay2.inMultiple_smul W T₂ c' e _ (ha₁ m).1 (Relay2.inMultiple_lA_pow_smul W T₂ c' e _ _ (hEP m))
    have h2 := Relay2.inMultiple_add W T₂ c' e _ (Relay2.inMultiple_lA_pow_smul W T₂ c' e _ ((∑ m, K m) + t) hXF)
      (Relay2.inMultiple_lA_pow_smul W T₂ c' e _ κ' (Relay2.inMultiple_sum W T₂ c' e _ Finset.univ _ fun m _ => hS m))
    convert h2 using 1
    have hB : ∑ m, a₁ m • (lA W ^ (∑ m, K m) • ((W.φD T₂) ^ e) (E m)) =
        lA W ^ (∑ m, K m) • ∑ m, a₁ m • ((W.φD T₂) ^ e) (E m) := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun m _ => smul_comm _ _ _
    rw [hB, hA]
    exact smul_pow_difference_identity (lA W) _ _ _ _ κ' (∑ m, K m) κ t

end SecMapMain

end Formalism.MainNotions.N.Ln17
