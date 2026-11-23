import Formalism.SharpRestriction.LevelLetterCocycles.LetterPull
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

theorem intA_inFr {a : ZMod n} {Λ : LetA O n} (hΛ : Λ ∈ W.AΔ) {g : W.EE} (h : IntA W a g) : InFr W a 1 Λ g := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨Λ * u, W.AΔ.mul_mem hΛ hu, ?_⟩
  rw [← map_mul]
  congr 1
  ring

theorem intA_add {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g + g') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  exact ⟨u + u', W.AΔ.add_mem hu hu', by rw [← map_add, mul_add]⟩

theorem intA_neg {a : ZMod n} {g : W.EE} (h : IntA W a g) : IntA W a (-g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨-u, W.AΔ.neg_mem hu, by rw [← map_neg, mul_neg]⟩

theorem intA_sub {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g - g') := by
  rw [sub_eq_add_neg]; exact intA_add W h (intA_neg W h')

theorem intA_zero {a : ZMod n} : IntA W a 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

theorem intA_mul {a : ZMod n} {g : W.EE} (h : IntA W a g) {c : LetA O n} (hc : c ∈ W.AΔ) :
    IntA W a (algebraMap (LetA O n) W.EE c * g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨c * u, W.AΔ.mul_mem hc hu, by rw [← map_mul]; congr 1; ring⟩

theorem intA_omul {a : ZMod n} {g : W.EE} (h : IntA W a g) (o : O) : IntA W a (g * algebraMap O W.EE o) := by
  rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  exact intA_mul W h (W.AΔ.algebraMap_mem o)

theorem intA_sum {a : ZMod n} {ι₀ : Type} (s : Finset ι₀) (g : ι₀ → W.EE) (h : ∀ i ∈ s, IntA W a (g i)) :
    IntA W a (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intA_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact intA_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intA_lE [NeZero n] {a : ZMod n} {g : W.EE} (h : IntA W a g) (t : ℕ) : IntA W a (lE W t * g) := by
  rw [LevC.lE_eq]; exact intA_mul W h (LevC.lA_mem W t)

theorem intA_of_inFr {a : ZMod n} {N : LetA O n} (hN : N ∈ W.AΔ) {g : W.EE} (h : InFr W a N 1 g) : IntA W a g := by
  obtain ⟨u, hu, hg⟩ := h
  refine ⟨N * u, W.AΔ.mul_mem hN hu, ?_⟩
  rw [map_one, one_mul] at hg
  rw [hg, mul_assoc]

variable [NeZero n]

theorem intA_of_nonpol (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {g : W.EE}
    (hα : ∀ s < e, 0 ≤ α s) (h : InId W a e α g) : IntA W a g := by
  have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat = 1 := by
    refine Finset.prod_eq_one fun s hs => ?_
    have : (-(α s)).toNat = 0 := by have := hα s (Finset.mem_range.1 hs); omega
    rw [this, pow_zero]
  unfold InId at h
  rw [hden] at h
  exact intA_of_inFr W (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _) h

theorem polar_core [FiniteDimensional Qp LL] (C : LevC.Ctx W) (h9 : DcrisExactStrict PD LL)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ) (a : ZMod n)
    (hac : c' + (e : ZMod n) = a)
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hT₂ : Win W A T₂) (hWY : Win W A Y) (hses : IsSESLat (Qp := Qp) ι π)
    {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    {dY : ℕ} (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (hNY : ∀ x, InFNc W Y a 1 x → ∃ f, InNL W Y a e (abelian₂ W A a e) bY f ∧
      RepVV W Y c' e (A.M PD.p) (abelian₂ W A a e) bY solY (lA W ^ A.σ PD.p • x) f)
    (w : W.DD T₂) (p x : W.DD Y) (hw : InFP W T₂ c' e 1 (abelian₂ W A a e • w)) (hp : p ∈ Pp W Y c' e)
    (hxN : InFNc W Y a 1 x) (hpx : W.map ι w = p - x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T₂ c' e (A.M PD.p) (abelian₂ W A a e) b sol (lA W ^ κ • w) f ∧
      SecIn W a e (LevC.condPolar (W := W) T₂ a e b) f := by
  have h2 := hT₂.1
  have hY := hWY.1
  set M : ℕ := A.M PD.p with hM
  set σ : ℕ := A.σ PD.p with hσ
  set Λ : LetA O n := abelian₂ W A a e with hΛ
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W C.hR.1 s) _

  obtain ⟨κ₁, F, hF, hFr⟩ := LevC.secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T₂ h2 b sol hb w
    (by rw [hac]; exact hw)
  rw [hac] at hF hFr

  choose mo hmo hmox hE using fun k => frame_const W C.hR ι h2 hY c' b hb.1 bY hbY.1 k
  set o : Fin d → Fin dY → O := fun k j => PowerSeries.constantCoeff (mo k j c') with ho
  have hFY := repVV_map W C ι h2 hY A hA a c' e b sol hb bY solY hbY o hE hF
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul] at hFY
  have hdv : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1) := fun k =>
    dv_map W ι h2 hY c' e b hb.1 bY hbY.1 k (mo k) (hmox k)

  obtain ⟨κp, G, hG, hGint⟩ := secOfP_int W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e Y hY bY solY hbY p
    ⟨p, hp, (one_smul _ _).symm⟩
  rw [hac] at hG hGint
  obtain ⟨fx, ⟨hfxr, κx, hSx⟩, hRx⟩ := hNY x hxN

  have R1 := LevC.repVV_lA Y c' e M Λ bY solY (W.map ι w) _ (κp + σ) κ₁ hFY
  have R2 := LevC.repVV_lA Y c' e M Λ bY solY p G (κ₁ + σ) κp hG
  have R3 := LevC.repVV_lA Y c' e M Λ bY solY x fx (κ₁ + κp) σ hRx
  rw [show κp + (κ₁ + σ) = κ₁ + (κp + σ) by omega] at R2
  rw [show σ + (κ₁ + κp) = κ₁ + (κp + σ) by omega] at R3
  have R23 := LevC.repVV_sub W C.hinj Y c' e M Λ bY solY _ _ _ _ R2 R3
  rw [← smul_sub, ← hpx] at R23
  have hfr1 : ∀ j, InFr W a 1 Λ (lE W (κp + σ) * ∑ k, F k * algebraMap O W.EE (o k j)) := fun j =>
    Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (LevC.inFr_sum W _ _ fun k _ => by
      rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      exact LevC.inFr_mulA W (hFr k) (W.AΔ.algebraMap_mem _)) _
  have hfr23 : ∀ j, InFr W a 1 Λ (lE W (κ₁ + σ) * G j - lE W (κ₁ + κp) * fx j) := fun j =>
    LevC.inFr_sub W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (intA_inFr W hΛm (hGint j)) _)
      (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfxr j) _)
  obtain ⟨t, ht⟩ := LevC.sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p Y
    (C.h3 Y hY) (C.hmod Y hY) A hA c' hc' hWY bY solY hbY e _ _ _ (by rw [hac]; exact R1) (by rw [hac]; exact R23)
    (by rw [hac]; exact hfr1) (by rw [hac]; exact hfr23)
  rw [hac] at ht
  choose u hu hue using ht
  simp only [map_one, one_mul, Pi.sub_apply] at hue
  set ε : Fin dY → W.EE := fun j => algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) with hεdef
  have hε : ∀ j, IntA W a (ε j) := fun j =>
    ⟨W.π₀ * Λ * u j, W.AΔ.mul_mem (W.AΔ.mul_mem C.hR.1 hΛm) (hu j), by
      show algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) = _
      congr 1
      ring⟩
  obtain ⟨I, g, cc, α, hgα, hfx⟩ := hSx

  have hpv : ∀ i, ∃ (m : ℕ) (r : Fin d → O), (∃ s < e, α i s < 0) →
      (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cc i j) ∧
        ∀ s < e, α i s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α i s)) := by
    intro i
    by_cases hi : ∃ s < e, α i s < 0
    · obtain ⟨m, r, h⟩ := pull_vec W C.hbij h9 C.hV C.hinj T₂ Y ι π hses h2 hY a e b bY hspan2 hindY hspanY o hdv
        (α i) (cc i) (hgα i).2 hi
      exact ⟨m, r, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose mi ri hri using hpv
  set M0 : ℕ := ∑ i, mi i with hM0
  set r' : Fin I → Fin d → O := fun i k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k with hr'def
  set pol : Fin I → Prop := fun i => ∃ s < e, α i s < 0 with hpol
  have hr'1 : ∀ i, pol i → ∀ j, ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
    intro i hi j
    have hle : mi i ≤ M0 := Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i)
    have h1 := (hri i hi).1 j
    calc ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ (M0 - mi i) * ∑ k, ri i k * o k j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hr'def]; ring
      _ = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
          rw [h1, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hr'2 : ∀ i, pol i → ∀ s < e, α i s < 0 → dvO W T₂ e b (r' i) ∈ FilS W T₂ a s (-(α i s)) := by
    intro i hi s hs hneg
    rw [show r' i = fun k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k from rfl, dvO_smul]
    exact Submodule.smul_mem _ _ ((hri i hi).2 s hs hneg)

  set Spol : Fin dY → W.EE := fun j => ∑ i, if pol i then g i * algebraMap O W.EE (cc i j) else 0 with hSpol
  set Snp : Fin dY → W.EE := fun j => ∑ i, if pol i then 0 else g i * algebraMap O W.EE (cc i j) with hSnpdef
  have hsplit : ∀ j, lE W κx * fx j = Spol j + Snp j := fun j => by
    have hfxj : lE W κx * fx j = ∑ i, g i * algebraMap O W.EE (cc i j) := hfx j
    rw [hfxj, hSpol, hSnpdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hSnp : ∀ j, IntA W a (Snp j) := fun j => intA_sum W _ _ fun i _ => by
    by_cases hi : pol i
    · rw [if_pos hi]; exact intA_zero W
    · rw [if_neg hi]
      refine intA_omul W (intA_of_nonpol W C.hR.1 (fun s hs => ?_) (hgα i).1) _
      by_contra hlt
      exact hi ⟨s, hs, not_le.mp hlt⟩
  set Pv : Fin d → W.EE := fun k => ∑ i, if pol i then g i * algebraMap O W.EE (r' i k) else 0 with hPvdef
  have hPv : ∀ j, ∑ k, Pv k * algebraMap O W.EE (o k j) = lE W M0 * Spol j := fun j => by
    simp only [hPvdef, hSpol, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : pol i
    · simp only [if_pos hi]
      have h3 : ∑ k, g i * algebraMap O W.EE (r' i k) * algebraMap O W.EE (o k j) =
          g i * algebraMap O W.EE (∑ k, r' i k * o k j) := by
        rw [map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp only [map_mul]; ring
      rw [h3, hr'1 i hi j]
      simp only [map_mul, map_pow, map_natCast]
      unfold lE
      ring
    · simp only [if_neg hi, zero_mul, Finset.sum_const_zero, mul_zero]
  set Mt : ℕ := M0 + κx + t + κp + σ with hMt
  set Z : Fin d → W.EE := fun k => lE W Mt * F k + lE W (t + κ₁ + κp) * Pv k with hZdef
  set R : Fin dY → W.EE := fun j => lE W M0 * (lE W (κx + t + κ₁ + σ) * G j + lE W κx * ε j -
    lE W (t + κ₁ + κp) * Snp j) with hRdef
  have hZR : ∀ j, ∑ k, Z k * algebraMap O W.EE (o k j) = R j := fun j => by
    have e1 : ∑ k, Z k * algebraMap O W.EE (o k j) = lE W Mt * ∑ k, F k * algebraMap O W.EE (o k j) +
        lE W (t + κ₁ + κp) * ∑ k, Pv k * algebraMap O W.EE (o k j) := by
      simp only [hZdef, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [e1, hPv j]
    have h1 := hue j
    have h2 := hsplit j
    simp only [hRdef, hMt, lE] at h1 h2 ⊢
    linear_combination (((PD.p : ℕ) : W.EE) ^ (M0 + κx)) * h1 - (((PD.p : ℕ) : W.EE) ^ (M0 + t + κ₁ + κp)) * h2

  obtain ⟨q, D, hD⟩ := right_inv W C.hV C.hinj o
    (o_inj W C.hbij h9 T₂ Y ι π hses h2 hY a e b bY hind2 hspan2 hindY o hdv)
  have hZq : ∀ m, lE W q * Z m = ∑ j, R j * algebraMap O W.EE (D j m) := fun m => by
    have e2 : ∑ j, R j * algebraMap O W.EE (D j m) = ∑ k, Z k * algebraMap O W.EE (∑ j, o k j * D j m) := by
      simp only [← hZR, Finset.sum_mul, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by simp only [map_mul]; ring
    rw [e2]
    simp only [hD, apply_ite (algebraMap O W.EE), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_pow, map_natCast]
    unfold lE
    ring
  have hInt : ∀ m, IntA W a (∑ j, R j * algebraMap O W.EE (D j m)) := fun m =>
    intA_sum W _ _ fun j _ => intA_omul W (intA_lE W (intA_sub W (intA_add W (intA_lE W (hGint j) _)
      (intA_lE W (hε j) _)) (intA_lE W (hSnp j) _)) _) _
  set cp : Fin I → Fin d → O := fun i k =>
    if pol i then -(((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp)) * r' i k) else 0 with hcpdef
  have hfin : ∀ m, lE W (q + Mt) * F m =
      (∑ j, R j * algebraMap O W.EE (D j m)) + ∑ i, g i * algebraMap O W.EE (cp i m) := fun m => by
    rw [← hZq m]
    have e3 : ∑ i, g i * algebraMap O W.EE (cp i m) = -(lE W (q + (t + κ₁ + κp)) * Pv m) := by
      rw [hPvdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : pol i
      · simp only [hcpdef, if_pos hi, map_neg, map_mul, map_pow, map_natCast]
        unfold lE
        ring
      · simp only [hcpdef, if_neg hi, map_zero, mul_zero, neg_zero]
    rw [e3, hZdef]
    simp only [hMt]
    unfold lE
    ring
  refine ⟨κ₁ + (q + Mt), fun m => lE W (q + Mt) * F m, LevC.repVV_lA T₂ c' e M Λ b sol w F (q + Mt) κ₁ hF, ?_⟩
  have hS1 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ j, R j * algebraMap O W.EE (D j m)) := by
    refine ⟨d, fun m₀ => ∑ j, R j * algebraMap O W.EE (D j m₀), fun m₀ => Pi.single m₀ 1, fun _ _ => 0,
      fun m₀ => ⟨?_, fun s _ => Or.inl le_rfl⟩, fun k => ?_⟩
    · obtain ⟨uu, huu, hug⟩ := hInt m₀
      show InFr W a (∏ s ∈ Finset.range e, ps W s ^ ((0 : ℤ)).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(0 : ℤ)).toNat) _
      simp only [neg_zero, Int.toNat_zero, pow_zero, Finset.prod_const_one]
      exact ⟨uu, huu, by rw [map_one, one_mul, hug, mul_one]⟩
    · simp [Pi.single_apply]
  have hS2 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ i, g i * algebraMap O W.EE (cp i m)) := by
    refine ⟨I, g, cp, α, fun i => ⟨(hgα i).1, fun s hs => ?_⟩, fun k => rfl⟩
    by_cases hneg : α i s < 0
    · right
      have hi : pol i := ⟨s, hs, hneg⟩
      have e4 : cp i = fun k => (-((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp))) * r' i k := by
        funext k; simp only [hcpdef, if_pos hi]; ring
      rw [e4, dvO_smul]
      exact Submodule.smul_mem _ _ (hr'2 i hi s hs hneg)
    · left
      exact not_lt.mp hneg
  have hS := LevC.secIn_add W hS1 hS2
  convert hS using 1
  funext m
  rw [Pi.add_apply]
  exact hfin m

end Formalism.MainNotions.UnusedSlot80.SplitP
