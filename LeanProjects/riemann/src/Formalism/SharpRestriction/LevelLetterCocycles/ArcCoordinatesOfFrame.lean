import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.ArcC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.PhiPowers

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem chainE (hs : W.s = 1) (T : LocLat G Qp LL O) {M h : ZMod n → ℕ}
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) (E : ℕ → ℕ) (e : ℕ)
    (hM : ∀ m : ℕ, 1 ≤ m → m ≤ e → M (c + (m : ZMod n)) ≤ E m) (x : W.DD T) (hx : x ∈ W.N T)
    (hxc : (letE c : LetA O n) • x = x) :
    ∀ k, k ≤ e → (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ E (k - s)) • ((W.φD T) ^ k) x ∈ W.N T := by
  intro k
  induction k with
  | zero => intro _; simpa using hx
  | succ k ih =>
    intro hk
    set a : LetA O n := ∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ E (k - s) with ha
    have hy : a • ((W.φD T) ^ k) x ∈ W.N T := ih (by omega)
    have hlet : (letE (c + (k : ZMod n)) : LetA O n) • (a • ((W.φD T) ^ k) x) =
        a • ((W.φD T) ^ k) x := by
      rw [smul_comm, φD_pow_letter W T c x hxc k]
    have hNl : a • ((W.φD T) ^ k) x ∈ W.Nl T (c + ((k + 1 : ℕ) : ZMod n) - 1) := by
      rw [show c + ((k + 1 : ℕ) : ZMod n) - 1 = c + (k : ZMod n) by push_cast; ring]
      exact ⟨_, hy, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hlet⟩
    have h1 := h5.1 (c + ((k + 1 : ℕ) : ZMod n)) _ hNl
    have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
    rw [hQ] at h1
    have hMk := hM (k + 1) (by omega) hk
    have h2 : W.q ^ E (k + 1) • W.φD T (a • ((W.φD T) ^ k) x) ∈ W.N T := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hMk
      rw [hd, pow_add, mul_comm, mul_smul]
      exact (W.N T).smul_mem _ h1
    rw [φD_smulA, smul_smul, ← pow_apply_succ] at h2
    have e : W.q ^ E (k + 1) * W.φA a =
        ∏ s ∈ Finset.range (k + 1), ((W.φA ^ s) W.q) ^ E (k + 1 - s) := by
      rw [Finset.prod_range_succ', ha, map_prod, pow_zero, AlgHom.one_apply, Nat.sub_zero, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun s hs' => ?_
      rw [map_pow, pow_succ', AlgHom.mul_apply, show k + 1 - (s + 1) = k - s by omega]
    rw [e] at h2
    exact h2

theorem hs_ge (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e m : ℕ)
    (hm1 : 1 ≤ m) (hme : m ≤ e) :
    Mw A.G₀ A.S A.η (A.ty (c' + (m : ZMod n))) ≤ A.Hs (c' + (e : ZMod n)) e (e - m) := by
  have hlet : c' + (e : ZMod n) - ((e - m : ℕ) : ZMod n) = c' + (m : ZMod n) := by
    rw [Nat.cast_sub hme]; ring
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [hlet]
  by_cases h1 : A.ty (c' + (m : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin
  · rw [if_pos (Or.inl h1), h1]; simp [Mw]
  · by_cases h2 : e - (e - m) ≤ A.j
    · rw [if_pos (Or.inr h2)]
      exact mw_le A hA c' hc' m hm1 (by omega)
    · rw [if_neg (by tauto)]
      have hth : (A.ty (c' + (m : ZMod n))).thick := by
        revert h1; cases A.ty (c' + (m : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.thick]
      have hsz := hA.2.2.2.2.2.2.2.1 _ hth
      have hok := hA.2.2.2.2.1 (c' + (m : ZMod n))
      revert hsz hok
      cases A.ty (c' + (m : ZMod n)) with
      | thin => intro _ _; simp [Mw]; exact hA.2.2.2.2.2.1
      | up b => intro hsz hok; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hsz; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok; simp only [Mw]; omega
      | down b => intro hsz _; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hsz; simp only [Mw]; omega

theorem φpow_pk (a b : ℕ) : (W.φA ^ a) (Formalism.MainNotions.LiftingTheory.pk W b) = Formalism.MainNotions.LiftingTheory.pk W (a + b) := by
  unfold Formalism.MainNotions.LiftingTheory.pk
  rw [pow_add, AlgHom.mul_apply]

theorem pk_eq_ps (s : ℕ) : Formalism.MainNotions.LiftingTheory.pk W s = Formalism.MainNotions.ArcLiftingSetup.ps W s := rfl

theorem hs_le_h (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (a : ZMod n) (e s : ℕ) : A.Hs a e s ≤ A.h := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  split_ifs
  · exact hA.2.2.2.2.2.1
  · exact le_rfl

theorem hs_top (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (a : ZMod n) (e s : ℕ) (h : e - s ≤ A.j) : A.Hs a e s = A.G₀ := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [if_pos (Or.inr h)]

theorem two_h_lt (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (h5 : 5 ≤ PD.p) : 2 * A.h < (PD.p - 1) * A.M PD.p := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.M
  exact Nat.lt_mul_div_succ _ (by omega)

theorem arc_ring
    (hTr : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (hπ : W.π₀ ∈ W.AΔ) (h5 : 5 ≤ PD.p) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (a : ZMod n) (e : ℕ)
    (hje : A.j ≤ e) :
    ∃ u ∈ W.AΔ, (W.φA ^ (e - A.j)) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p)) =
      W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e ^ 2 * u := by
  have hlt := two_h_lt A h5
  set m := e - A.j with hm
  set M := A.M PD.p with hMdef
  obtain ⟨u, hu, u', -, -, hT⟩ := hTr m M
  have hM1 : 1 ≤ M := by simp [hMdef, Formalism.MainNotions.ArcLiftingSetup.ArcP.M]
  set R : LetA O n := ∏ s ∈ Finset.range m,
    Formalism.MainNotions.ArcLiftingSetup.ps W s ^ ((PD.p - 1) * M - 2 * A.Hs a e s) with hR
  refine ⟨u * W.π₀ ^ (M - 1) * R,
    W.AΔ.mul_mem (W.AΔ.mul_mem hu (W.AΔ.pow_mem hπ _))
      (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hπ s) _), ?_⟩
  have he : e = m + A.j := by omega
  have hJ : (W.φA ^ m) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M) =
      ((W.φA ^ m) W.π₀) ^ M * ∏ k ∈ Finset.range A.j, Formalism.MainNotions.LiftingTheory.pk W (m + k) ^ (2 * A.G₀) := by
    unfold Formalism.MainNotions.LiftingTheory.JJ
    rw [map_mul, map_pow, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun k _ => by rw [map_pow, φpow_pk]
  have hL : Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e = (∏ s ∈ Finset.range m, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.Hs a e s) *
      ∏ k ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W (m + k) ^ A.G₀ := by
    unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
    rw [he, Finset.prod_range_add, ← he]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by
      rw [hs_top A a e (m + k) (by simp at hk; omega)]
  have hA1 : ∏ s ∈ Finset.range m, Formalism.MainNotions.LiftingTheory.pk W s ^ ((PD.p - 1) * M) =
      (∏ s ∈ Finset.range m, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.Hs a e s) ^ 2 * R := by
    rw [hR, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    have := hs_le_h A hA a e s
    rw [← pow_mul, ← pow_add, pk_eq_ps]
    congr 1
    omega
  have hA2 : ∏ k ∈ Finset.range A.j, Formalism.MainNotions.LiftingTheory.pk W (m + k) ^ (2 * A.G₀) =
      (∏ k ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W (m + k) ^ A.G₀) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_mul, pk_eq_ps, mul_comm]
  rw [hJ, hT, hL, hA1, hA2]
  have hpM : W.π₀ ^ M = W.π₀ * W.π₀ ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM1]
  rw [hpM]
  ring

theorem prod_q_eqE (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (k : ℕ) (E : ℕ → ℕ) :
    ∃ u : LetA O n, IsUnit u ∧ ∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ E s =
      u * ∏ s ∈ Finset.range k, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ E s := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_eq] at hw
  refine ⟨∏ s ∈ Finset.range k, ((W.φA ^ s) (w : LetA O n)) ^ E s, ?_, ?_⟩
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      fun s _ => ((w.isUnit.map (W.φA ^ s)).pow (E s))
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← mul_pow, hw, map_mul]
    rfl

theorem lam_mem_AΔ (hπ : W.π₀ ∈ W.AΔ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (a : ZMod n) (e : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e ∈ W.AΔ :=
  W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hπ s) _

theorem lam_phi_mem (hs : W.s = 1) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (T : LocLat G Qp LL O)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun i => Mw A.G₀ A.S A.η (A.ty i)) (fun i => Hw A.G₀ A.S A.η (A.ty i)))
    (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ) (x : W.DD T) (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c' x) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) x ∈ W.NΔ T ∧
      (letE (c' + (e : ZMod n)) : LetA O n) •
        (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) x) =
        Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) x := by
  obtain ⟨⟨hxN, hxΔ⟩, ⟨y, hyN, hyx⟩⟩ := hx
  have hxc : (letE c' : LetA O n) • x = x := by
    rw [← hyx, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]
  set a : ZMod n := c' + (e : ZMod n)
  have h1 := chainE W hs T h5 c' (fun m => A.Hs a e (e - m)) e
    (fun m hm1 hme => hs_ge A hA c' hc' e m hm1 hme) x hxN hxc e le_rfl
  have he : ∏ s ∈ Finset.range e, ((W.φA ^ s) W.q) ^ (A.Hs a e (e - (e - s))) =
      ∏ s ∈ Finset.range e, ((W.φA ^ s) W.q) ^ (A.Hs a e s) :=
    Finset.prod_congr rfl fun s hs' => by
      rw [Nat.sub_sub_self (Finset.mem_range.1 hs').le]
  rw [he] at h1
  obtain ⟨u, hu, hue⟩ := prod_q_eqE W hR e (fun s => A.Hs a e s)
  rw [hue, mul_smul] at h1
  have hN : Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e • ((W.φD T) ^ e) x ∈ W.N T := by
    obtain ⟨u', hu'⟩ := hu.exists_left_inv
    have := (W.N T).smul_mem u' h1
    rwa [smul_smul, hu', one_smul] at this
  have hP := lam_mem_AΔ W hR.1 A a e
  refine ⟨⟨hN, fun δ hδ => ?_⟩, ?_⟩
  · rw [γD_smulA, hP δ hδ, φD_pow_Δ W T hxΔ e δ hδ]
  · rw [smul_comm, φD_pow_letter W T c' x hxc e]

theorem arc_up (hs : W.s = 1) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ)
    (T : LocLat G Qp LL O) (hT : Formalism.MainNotions.ArcLiftingSetup.Win W A T) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c' e,
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • y) := by
  set P : LetA O n := Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e with hPdef
  have h5T := h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have hP : P ∈ W.AΔ := lam_mem_AΔ W hR.1 A _ e
  let S : AddSubgroup (W.DD T) :=
    { carrier := {y | P • y ∈ W.NΔ T ∧ (letE (c' + (e : ZMod n)) : LetA O n) • (P • y) = P • y}
      add_mem' := fun {a b} ha hb => ⟨by rw [smul_add]; exact (W.NΔ T).add_mem ha.1 hb.1,
        by rw [smul_add, smul_add, ha.2, hb.2]⟩
      zero_mem' := ⟨by rw [smul_zero]; exact (W.NΔ T).zero_mem, by rw [smul_zero, smul_zero]⟩
      neg_mem' := fun {a} ha => ⟨by rw [smul_neg]; exact (W.NΔ T).neg_mem ha.1,
        by rw [smul_neg, smul_neg, ha.2]⟩ }
  have hgen : {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c' x ∧ z = a • ((W.φD T) ^ e) x} ⊆
      (S : Set (W.DD T)) := by
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := lam_phi_mem W hs hR T A hA h5T c' hc' e x hx
    refine ⟨?_, ?_⟩
    · rw [smul_comm]; exact smul_mem_NΔ W T ha h1
    · rw [smul_comm P a, smul_comm _ a, h2]
  intro y hy
  obtain ⟨hy1, hy2⟩ := (AddSubgroup.closure_le S).2 hgen hy
  exact ⟨P • y, hy1, hy2, (one_smul _ _).symm⟩

theorem hw_le_hs (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e s : ℕ)
    (hse : s < e) :
    Hw A.G₀ A.S A.η (A.ty (c' + (e : ZMod n) - (s : ZMod n))) ≤ A.Hs (c' + (e : ZMod n)) e s := by
  have hlet : c' + (e : ZMod n) - (s : ZMod n) = c' + ((e - s : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hse.le]; ring
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [hlet]
  by_cases h1 : A.ty (c' + ((e - s : ℕ) : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin
  · rw [if_pos (Or.inl h1), h1]; simp [Hw]
  · by_cases h2 : e - s ≤ A.j
    · rw [if_pos (Or.inr h2)]
      rcases hA.2.2.2.2.2.2.2.2 with h | ⟨hj, hth, hsz⟩
      · rw [h c' hc' (e - s) (by omega) h2]; simp [Hw]
      · have hk : e - s = 1 := by omega
        rw [hk] at h1 ⊢
        have hsz1 := hsz c' hc'
        have hok := hA.2.2.2.2.1 (c' + 1)
        simp only [Nat.cast_one] at h1 ⊢
        revert hsz1 hok
        cases A.ty (c' + 1) with
        | thin => intro _ _; simp [Hw]
        | up b => intro hs hok; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hs; simp only [Hw]; omega
        | down b => intro hs hok; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hs
                    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok; simp only [Hw]; omega
    · rw [if_neg (by tauto)]
      have hth : (A.ty (c' + ((e - s : ℕ) : ZMod n))).thick := by
        revert h1; cases A.ty (c' + ((e - s : ℕ) : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.thick]
      have hsz := hA.2.2.2.2.2.2.2.1 _ hth
      have hok := hA.2.2.2.2.1 (c' + ((e - s : ℕ) : ZMod n))
      revert hsz hok
      cases A.ty (c' + ((e - s : ℕ) : ZMod n)) with
      | thin => intro _ _; simp [Hw]; exact hA.2.2.2.2.2.1
      | up b => intro hsz _; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hsz; simp only [Hw]; omega
      | down b => intro hsz hok; simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at hsz
                  simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok; simp only [Hw]; omega

theorem φpow_span (T : LocLat G Qp LL O) (S : Set (W.DD T)) (k : ℕ) (z : W.DD T)
    (hz : z ∈ Submodule.span (LetA O n) (W.φD T '' S)) :
    ((W.φD T) ^ k) z ∈ Submodule.span (LetA O n) (((W.φD T) ^ (k + 1)) '' S) := by
  let U : Submodule (LetA O n) (W.DD T) :=
    { carrier := {z | ((W.φD T) ^ k) z ∈ Submodule.span (LetA O n) (((W.φD T) ^ (k + 1)) '' S)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢; exact Submodule.add_mem _ ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact Submodule.zero_mem _
      smul_mem' := fun c z hz => by
        simp only [Set.mem_ofPred_eq] at hz ⊢
        rw [SatPW.φD_pow_smulA]; exact Submodule.smul_mem _ _ hz }
  have hle : Submodule.span (LetA O n) (W.φD T '' S) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change ((W.φD T) ^ k) (W.φD T y) ∈ Submodule.span (LetA O n) (((W.φD T) ^ (k + 1)) '' S)
    rw [show ((W.φD T) ^ k) (W.φD T y) = ((W.φD T) ^ (k + 1)) y by rw [pow_succ]; rfl]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  exact hle hz

theorem iter_down (hs : W.s = 1) (T : LocLat G Qp LL O) {M hh : ZMod n → ℕ}
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M hh) (a : ZMod n) :
    ∀ k : ℕ, ∀ y ∈ W.Nl T a,
      (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ hh (a - (s : ZMod n))) • y ∈
        Submodule.span (LetA O n) (((W.φD T) ^ k) '' (W.Nl T (a - (k : ZMod n)) : Set (W.DD T))) := by
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
  intro k
  induction k with
  | zero =>
    intro y hy
    simp only [Finset.range_zero, Finset.prod_empty, one_smul, pow_zero, Nat.cast_zero, sub_zero]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | succ k ih =>
    intro y hy
    set c : LetA O n := ((W.φA ^ k) W.q) ^ hh (a - (k : ZMod n)) with hc
    have hlet : a - ((k + 1 : ℕ) : ZMod n) = a - (k : ZMod n) - 1 := by push_cast; ring
    let U : Submodule (LetA O n) (W.DD T) :=
      (Submodule.span (LetA O n) (((W.φD T) ^ (k + 1)) ''
        (W.Nl T (a - ((k + 1 : ℕ) : ZMod n)) : Set (W.DD T)))).comap (c • LinearMap.id)
    have hle : Submodule.span (LetA O n) (((W.φD T) ^ k) '' (W.Nl T (a - (k : ZMod n)) : Set (W.DD T))) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨y', hy', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      have h1 := h5.2.1 (a - (k : ZMod n)) y' hy'
      rw [hQ] at h1
      have h2 := φpow_span W T _ k _ h1
      rw [SatPW.φD_pow_smulA, map_pow, ← hc] at h2
      rw [hlet]
      exact h2
    have h3 := hle (ih y hy)
    simp only [U, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, smul_smul] at h3
    rw [Finset.prod_range_succ, mul_comm]
    exact h3

theorem span_pow_le (T : LocLat G Qp LL O) {r : ℕ} (b : Fin r → W.DD T)
    (hb : ∀ x ∈ W.N T, ∃ a : Fin r → LetA O n, x = ∑ j, a j • b j) (c : ZMod n) (e : ℕ) :
    Submodule.span (LetA O n) (((W.φD T) ^ e) '' (W.Nl T c : Set (W.DD T))) ≤
      Submodule.span (LetA O n) (Set.range fun j => ((W.φD T) ^ e) ((letE c : LetA O n) • b j)) := by
  rw [Submodule.span_le]
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨aa, haa⟩ := hb z hz
  rw [SetLike.mem_coe, LinearMap.smul_apply, LinearMap.id_apply, haa, Finset.smul_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_comm, SatPW.φD_pow_smulA]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem arc_down [NeZero n] (hs : W.s = 1) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (T : LocLat G Qp LL O)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun i => Mw A.G₀ A.S A.η (A.ty i)) (fun i => Hw A.G₀ A.S A.η (A.ty i)))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ) (x : W.DD T)
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x) := by
  set a : ZMod n := c' + (e : ZMod n) with ha
  set Λ : LetA O n := Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A a e with hΛdef
  obtain ⟨y, hyN, hya, rfl⟩ := hx
  rw [one_smul]
  have hyl : y ∈ W.Nl T a := ⟨y, hyN.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hya⟩
  have h1 := iter_down W hs T h5 a e y hyl
  rw [show a - (e : ZMod n) = c' by rw [ha]; ring] at h1
  set Pe : LetA O n := ∏ s ∈ Finset.range e, ((W.φA ^ s) W.q) ^ Hw A.G₀ A.S A.η (A.ty (a - (s : ZMod n)))
    with hPe
  set Rs : LetA O n := ∏ s ∈ Finset.range e, ((W.φA ^ s) W.q) ^
    (A.Hs a e s - Hw A.G₀ A.S A.η (A.ty (a - (s : ZMod n)))) with hRs
  obtain ⟨u, hu, hue⟩ := prod_q_eqE W hR e (fun s => A.Hs a e s)
  have hsplit : ∏ s ∈ Finset.range e, ((W.φA ^ s) W.q) ^ A.Hs a e s = Rs * Pe := by
    rw [hRs, hPe, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s hs' => ?_
    have := hw_le_hs A hA c' hc' e s (Finset.mem_range.1 hs')
    rw [← ha] at this
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨u', hu'⟩ := hu.exists_left_inv
  have hΛ : Λ = u' * (Rs * Pe) := by
    calc Λ = u' * (u * Λ) := by rw [← mul_assoc, hu', one_mul]
      _ = u' * (Rs * Pe) := by rw [← hsplit, hue]; rfl
  have h2 : Λ • y ∈ Submodule.span (LetA O n) (((W.φD T) ^ e) '' (W.Nl T c' : Set (W.DD T))) := by
    rw [hΛ, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ h1)
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hmod
  have h3 := span_pow_le W T b (fun z hz => (huniq z hz).exists) c' e h2
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hbΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c' ((letE c' : LetA O n) • b j) := fun j =>
    ⟨PhiPowers.smul_mem_NΔ W T (SatPW.letE_mem_AΔ W c') (hb j),
      ⟨b j, (hb j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  obtain ⟨d, hd, hzd⟩ := average hΔ cc (fun j => ((W.φD T) ^ e) ((letE c' : LetA O n) • b j))
    (fun j δ hδ => φD_pow_Δ W T (hbΔ j).1.2 e δ hδ)
    (fun δ hδ => (PhiPowers.smul_mem_NΔ W T (lam_mem_AΔ W hR.1 A a e) hyN).2 δ hδ) hcc.symm
  refine ⟨∑ j, d j • ((W.φD T) ^ e) ((letE c' : LetA O n) • b j), ?_, by rw [one_smul]; exact hzd⟩
  exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨d j, hd j, _, hbΔ j, rfl⟩

theorem Pp_letter (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (y : W.DD T)
    (hy : y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e) : (letE (c + (e : ZMod n)) : LetA O n) • y = y := by
  let S : AddSubgroup (W.DD T) :=
    { carrier := {y | (letE (c + (e : ZMod n)) : LetA O n) • y = y}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢; rw [smul_add, ha, hb]
      zero_mem' := by simp only [Set.mem_ofPred_eq, smul_zero]
      neg_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at ha ⊢; rw [smul_neg, ha] }
  have hgen : {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ z = a • ((W.φD T) ^ e) x} ⊆
      (S : Set (W.DD T)) := by
    rintro _ ⟨a, -, x, ⟨-, ⟨y', -, hyx⟩⟩, rfl⟩
    have hxc : (letE c : LetA O n) • x = x := by
      rw [← hyx, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]
    show (letE (c + (e : ZMod n)) : LetA O n) • (a • ((W.φD T) ^ e) x) = a • ((W.φD T) ^ e) x
    rw [smul_comm, φD_pow_letter W T c x hxc e]
  exact (AddSubgroup.closure_le S).2 hgen hy

theorem arc_sat (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hsat : Formalism.MainNotions.ArcLiftingSetup.SATcore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ)
    (hup : ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c' e,
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • y))
    (x : W.DD T) (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hk : ∃ k : ℕ, Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x)) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 x := by
  set Λ : LetA O n := Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  obtain ⟨y, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨z, hzN, -, hzy⟩ := hup y hyP
  have hΛ2 : (Λ * Λ) • x ∈ W.NΔ T := by
    rw [mul_smul, hyx, hzy, one_smul]; exact hzN
  obtain ⟨k, w, hwN, -, hwk⟩ := hk
  have hPi : Λ ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W :=
    Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self s))) _
  obtain ⟨x', hx'N, hxx'⟩ := hsat hCA T 1 (Λ * Λ) hT (Submonoid.one_mem _)
    (Submonoid.mul_mem _ hPi hPi) x hΛ2 ⟨k, w, hwN, hwk⟩
  rw [one_smul] at hxx'
  obtain ⟨h3, h6⟩ := SatW.ring_clauses W hR
  have hU : SatW.UPi PD.p Λ :=
    SatW.UPi.prod _ _ fun s _ => (SatW.UPi_qpow W h3 h6 s).pow _
  have hlet : Λ • ((letE (c' + (e : ZMod n)) : LetA O n) • x) = Λ • x := by
    rw [smul_comm, hyx, Pp_letter W T c' e y hyP]
  have hxa := SatW.smul_cancel W T (SatW.isUnit_EE_of_UPi W hU) hlet
  exact ⟨x, by rw [hxx']; exact hx'N, hxa, (one_smul _ _).symm⟩

open TensorProduct

theorem crisMap_φVB {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (z : T₁.V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (φVB PD (LL := LL) (V := T₁.V) z) =
      φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisMap_φVB_pow {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (e : ℕ) (z : T₁.V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (((φVB PD (LL := LL) (V := T₁.V)) ^ e) z) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f z) := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', Module.End.mul_apply, crisMap_φVB, ih, pow_succ', Module.End.mul_apply]

theorem γD_Nl (T : LocLat G Qp LL O) (c : ZMod n) (δ : W.Gam) {x : W.DD T} (hx : x ∈ W.Nl T c) :
    W.γD T δ x ∈ W.Nl T c := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨W.γD T δ z, W.N_Γ T δ z hz, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [γD_smulA, γA_letE]

theorem Nl_le_N (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T c) : x ∈ W.N T := by
  obtain ⟨z, hz, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact (W.N T).smul_mem _ hz

theorem map_smulA {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (a : LetA O n) (x : W.DD T₁) :
    W.map F (a • x) = a • W.map F x :=
  ((W.map F).restrictScalars (LetA O n)).map_smul a x

theorem map_smulO {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (c : O) (x : W.DD T₁) :
    W.map F (c • x) = c • W.map F x := by
  rw [← algebraMap_smul (LetA O n) c x, map_smulA, algebraMap_smul]

theorem arcL_at [NeZero n] (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) : Formalism.MainNotions.ArcLiftingSetup.ArcLCore W := by
  intro _ T₁ T₂ F hSur c' rr e hK x₂ hx₂
  obtain ⟨⟨hx₂N, hx₂Δ⟩, hx₂l⟩ := hx₂
  obtain ⟨x₁', hx₁'l, hmap⟩ := hK x₂ hx₂l hx₂Δ
  simp only [LinearMap.coe_restrictScalars] at hmap
  obtain ⟨u, hu⟩ := hΔ
  set x₁ : W.DD T₁ := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ x₁' with hx₁
  have hx₁l : x₁ ∈ W.Nl T₁ c' :=
    Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => γD_Nl W T₁ c' δ hx₁'l)
  have hx₁N : x₁ ∈ W.N T₁ := Nl_le_N W T₁ c' hx₁l
  have hx₁Δ : ∀ δ' ∈ W.DelF, W.γD T₁ δ' x₁ = x₁ := by
    intro δ' hδ'
    rw [hx₁, map_smul, map_sum]
    congr 1
    refine Finset.sum_equiv (Equiv.mulLeft δ') (fun δ => ?_) (fun δ _ => ?_)
    · exact mem_DelF_mul hδ' δ
    · rw [← W.γD_mul]; rfl
  have hlp : Formalism.MainNotions.LiftingTheory.lp W rr • x₂ = (((PD.p : ℕ) : O) ^ rr) • x₂ := by
    rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ rr) x₂, map_pow, map_natCast]; rfl
  have hmap1 : W.map F x₁ = (((PD.p : ℕ) : O) ^ rr) • x₂ := by
    rw [hx₁, map_smulO, map_sum]
    have h1 : ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ x₁') = (((PD.p : ℕ) : O) ^ rr) • x₂ := by
      intro δ hδ
      rw [W.map_γ, hmap, hlp, map_smul, hx₂Δ δ hδ]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, smul_smul,
      ← hu, Units.inv_mul, one_smul]
  have hN2 : W.map F x₁ ∈ W.N T₂ := W.map_N F hSur.1 hSur.2.1 x₁ hx₁N
  refine ⟨x₁, ⟨⟨hx₁N, hx₁Δ⟩, hx₁l⟩, ?_⟩
  unfold Formalism.MainNotions.ArcLiftingSetup.cmpD
  rw [dif_pos hx₁N, dif_pos hx₂N, crisMap_φVB_pow]
  have hc := W.cmp_map F hSur.1 hSur.2.1 ⟨x₁, hx₁N⟩ hN2
  have e1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (W.cmp T₁ ⟨x₁, hx₁N⟩) = W.cmp T₂ ⟨W.map F x₁, hN2⟩ := hc.symm
  have e2 : (⟨W.map F x₁, hN2⟩ : ↥(W.N T₂)) = (((PD.p : ℕ) : O) ^ rr) • ⟨x₂, hx₂N⟩ :=
    Subtype.ext hmap1
  rw [e1, e2, W.cmp_smul, map_smul, map_pow, map_natCast]

theorem arc_pi (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hsatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e M : ℕ)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T)
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x))
    (h0 : Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e M (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol x 0) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e (W.π₀ * Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) x := by
  set Λ : LetA O n := Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  obtain ⟨κ, κ', Hh, aa, -, haa, y, hyP, hy⟩ := h0
  have haa0 : ∀ k, aa k = 0 := fun k => W.EE_inj (by rw [map_zero, ← (haa k).2, Pi.zero_apply, mul_zero])
  simp only [haa0, zero_smul, Finset.sum_const_zero, sub_zero] at hy
  have hPi : Λ ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W :=
    Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self s))) _
  have hπ : W.π₀ ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W := Submonoid.subset_closure (Set.mem_insert _ _)
  obtain ⟨h3, h6⟩ := SatW.ring_clauses W hR
  have hU : SatW.UPi PD.p Λ :=
    SatW.UPi.prod _ _ fun s _ => (SatW.UPi_qpow W h3 h6 s).pow _
  have hk : Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e (W.π₀ * Λ) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ' + κ) • x) := by
    refine ⟨y, hyP, SatW.smul_cancel W T (SatW.isUnit_EE_of_UPi W hU) ?_⟩
    have e1 : Λ • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ' + κ) • x) =
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • Λ • x := by
      rw [pow_add, mul_smul, smul_comm Λ, smul_comm Λ (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ)]
    rw [e1, hy, smul_smul]
    congr 1
    ring
  exact hsatP hCA T c' e (W.π₀ * Λ) Λ hT (Submonoid.mul_mem _ hπ hPi) hPi x hx ⟨κ' + κ, hk⟩

def ArcHyp (P : Formalism.MainNotions.ArcLiftingSetup.ArcP n → ZMod n → ℕ → ∀ (T : LocLat G Qp LL O) (d : ℕ),
      (Fin d → W.DD T) → (Fin d → ℕ → Fin d → LL) → Prop) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : Formalism.MainNotions.ArcLiftingSetup.ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ e : ℕ,
    A.j ≤ e → e ≤ A.len c → ∀ T : LocLat G Qp LL O, Formalism.MainNotions.ArcLiftingSetup.Win W A T →
      ∀ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL),
        Formalism.MainNotions.ArcLiftingSetup.IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol →
          P A (c - ((A.len c : ℕ) : ZMod n)) e T d b sol

def FrameBasis (_A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (_sol : Fin d → ℕ → Fin d → LL) : Prop :=
  LinearIndependent LL (fun k : Fin d => Formalism.MainNotions.ArcLiftingSetup.dv W T e b (Pi.single k 1)) ∧
    Submodule.span LL (Set.range fun k : Fin d => Formalism.MainNotions.ArcLiftingSetup.dv W T e b (Pi.single k 1)) =
      DcrisL PD T.ρ (W.emb (c' + (e : ZMod n)))

def SecOfP (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ x, Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x) →
    ∃ f, (∀ k, Formalism.MainNotions.ArcLiftingSetup.InFr W (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) (f k)) ∧
      Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e (A.M PD.p) (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol
        (Formalism.MainNotions.ArcLiftingSetup.lA W ^ A.σ PD.p • x) f

def POfSec (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ f : Fin d → W.EE,
    (∀ k, Formalism.MainNotions.ArcLiftingSetup.InFr W (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) (f k)) →
    ∃ x, Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x) ∧
      Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e (A.M PD.p) (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol x
        fun k => Formalism.MainNotions.ArcLiftingSetup.lE W (A.σ PD.p) * f k

def SecOfN (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ x, Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 x →
    ∃ f, Formalism.MainNotions.ArcLiftingSetup.InNL W T (c' + (e : ZMod n)) e (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b f ∧
      Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e (A.M PD.p) (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol
        (Formalism.MainNotions.ArcLiftingSetup.lA W ^ A.σ PD.p • x) f

def NOfSec (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ f, Formalism.MainNotions.ArcLiftingSetup.InNL W T (c' + (e : ZMod n)) e (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b f →
    ∃ x, Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 x ∧
      Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e (A.M PD.p) (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol x
        fun k => Formalism.MainNotions.ArcLiftingSetup.lE W (A.σ PD.p) * f k

def SecCrit (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (d : ℕ)
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ x (k : ℕ) f, Formalism.MainNotions.ArcLiftingSetup.InFP W T c' e 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e • x) →
    Formalism.MainNotions.ArcLiftingSetup.RepVV W T c' e (A.M PD.p) (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) f →
    (∀ m, Formalism.MainNotions.ArcLiftingSetup.InFr W (c' + (e : ZMod n)) 1 (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e) (f m)) →
    (Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c' + (e : ZMod n)) 1 x ↔
      ∃ κ : ℕ, Formalism.MainNotions.ArcLiftingSetup.SecIn W (c' + (e : ZMod n)) e
        (Formalism.MainNotions.ArcLiftingSetup.condNN W T (c' + (e : ZMod n)) e b) fun m => Formalism.MainNotions.ArcLiftingSetup.lE W κ * f m)

def ArcFrame : Prop :=
  ArcHyp W (FrameBasis W) ∧ ArcHyp W (SecOfP W) ∧ ArcHyp W (POfSec W) ∧ ArcHyp W (SecOfN W) ∧
    ArcHyp W (NOfSec W) ∧ ArcHyp W (SecCrit W)

theorem arcCore_of [NeZero n] (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (hsat : Formalism.MainNotions.ArcLiftingSetup.SATcore W)
    (hsatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hF : ArcFrame W) : Formalism.MainNotions.ArcLiftingSetup.ArcCore W := by
  intro hCA h5p A hA c hc e hje hel c' a Λ M σ
  obtain ⟨hF0, hF1, hF2, hF3, hF4, hF6⟩ := hF
  have hs : W.s = 1 := hCA.2.1
  have hc' : c' ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hup := fun T hT => arc_up W hs hR h5 A hA c' hc' e T hT
  refine ⟨arc_ring W (hTr hCA).2.1 hR.1 h5p A hA a e hje, fun T hT => ⟨hup T hT,
    fun x hx => arc_down W hs hR T A hA (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)) (hmod T hT.1) hΔ
      c' hc' e x hx,
    fun x hx hk => arc_sat W hCA hsat hR T hT.1 A c' e (hup T hT) x hx hk,
    fun d b sol hb => ⟨hF0 hCA h5p A hA c hc e hje hel T hT d b sol hb,
      hF1 hCA h5p A hA c hc e hje hel T hT d b sol hb,
      hF2 hCA h5p A hA c hc e hje hel T hT d b sol hb,
      hF3 hCA h5p A hA c hc e hje hel T hT d b sol hb,
      hF4 hCA h5p A hA c hc e hje hel T hT d b sol hb,
      fun x hx h0 => arc_pi W hCA hsatP hR T hT.1 A c' e M b sol x hx h0,
      hF6 hCA h5p A hA c hc e hje hel T hT d b sol hb⟩⟩⟩

end Formalism.MainNotions.UnusedSlot80.ArcC

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

def ArcFrameL (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ArcC.ArcFrame ((HW l).W K 1 LL hG)

theorem arc_coordinates_of_frame (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hFr : ArcFrameL D HW) : ArcCoordinatesTheorem D HW F Cm := by
  rintro ⟨-, -, h5, h9, -, hTr, -, hSat⟩ l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hCW : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hG) := caseA_of_unram' (D.loc l) (HW l) hG hCA.1 hCA.2.1
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hCA.2.1
  have hK := finrank_K0_eq_one_of_le_Kur hCA.1
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hmod : ∀ T, IsCrys ((D.loc l).PD K) T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T
      ((HW l).W K 1 LL hG).π₀ := fun T hT => ((h9 l K 1 LL hG T hT hs hp).2.2 hK).2
  have hc1 := Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hG)
  have := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    cardΔ_of (W := (HW l).W K 1 LL hG) (not_isUnit_p ((HW l).W K 1 LL hG) (valRing_rec (D.loc l) LL))
      (card_DelF (W := (HW l).W K 1 LL hG) hs hp hK (h9 l K 1 LL hG _ hc1))
  exact ⟨ArcC.arcCore_of _ (hTr l K 1 LL hG) hR (h5 l K 1 LL hG) hmod hΔ (hSat l K LL hG hCA h5l)
      (saturation_pullback_of_ring_condition D HW F h9 l K LL hG hCA h5l) (hFr l K LL hG hCA h5l),
    ArcC.arcL_at _ hΔ⟩

end Formalism.MainNotions.UnusedSlot80
