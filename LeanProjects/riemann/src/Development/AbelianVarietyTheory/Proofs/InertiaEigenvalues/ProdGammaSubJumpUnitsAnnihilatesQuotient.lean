import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurentStatement

namespace GlobalTheory.NL.KillLevels

theorem kill {β α M R : Type} [DecidableEq β] [Semiring R] [AddCommMonoid M] [Module R M]
    (Sub : ℤ → Submodule R M) (y : ℕ) (S : α → Prop) (E : α → ℤ → M)
    (c : ℤ → β) (hc : Function.Injective c)
    (P : Finset β → α → α) (op : β → α → α)
    (hP0 : ∀ x, P ∅ x = x)
    (hP : ∀ A d x, d ∈ A → P A x = P (A.erase d) (op d x))
    (hS : ∀ d x, S x → S (op d x))
    (hE : ∀ x, S x → ∀ j, E x j ∈ Sub j)
    (hstep : ∀ d x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ j < k, E (op d x) j ∈ Sub (j - y)) ∧ (d = c k → E (op d x) k ∈ Sub (k - y))) :
    ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → ¬ Sub k' ≤ Sub (k' - y) → c k' ∈ A) → ∀ j, E (P A x) j ∈ Sub (j - y) := by
  have hins : ∀ A d x, d ∉ A → P (insert d A) x = P A (op d x) := fun A d x hd => by
    rw [hP (insert d A) d x (Finset.mem_insert_self d A), Finset.erase_insert hd]
  have pres : ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      S (P A x) ∧ ∀ j < k, E (P A x) j ∈ Sub (j - y) := by
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro x k hx hk
      rw [hP0]
      exact ⟨hx, hk⟩
    · intro d A hd ih x k hx hk
      rw [hins A d x hd]
      exact ih _ k (hS d x hx) (hstep d x k hx hk).1
  have nobad : ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → Sub k' ≤ Sub (k' - y)) → ∀ j, E (P A x) j ∈ Sub (j - y) := by
    intro A x k hx hk hgood j
    obtain ⟨hS', hk'⟩ := pres A x k hx hk
    by_cases hj : j < k
    · exact hk' j hj
    · exact hgood j (not_lt.1 hj) (hE _ hS' j)
  suffices H : ∀ n : ℕ, ∀ A : Finset β, A.card ≤ n → ∀ x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → ¬ Sub k' ≤ Sub (k' - y) → c k' ∈ A) → ∀ j, E (P A x) j ∈ Sub (j - y) from
    fun A => H _ A le_rfl
  intro n
  induction n with
  | zero =>
    intro A hA x k hx hk hbad
    by_cases hex : ∃ k', k ≤ k' ∧ ¬ Sub k' ≤ Sub (k' - y)
    · obtain ⟨k', h1, h2⟩ := hex
      have h3 := hbad k' h1 h2
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hA)] at h3
      simp at h3
    · push Not at hex
      exact nobad A x k hx hk hex
  | succ n ih =>
    intro A hA x k hx hk hbad
    classical
    by_cases hex : ∃ m : ℕ, ¬ Sub (k + m) ≤ Sub (k + m - y)
    · have hm0 : ¬ Sub (k + (Nat.find hex : ℕ)) ≤ Sub (k + (Nat.find hex : ℕ) - y) := Nat.find_spec hex
      have hmin : ∀ m < Nat.find hex, Sub (k + m) ≤ Sub (k + m - y) :=
        fun m hm => not_not.1 (Nat.find_min hex hm)
      have hla : ∀ j < k + (Nat.find hex : ℕ), E x j ∈ Sub (j - y) := by
        intro j hj
        by_cases hjk : j < k
        · exact hk j hjk
        · have e : j = k + ((j - k).toNat : ℕ) := by omega
          have h1 := hmin (j - k).toNat (by omega)
          rw [← e] at h1
          exact h1 (hE x hx j)
      have hca : c (k + (Nat.find hex : ℕ)) ∈ A := hbad _ (by omega) hm0
      have hla' : ∀ j < k + (Nat.find hex : ℕ) + 1,
          E (op (c (k + (Nat.find hex : ℕ))) x) j ∈ Sub (j - y) := by
        intro j hj
        rcases lt_or_eq_of_le (Int.lt_add_one_iff.1 hj) with h | h
        · exact (hstep _ x _ hx hla).1 j h
        · rw [h]; exact (hstep _ x _ hx hla).2 rfl
      rw [hP A _ x hca]
      refine ih (A.erase _) ?_ _ _ (hS _ x hx) hla' ?_
      · have := Finset.card_erase_of_mem hca
        omega
      · intro k' hk' hb
        refine Finset.mem_erase.2 ⟨fun he => ?_, hbad k' (by omega) hb⟩
        have := hc he
        omega
    · push Not at hex
      refine nobad A x k hx hk fun k' hk' => ?_
      have h1 := hex (k' - k).toNat
      rwa [show k + (((k' - k).toNat : ℕ) : ℤ) = k' by omega] at h1

end GlobalTheory.NL.KillLevels

noncomputable section

namespace GlobalTheory.NL.KillLevels

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lev_algebraMap (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (d : O) :
    W.lev i ζ (algebraMap O (LetA O n) d) = PowerSeries.C (algebraMap O LL d) := by
  rw [AlgHom.commutes, PowerSeries.algebraMap_apply]

theorem map_sub_smul {M : Type} [AddCommGroup M] [Module LL M] (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (e : ↥(W.N T) →+ (ℤ → M))
    (he : ∀ (a : LetA O n) (x : ↥(W.N T)), e (a • x) = conv (W.lev i ζ a) (e x))
    (y : ℕ) (z : W.DD T) (d : O) (hz : W.Q ^ y • z ∈ W.N T) (hγz : W.Q ^ y • W.γ T z ∈ W.N T) :
    ∃ hz' : W.Q ^ y • (W.γ T z - d • z) ∈ W.N T, ∀ j : ℤ,
      e ⟨_, hz'⟩ j = e ⟨_, hγz⟩ j - algebraMap O LL d • e ⟨_, hz⟩ j := by
  have hdz : W.Q ^ y • (d • z) = algebraMap O (LetA O n) d • (W.Q ^ y • z) := by
    rw [← algebraMap_smul (LetA O n) d z, smul_smul, mul_comm, ← smul_smul]
  have hz' : W.Q ^ y • (W.γ T z - d • z) ∈ W.N T := by
    rw [smul_sub, hdz]
    exact (W.N T).sub_mem hγz ((W.N T).smul_mem _ hz)
  refine ⟨hz', fun j => ?_⟩
  have e1 : (⟨_, hz'⟩ : ↥(W.N T)) = ⟨_, hγz⟩ - algebraMap O (LetA O n) d • ⟨_, hz⟩ := by
    apply Subtype.ext
    show W.Q ^ y • (W.γ T z - d • z) = W.Q ^ y • W.γ T z - algebraMap O (LetA O n) d • (W.Q ^ y • z)
    rw [smul_sub, hdz]
  rw [e1, map_sub, he, lev_algebraMap, GlobalTheory.NL.LevInj.conv_C]
  rfl

theorem aeval_erase [DecidableEq Oˣ] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (A : Finset Oˣ) (d : Oˣ)
    (z : W.DD T) (hd : d ∈ A) :
    Polynomial.aeval (W.γ T) (∏ c ∈ A, ((Polynomial.X : Polynomial O) - Polynomial.C (Units.val c))) z =
      Polynomial.aeval (W.γ T) (∏ c ∈ A.erase d, ((Polynomial.X : Polynomial O) - Polynomial.C (Units.val c)))
        (W.γ T z - (d : O) • z) := by
  rw [← Finset.prod_erase_mul A _ hd, map_mul, Module.End.mul_apply]
  congr 1
  simp

theorem algebraMap_uU_zpow (W : LocWach PD LL O v n) (m : ℤ) :
    algebraMap O LL ((uU W ^ m : Oˣ) : O) = algebraMap O LL (W.χΓ W.gam : O) ^ m := by
  have h2 := congrArg Units.val (map_zpow (Units.map (algebraMap O LL).toMonoidHom) (uU W) m)
  rw [Units.val_zpow_eq_zpow_val] at h2
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h2
  exact h2

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

open Classical in

def Ex (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) : ℤ → T.V ⊗[ℚ_[l]] P.R.B :=
  if hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T then ex C h T i ζ ⟨_, hz⟩ else 0

theorem Ex_eq (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T) :
    Ex C h T i ζ y z = ex C h T i ζ ⟨_, hz⟩ := by
  unfold Ex
  rw [dif_pos hz]

def SubF (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (k : ℤ) :
    Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) :=
  Di H h T i ⊓ (FilAt (P.PD K) T τ (-k)).comap (ιV (P.PD K) (LL := ↥LL.1) (V := T.V))

theorem SubF_mono (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Monotone (SubF H h T i τ) := by
  intro a b hab
  have hanti : Antitone (FilAt (P.PD K) T τ) :=
    antitone_int_of_succ_le (GlobalTheory.NL.Model.FilAt_anti T τ)
  exact inf_le_inf_left _ (Submodule.comap_mono (hanti (by omega)))

set_option maxHeartbeats 1000000 in

theorem exists_jump (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : ℕ) (k : ℤ) (hb : ¬ SubF H h T i τ k ≤ SubF H h T i τ (k - y)) :
    ∃ a : ℤ, IsJumpV (P.PD K) T.ρ τ a ∧ -k ≤ a ∧ a ≤ y - k - 1 := by
  by_contra hn
  push Not at hn
  apply hb
  have hnj : ∀ a : ℤ, -k ≤ a → a ≤ y - k - 1 →
      FildR (P.PD K) T.ρ τ (a + 1) = FildR (P.PD K) T.ρ τ a := by
    intro a h1 h2
    by_contra hj
    exact absurd h2 (not_le.2 (hn a hj h1))
  have hfil : ∀ m : ℕ, m ≤ y → FildR (P.PD K) T.ρ τ (-k + m) = FildR (P.PD K) T.ρ τ (-k) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [show -k + ((m + 1 : ℕ) : ℤ) = (-k + m) + 1 by push_cast; ring,
        hnj _ (by omega) (by omega), ih (by omega)]
  have hF : FilAt (P.PD K) T τ (-(k - y)) = FilAt (P.PD K) T τ (-k) := by
    unfold FilAt
    rw [show -(k - (y : ℤ)) = -k + (y : ℕ) by ring, hfil y le_rfl]
  intro e he
  unfold SubF at he ⊢
  rw [hF]
  exact he

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem Ex_sub_smul (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) (d : ↥(OL LL))
    (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
    (hγz : (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T) (j : ℤ) :
    Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j =
      Ex C h T i ζ y ((H.W K s LL h).γ T z) j - algebraMap ↥(OL LL) ↥LL.1 d • Ex C h T i ζ y z j := by
  obtain ⟨hz', he⟩ := map_sub_smul (H.W K s LL h) T i ζ ((C.C K s LL h).tie.levB T i ζ)
    (GlobalTheory.NL.Model.ex_smul C h T i ζ) y z d hz hγz
  rw [Ex_eq C h T i ζ y _ hz', Ex_eq C h T i ζ y _ hγz, Ex_eq C h T i ζ y z hz]
  exact he j

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem step (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : ℕ) (w : PowerSeries ↥LL.1)
    (hw0 : PowerSeries.constantCoeff w = algebraMap ↥(OL LL) ↥LL.1
      ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (-(y : ℤ)))
    (hγN : ∀ z : (H.W K s LL h).DD T, (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T →
      (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T)
    (hw : ∀ (z : (H.W K s LL h).DD T) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
      (hγ : (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T) (j : ℤ),
      ex C h T i ζ ⟨(H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z, hγ⟩ j =
        conv w (fun m => algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ m •
          ex C h T i ζ ⟨(H.W K s LL h).Q ^ y • z, hz⟩ m) j)
    (hE : ∀ z : (H.W K s LL h).DD T, (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T →
      ∀ j, Ex C h T i ζ y z j ∈ SubF H h T i τ j)
    (d : ↥(OL LL)) (z : (H.W K s LL h).DD T) (k : ℤ) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
    (hk : ∀ j < k, Ex C h T i ζ y z j ∈ SubF H h T i τ (j - y)) :
    (∀ j < k, Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j ∈ SubF H h T i τ (j - y)) ∧
      (algebraMap ↥(OL LL) ↥LL.1 d =
          algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (k - y) →
        Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) k ∈ SubF H h T i τ (k - y)) := by
  have hform : ∀ j, Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j =
      conv w (fun m => algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ m •
        Ex C h T i ζ y z m) j - algebraMap ↥(OL LL) ↥LL.1 d • Ex C h T i ζ y z j := by
    intro j
    rw [Ex_sub_smul C h T i ζ y z d hz (hγN z hz) j, Ex_eq C h T i ζ y _ (hγN z hz),
      Ex_eq C h T i ζ y z hz, hw z hz (hγN z hz) j]
  have hbdd : ∃ m : ℤ, ∀ j < m, Ex C h T i ζ y z j = 0 := by
    obtain ⟨m, hm⟩ := (C.C K s LL h).tie.levB_supp T i ζ ⟨_, hz⟩
    exact ⟨m, fun j hj => by rw [Ex_eq C h T i ζ y z hz]; exact hm j hj⟩
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent w
    (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)))
    (SubF H h T i τ) (SubF_mono H h T i τ) y (Ex C h T i ζ y z) hbdd (hE z hz) k hk
  refine ⟨fun j hj => ?_, fun hd => ?_⟩
  · rw [hform j]
    exact (SubF H h T i τ _).sub_mem (h3 j hj) ((SubF H h T i τ _).smul_mem _ (hk j hj))
  · rw [hform k, hd]
    have hu0 : algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ≠ 0 :=
      (((H.W K s LL h).χΓ (H.W K s LL h).gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
    have e : algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (k - (y : ℤ)) =
        PowerSeries.constantCoeff w *
          algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ k := by
      rw [hw0, ← zpow_add₀ hu0, neg_add_eq_sub]
    rw [e]
    exact h4

end Concrete

end GlobalTheory.NL.KillLevels

end

namespace GlobalTheory.NL.KillLevels

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem annihilate : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ Fs : Finset (↥(OL LL))ˣ, (∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → uU W ^ (-(a + j)) ∈ Fs) → ∀ x ∈ invN W T (W.Q ^ y), Polynomial.aeval (W.γ T) (∏ c ∈ Fs, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x ∈ W.N T := by
  classical
  intro D HW F Cm l _ K s LL h W T hT y hy Fs hFs x hx
  have hx' : W.Q ^ y • x ∈ W.N T := by simpa [invN, smulA] using hx
  obtain ⟨hγ, hgam⟩ := GlobalTheory.T.wachN_invQPow_gamma_stable D HW F Cm l K s LL h T hT y
  let S : W.DD T → Prop := fun z => W.Q ^ y • z ∈ W.N T
  let op : (↥(OL LL))ˣ → W.DD T → W.DD T := fun d z => W.γ T z - (d : ↥(OL LL)) • z
  let Pf : Finset (↥(OL LL))ˣ → W.DD T → W.DD T := fun A z =>
    Polynomial.aeval (W.γ T) (∏ c ∈ A, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) z
  have hP0 : ∀ z, Pf ∅ z = z := by intro z; simp [Pf]
  have hP : ∀ A d z, d ∈ A → Pf A z = Pf (A.erase d) (op d z) := fun A d z hd => aeval_erase W T A d z hd
  have hS : ∀ d z, S z → S (op d z) := fun d z hz =>
    (map_sub_smul W T 0 1 (((Cm l).C K s LL h).tie.levB T 0 1)
      (GlobalTheory.NL.Model.ex_smul (Cm l) h T 0 1) y z (d : ↥(OL LL)) hz (hγ z hz)).1
  have hSA : ∀ A z, S z → S (Pf A z) := by
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro z hz; rw [hP0]; exact hz
    · intro d A hd ih z hz
      rw [hP (insert d A) d z (Finset.mem_insert_self d A), Finset.erase_insert hd]
      exact ih _ (hS d z hz)
  have hQ : S (Pf Fs x) := hSA Fs x hx'
  refine (GlobalTheory.T.mem_wachN_iff_expansion D HW F Cm l K s LL h T hT y (Pf Fs x) hQ).2 ?_
  intro i ζ hζ
  obtain ⟨τ, hτ⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).1 i ζ hζ
  obtain ⟨w, hw0, hw⟩ := hgam i ζ hζ
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hτ
  let c : ℤ → (↥(OL LL))ˣ := fun k => uU W ^ (k - (y : ℤ))
  have hu0 : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ≠ 0 :=
    ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hc : Function.Injective c := by
    intro a b hab
    by_contra hne
    have h1 : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ^ (a - (y : ℤ)) =
        algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ^ (b - (y : ℤ)) :=
      (algebraMap_uU_zpow W _).symm.trans
        ((congrArg (fun e : (↥(OL LL))ˣ => algebraMap ↥(OL LL) ↥LL.1 (e : ↥(OL LL))) hab).trans
          (algebraMap_uU_zpow W _))
    refine GlobalTheory.NL.AtZero.chi_gam_zpow_ne_one W (a - b) (sub_ne_zero.2 hne) ?_
    have e : a - b = (a - (y : ℤ)) - (b - (y : ℤ)) := by ring
    rw [e, zpow_sub₀ hu0, h1, div_self (zpow_ne_zero _ hu0)]
  have hE : ∀ z, S z → ∀ j, Ex (Cm l) h T i ζ y z j ∈ SubF (HW l) h T i τ j := by
    intro z hz j
    rw [Ex_eq (Cm l) h T i ζ y z hz]
    exact ((hlat _).1 (GlobalTheory.NL.Model.ex_mem_Lat (Cm l) h T i ζ ⟨_, hz⟩)).2 j
  have hbdd : ∀ z, S z → ∃ m : ℤ, ∀ k < m, Ex (Cm l) h T i ζ y z k = 0 := by
    intro z hz
    rw [Ex_eq (Cm l) h T i ζ y z hz]
    exact ((Cm l).C K s LL h).tie.levB_supp T i ζ ⟨_, hz⟩
  obtain ⟨m, hm⟩ := hbdd x hx'
  have key := kill (SubF (HW l) h T i τ) y S (Ex (Cm l) h T i ζ y) c hc Pf op hP0 hP hS hE
    (fun d z k hz hk =>
      ⟨(step (Cm l) h T i ζ τ y w hw0 hγ hw hE (d : ↥(OL LL)) z k hz hk).1, fun hd =>
        (step (Cm l) h T i ζ τ y w hw0 hγ hw hE (d : ↥(OL LL)) z k hz hk).2
          (by rw [hd]; exact algebraMap_uU_zpow W _)⟩)
    Fs x m hx' (fun j hj => by rw [hm j hj]; exact Submodule.zero_mem _)
    (fun k _ hb => by
      obtain ⟨a, ha, h1, h2⟩ := exists_jump (HW l) h T i τ y k hb
      have h3 := hFs a ⟨τ, ha⟩ ((y : ℤ) - k - a).toNat (by omega) (by omega)
      have e : -(a + ((((y : ℤ) - k - a).toNat : ℕ) : ℤ)) = k - (y : ℤ) := by omega
      rw [e] at h3
      exact h3)
  obtain ⟨m', hm'⟩ := hbdd _ hQ
  refine ⟨fun j => Ex (Cm l) h T i ζ y (Pf Fs x) (j + y), (hlat _).2 ⟨⟨m' - y, fun k hk => hm' _ (by omega)⟩,
    fun k => ?_⟩, fun j => ?_⟩
  · have h1 := key (k + y)
    rw [add_sub_cancel_right] at h1
    exact h1
  · show _ = Ex (Cm l) h T i ζ y (Pf Fs x) (j - y + y)
    rw [sub_add_cancel, Ex_eq (Cm l) h T i ζ y _ hQ]

end GlobalTheory.NL.KillLevels
