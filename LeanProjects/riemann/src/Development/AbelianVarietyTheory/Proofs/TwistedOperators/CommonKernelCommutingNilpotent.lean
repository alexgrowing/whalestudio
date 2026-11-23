import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory

noncomputable def jointNullChain {V : Type} [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V)
    (S : Submodule ℂ V) : ℕ → Submodule ℂ V
  | 0 => S
  | m + 1 => jointNullChain T S m ⊓ LinearMap.ker (T m)

theorem exists_common_null_of_commute_locallyNilpotent :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V),
      FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) →
      (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  intro V _ _ T S hfin hne hstab hcomm hnil
  set Z := jointNullChain T S with hZ
  have hsucc : ∀ m, Z (m + 1) = Z m ⊓ LinearMap.ker (T m) := fun m => rfl
  have hanti : Antitone Z := antitone_nat_of_succ_le (fun m => by rw [hsucc]; exact inf_le_left)
  have hleS : ∀ m, Z m ≤ S := fun m => hanti (Nat.zero_le m)
  have hst : ∀ m l, ∀ v ∈ Z m, T l v ∈ Z m := by
    intro m
    induction m with
    | zero => exact fun l v hv => hstab l v hv
    | succ m ih =>
      intro l v hv
      rw [hsucc] at hv ⊢
      refine ⟨ih l v hv.1, ?_⟩
      have h0 : T m v = 0 := hv.2
      show T m (T l v) = 0
      have := LinearMap.congr_fun (hcomm m l).eq v
      simp only [Module.End.mul_apply] at this
      rw [this, h0, map_zero]
  have hstpow : ∀ m l i, ∀ v ∈ Z m, (T l ^ i) v ∈ Z m := by
    intro m l i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hst m l _ (ih v hv)
  have hkill : ∀ m, ∀ k < m, ∀ v ∈ Z m, T k v = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk v hv
      rw [hsucc] at hv
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact ih k hk v hv.1
      · subst hk; exact hv.2
  have hnebot : ∀ m, Z m ≠ ⊥ := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih =>
      obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp ih
      have hex : ∃ N : ℕ, (T m ^ N) w = 0 := hnil m w (hleS m hw)
      classical
      set N0 := Nat.find hex with hN0
      have hN0spec : (T m ^ N0) w = 0 := Nat.find_spec hex
      have hN0pos : N0 ≠ 0 := by
        intro h
        rw [h, pow_zero, Module.End.one_apply] at hN0spec
        exact hw0 hN0spec
      obtain ⟨i, hi⟩ : ∃ i, N0 = i + 1 := ⟨N0 - 1, by omega⟩
      have hne0 : (T m ^ i) w ≠ 0 := Nat.find_min hex (by omega)
      rw [Submodule.ne_bot_iff]
      refine ⟨(T m ^ i) w, ?_, hne0⟩
      rw [hsucc]
      refine ⟨hstpow m m i w hw, ?_⟩
      show T m ((T m ^ i) w) = 0
      rw [← Module.End.mul_apply, ← pow_succ', ← hi, hN0spec]
  have hfinZ : ∀ m, FiniteDimensional ℂ (Z m) := fun m => Submodule.finiteDimensional_of_le (hleS m)
  let f : ℕ → ℕ := fun m => Module.finrank ℂ (Z m)
  have hexc : ∃ c, ∃ m, f m = c := ⟨_, 0, rfl⟩
  classical
  obtain ⟨M, hM⟩ := Nat.find_spec hexc
  have hmin : ∀ m, Nat.find hexc ≤ f m := fun m => Nat.find_min' hexc ⟨m, rfl⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp (hnebot M)
  refine ⟨w, hleS M hw, hw0, fun k => ?_⟩
  rcases lt_or_ge k M with hk | hk
  · exact hkill M k hk w hw
  · have hle : Z (k + 1) ≤ Z M := hanti (by omega)
    have heq : Z (k + 1) = Z M := by
      haveI := hfinZ M
      apply Submodule.eq_of_le_of_finrank_eq hle
      have h1 := hmin (k + 1)
      have h2 : f (k + 1) ≤ f M := Submodule.finrank_mono hle
      have h3 : f M = Nat.find hexc := hM
      show f (k + 1) = f M
      omega
    exact hkill (k + 1) k (Nat.lt_succ_self k) w (heq ▸ hw)

end GlobalTheory
