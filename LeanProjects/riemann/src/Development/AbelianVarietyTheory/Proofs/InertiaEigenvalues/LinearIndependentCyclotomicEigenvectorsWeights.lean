import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsTwist
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem actC_apply_eq_σC {l : ℕ} [Fact l.Prime] (g : GQ l) (y : ℂ_[l]) :
    GlobalTheory.Cyc.Model.actC g y = Formalism.Per.σC g y := by
  change GlobalTheory.Cyc.Model.extHom g y = Formalism.Per.σC g y
  have hc : Continuous (Formalism.Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (GlobalTheory.Cyc.Model.extHom_cont g) hc
  | ih x => exact (GlobalTheory.Cyc.Model.extHom_coe g x).trans (GlobalTheory.RingBasics.σC_coe g x).symm

theorem linIndep_of_eigen_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  intro l _ P n _ _ K A ι _ v w hA hK
  classical

  set e : GQ l → ℤ → ℂ_[l] := fun g k => algebraMap ℚ_[l] ℂ_[l] ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) with he
  have e_ne : ∀ g k, e g k ≠ 0 := fun g k => by
    simp only [he, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ℂ_[l]).injective, Units.ne_zero,
      not_false_eq_true]
  have e_sub : ∀ g (a b : ℤ), e g (a - b) * e g b = e g a := fun g a b => by
    simp only [he, ← map_mul, ← Units.val_mul, ← zpow_add, sub_add_cancel]
  have hcyc : GlobalTheory.Cyc.IsCyc P.χQ := P.χQ_cyc
  rw [Fintype.linearIndependent_iff]
  suffices key : ∀ m : ℕ, ∀ a : ι → ℂ_[l], (Finset.univ.filter (fun j => a j ≠ 0)).card = m →
      ∑ j, a j • v j = 0 → a = 0 by
    intro a ha j
    exact congrFun (key _ a rfl ha) j
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hcard hrel
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j0, a j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set b : ι → ℂ_[l] := fun j => (a j0)⁻¹ * a j with hb
  have hbrel : ∑ j, b j • v j = 0 := by
    simp only [hb, mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hb0 : b j0 = 1 := by simp only [hb, inv_mul_cancel₀ hj0]
  have hsupp : ∀ j, b j ≠ 0 ↔ a j ≠ 0 := fun j => by
    simp only [hb, ne_eq, mul_eq_zero, inv_eq_zero, hj0, false_or]

  have htw : ∀ g : ↥(GK K), ∀ j, Formalism.Per.σC (g : GQ l) (b j) * e g (w j) = e g (w j0) * b j := by
    intro g
    have h1 : (∑ j, Formalism.Per.σC (g : GQ l) (b j) • (fun i => Formalism.Per.σC (g : GQ l) (v j i))) = 0 := by
      funext i
      have hi := congrFun hbrel i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [← map_zero (Formalism.Per.σC (g : GQ l)), ← hi, map_sum]
      simp only [map_mul]
    have h2 : ∑ j, (Formalism.Per.σC (g : GQ l) (b j) * e g (w j)) • v j = 0 := by
      have := congrArg (fun u => (A g).mulVec u) h1
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.mulVec_zero, smul_smul] at this
      exact this
    set d : ι → ℂ_[l] := fun j => Formalism.Per.σC (g : GQ l) (b j) * e g (w j) - e g (w j0) * b j with hd
    have hdrel : ∑ j, d j • v j = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib]
      rw [h2]
      simp only [mul_smul, ← Finset.smul_sum, hbrel, smul_zero, sub_zero]
    have hdsub : Finset.univ.filter (fun j => d j ≠ 0) ⊆ (Finset.univ.filter (fun j => a j ≠ 0)).erase j0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hj
        simp only [hd, hb0, map_one, one_mul, mul_one, sub_self]
      · rw [← hsupp]
        intro hbj
        apply hj
        simp only [hd, hbj, map_zero, zero_mul, mul_zero, sub_self]
    have hlt : (Finset.univ.filter (fun j => d j ≠ 0)).card < m := by
      rw [← hcard]
      refine lt_of_le_of_lt (Finset.card_le_card hdsub) (Finset.card_erase_lt_of_mem ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj0
    have hd0 := ih _ hlt d rfl hdrel
    intro j
    exact sub_eq_zero.1 (congrFun hd0 j)

  have hin : ∀ j, ∃ x : Om l, x ∈ K.1 ∧ (x : ℂ_[l]) = b j ∧ (w j ≠ w j0 → x = 0) := by
    intro j
    have hfix : ∀ g ∈ GK K, GlobalTheory.Cyc.chiC P.χQ (w j - w j0) g * GlobalTheory.Cyc.Model.actC g (b j) = b j := by
      intro g hg
      rw [actC_apply_eq_σC]
      have h := htw ⟨g, hg⟩ j
      change Formalism.Per.σC g (b j) * e g (w j) = e g (w j0) * b j at h
      change e g (w j - w j0) * Formalism.Per.σC g (b j) = b j
      apply mul_left_cancel₀ (e_ne g (w j0))
      rw [← h, ← e_sub g (w j) (w j0)]
      ring
    have hT := GlobalTheory.Cyc.tate_invariants_twist l GlobalTheory.Cyc.Model.actC P.χQ GlobalTheory.Cyc.Model.isActC_actC hcyc K
      (w j - w j0) (b j) hfix
    by_cases hw : w j = w j0
    · obtain ⟨x, hxK, hx⟩ := hT.2 (sub_eq_zero.2 hw)
      exact ⟨x, hxK, hx, fun h => absurd hw h⟩
    · have hbj : b j = 0 := hT.1 (sub_ne_zero.2 hw)
      exact ⟨0, K.1.zero_mem, by rw [hbj]; exact UniformSpace.Completion.coe_zero, fun _ => rfl⟩
  choose c hcK hcb hc0 using hin
  have hc : c = 0 := hK (w j0) c hcK hc0 (by simp only [hcb]; exact hbrel)
  have : b j0 = 0 := by rw [← hcb j0, hc, Pi.zero_apply]; exact UniformSpace.Completion.coe_zero
  rw [hb0] at this
  exact one_ne_zero this

end GlobalTheory.PMon
