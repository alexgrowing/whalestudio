import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.eventually_isGenerated_tens_lbPow {X : Scheme.{0}} {A N : LB X} (hA : IsAmpleLB A)
    (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsGenerated (tens N (lbPow A n)) := by
  have := isFiniteQC_twist (F := GlobalTheory.structureModule X) hN
  refine (hA.eventually_isGloballyGenerated_twist (twist (GlobalTheory.structureModule X) N)).mono
    fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hT := isLB_tens hN hP
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule X) hN hP hT
    (cls_tens hN hP hT)
  exact (isGloballyGenerated_toMod_iff hT).1 ((hn.of_epi e.hom).of_epi (unitTwistIso _).hom)

theorem IsAmpleLB.eventually_isAmpleLB_tens_lbPow_succ {X : Scheme.{0}} {A N : LB X}
    (hA : IsAmpleLB A) (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsAmpleLB (tens N (lbPow A (n + 1))) := by
  refine (hA.eventually_isGenerated_tens_lbPow hN).mono fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hP' := isLB_lbPow hA.isLB (n + 1)
  have hT := isLB_tens hN hP'
  have hD := LB.isLB_div hT hA.isLB
  refine hA.tensor_isGenerated hn hT ((cls_eq_zero_iff (LB.isLB_div hD hn.isLB)).1 ?_)
  rw [cls_div hD hn.isLB, cls_div hT hA.isLB, cls_tens hN hP', cls_tens hN hP,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB, succ_nsmul]
  abel

theorem exists_isAmpleLB_tens_lbPow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ A N : LB X, IsAmpleLB A → N.IsLB → ∃ c : ℕ, 1 ≤ c ∧ IsAmpleLB (tens N (lbPow A c)) := by
  intro k _ _ X _ _ A N hA hN
  obtain ⟨n, hn⟩ := (hA.eventually_isAmpleLB_tens_lbPow_succ hN).exists
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end GlobalTheory
