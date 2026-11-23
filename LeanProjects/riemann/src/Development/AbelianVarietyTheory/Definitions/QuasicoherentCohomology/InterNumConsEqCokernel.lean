import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.InterModel

variable {X Z : Scheme.{0}} {k : Type} [Field k] [Algebra k Γ(X, ⊤)]

def cut (F : X.Modules) {M : LB X} (hM : M.IsLB) (σ : LB.Sec M) : twistZ F M (-1) ⟶ F :=
  Twist.mulSecOfEq F (Twist.zofSec σ) (neg_add_cancel 1) ≫ (Twist.twistZZeroIso F hM).inv

theorem interNum_cons_eq_cokernel (F : X.Modules) {M : LB X} (hM : M.IsLB) (σ : LB.Sec M)
    [Mono (cut F hM σ)] (hF : FiniteCohTwists k F) {d : ℕ} {P : Fin d → LB X}
    (hP : ∀ i, (P i).IsLB) :
    interNum k F (Fin.cons M P : Fin (d + 1) → LB X) = interNum k (cokernel (cut F hM σ)) P := by
  rw [interNum_cons k F hM hP,
    interNum_cokernel _ hP (hF.twist (Twist.isLB_lbZPow hM (-1))) hF]

theorem interNum_one_eq_hdim (F : X.Modules) {M : LB X} (hM : M.IsLB) (σ : LB.Sec M)
    [Mono (cut F hM σ)] (hF : FiniteCohTwists k F)
    (h : ∀ n, 0 < n → Subsingleton (coh (cokernel (cut F hM σ)) n)) :
    interNum k F ![M] = hdim k (cokernel (cut F hM σ)) 0 :=
  (interNum_cons_eq_cokernel F hM σ hF (P := ![]) isEmptyElim).trans
    ((interNum_of_isEmpty k _ _).trans (chi_eq_hdim_zero k h))

variable (k) {ι : Type} [Fintype ι]

theorem interNumSub_bot (L : ι → LB X) :
    interNumSub k ⊥ L = interNum k (structureModule X) L := by
  rw [← interNumOn_id, interNumOn_eq_interNumSub]
  congr 1
  exact (Scheme.Hom.ker_eq_bot_of_isIso _).symm

theorem radical_ker (f : Z ⟶ X) [QuasiCompact f] [IsReduced Z] : f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun a ⟨n, hn⟩ => ?_
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem interNumRed_eq_interNumOn (f : Z ⟶ X) [IsClosedImmersion f] [IsReduced Z]
    (C : Closeds X) (h : Set.range f = C) (L : ι → LB X) :
    interNumRed k C L = interNumOn k f L := by
  rw [interNumOn_eq_interNumSub, interNumRed_def, ← radical_ker f,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 2
  ext1
  rw [Scheme.Hom.support_ker, h, C.isClosed.closure_eq]

theorem isZero_of_isEmpty [IsEmpty X] (F : X.Modules) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have : U = ⊥ := Subsingleton.elim _ _
  subst this
  have : Subsingleton Γ(X, ⊥) := inferInstance
  have := Module.subsingleton Γ(X, ⊥) Γ(F, ⊥)
  exact Subsingleton.elim _ _

theorem interNumSub_top {L : ι → LB X} (hL : ∀ i, (L i).IsLB) : interNumSub k ⊤ L = 0 := by
  have : IsEmpty (⊤ : X.IdealSheafData).subscheme := inferInstance
  exact interNum_eq_zero_of_isZero k (Functor.map_isZero _ (isZero_of_isEmpty _)) hL

theorem interNumRed_bot {L : ι → LB X} (hL : ∀ i, (L i).IsLB) : interNumRed k ⊥ L = 0 := by
  rw [interNumRed_def, Scheme.IdealSheafData.vanishingIdeal_bot, interNumSub_top k hL]

theorem plane_values (F : X.Modules) {M : LB X} (hM : M.IsLB)
    (h : ∀ n : ℤ, 2 * chi k (twistZ F M n) = (n + 1) * (n + 2)) :
    interNum k F (fun _ : Fin 2 ↦ M) = 1 ∧ interNum k F (fun _ : Fin 3 ↦ M) = 0 ∧
      interNum k F (fun _ : Fin 1 ↦ M) = 1 := by
  have h0 := h 0
  have h1 := h (-1)
  have h2 := h (-2)
  have h3 := h (-3)
  simp only [interNum_const_eq_sum k F hM, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose] at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem dualNumber_example :
    letI := algebraΓSpecOf k (.of (DualNumber k))
    interNumSub k ⊥ (![] : Fin 0 → LB (Spec (.of (DualNumber k)))) = 2 ∧
    interNumRed k ⊤ (![] : Fin 0 → LB (Spec (.of (DualNumber k)))) = 1 := by
  letI := algebraΓSpecOf k (.of (DualNumber k))
  have := isScalarTower_algebraΓSpecOf k (.of (DualNumber k))
  letI := algebraΓSpecOf k (.of k)
  have := isScalarTower_algebraΓSpecOf k (.of k)
  constructor
  · rw [interNumSub_bot, interNum_of_isEmpty, chi_structureModule_Spec]
    have : Module.finrank k (k × k) = 2 := by simp
    exact congrArg Nat.cast this
  · let φ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
    have hφ : Function.Surjective φ := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
    have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
    rw [interNumRed_eq_interNumOn k (Spec.map φ) ⊤ ?_, interNumOn_eq_interNum_pull ?_ isEmptyElim,
      interNum_of_isEmpty, chi_structureModule_Spec]
    · simp
    · intro r
      have := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) (algebraMap k _ r)
      refine this.symm.trans ?_
      exact congrArg (Scheme.ΓSpecIso (.of k)).inv ((TrivSqZeroExt.fstHom k k k).commutes r)
    · have : Subsingleton (PrimeSpectrum (DualNumber k)) := by
        have key (p : PrimeSpectrum (DualNumber k)) :
            Ideal.span {DualNumber.eps} = p.asIdeal :=
          DualNumber.isMaximal_span_singleton_eps.eq_of_le p.isPrime.ne_top
            ((Ideal.span_singleton_le_iff_mem _).2 (p.isPrime.mem_of_pow_mem 2
              (by rw [pow_two, DualNumber.eps_mul_eps]; exact zero_mem _)))
        exact ⟨fun p q => PrimeSpectrum.ext ((key p).symm.trans (key q))⟩
      have : Subsingleton (Spec (.of (DualNumber k)) : Scheme) := this
      refine Set.eq_univ_of_forall fun x => ⟨(default : PrimeSpectrum k), Subsingleton.elim _ _⟩

end GlobalTheory.InterModel
