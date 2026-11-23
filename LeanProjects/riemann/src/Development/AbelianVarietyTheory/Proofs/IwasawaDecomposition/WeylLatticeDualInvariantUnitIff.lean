import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DelWSub

def intBall (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem eval_rowAct {R : Type} [CommRing R] {N : ℕ} (G Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.eval (fun k => Y k.1 k.2) (Formalism.GradedWeylDivisibility.rowAct R G P) =
      MvPolynomial.eval (fun k => (G * Y) k.1 k.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl ℤ N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν := rfl

theorem rowSub_expand (p : ℕ) [Fact p.Prime] {N : ℕ} (ν : Fin N → ℕ)
    (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    ∃ (s : Finset (List (Fin N × Fin N × ℕ))) (o : List (Fin N × Fin N × ℕ) → ℂ_[p]),
      (∀ w, ‖o w‖ ≤ 1) ∧ ∀ Y : Matrix (Fin N) (Fin N) ℂ_[p],
        MvPolynomial.eval (fun k => (g * Y) k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) f) =
          ∑ w ∈ s, o w * MvPolynomial.eval (fun k => Y k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
            (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν))) := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hgO : gO.map O.subtype = g := by ext a b; rfl
  have hfO : MvPolynomial.map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl ν :=
    GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom O) le_rfl ν f (by rw [← weyl_eq]; exact hf)
  have hQ := GlobalTheory.WeylRowAll.rowAct_mem_weyl O le_rfl ν gO _ hfO
  unfold Formalism.GradedWeylDivisibility.weyl at hQ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hQ
  refine ⟨c.support, fun w => (c w : ℂ_[p]), fun w => (c w).2, fun Y => ?_⟩
  have h1 : MvPolynomial.map (Int.castRingHom ℂ_[p]) f =
      MvPolynomial.map O.subtype (MvPolynomial.map (Int.castRingHom O) f) := by
    rw [MvPolynomial.map_map]; congr 1
  have hterm : ∀ w, MvPolynomial.map O.subtype (Formalism.GradedWeylDivisibility.applyWord O w (Formalism.GradedWeylDivisibility.hw O le_rfl ν)) =
      MvPolynomial.map (Int.castRingHom ℂ_[p])
        (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν)) := by
    intro w
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    show _ = MvPolynomial.map _ (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl ν))
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  rw [h1, ← eval_rowAct, ← hgO, ← GlobalTheory.WeylRowAll.map_rowAct, ← hc, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hterm]
  rfl

def act (p : ℕ) [Fact p.Prime] (T : Type) (N : ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) :
    ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) →+ ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) where
  toFun F := fun y => c * F (fun τ => g τ * y τ)
  map_zero' := by funext y; simp
  map_add' F G := by funext y; simp [mul_add]

theorem mem_delW_act (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  classical
  refine (AddSubgroup.closure_le ((WeylLatticeDuality.DelW p T N ν).comap (act p T N g c))).2 ?_ hF
  rintro _ ⟨r, f, hr, hf, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  choose s o ho hexp using fun τ => rowSub_expand p (ν τ) (g τ) (hg τ) (f τ) (hf τ)
  have heq : act p T N g c (fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) =
      ∑ x ∈ Fintype.piFinset s, fun y => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
          (WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)))) := by
    funext y
    rw [Finset.sum_apply]
    show c * (r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) = _
    simp only [hexp]
    rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.subset_closure
    ⟨c * r * ∏ τ, o τ (x τ), fun τ => WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)),
      ?_, fun τ => Submodule.subset_span ⟨x τ, rfl⟩, rfl⟩
  rw [norm_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)

theorem exists_int_inv (p : ℕ) [Fact p.Prime] {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ_[p])
    (hg : ∀ a b, ‖g a b‖ ≤ 1) (hdet : ‖g.det‖ = 1) :
    ∃ h : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖h a b‖ ≤ 1) ∧ g * h = 1 := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hmap : gO.map O.subtype = g := by ext a b; rfl
  have hd : O.subtype gO.det = g.det := by rw [RingHom.map_det]; rfl
  have hdne : g.det ≠ 0 := norm_ne_zero_iff.1 (by rw [hdet]; exact one_ne_zero)
  have hu : IsUnit gO.det := by
    refine IsUnit.of_mul_eq_one (⟨g.det⁻¹, ?_⟩ : O) ?_
    · show ‖g.det⁻¹‖ ≤ 1
      rw [norm_inv, hdet, inv_one]
    · apply Subtype.ext
      show O.subtype gO.det * g.det⁻¹ = 1
      rw [hd, mul_inv_cancel₀ hdne]
  refine ⟨gO⁻¹.map O.subtype, fun a b => (gO⁻¹ a b).2, ?_⟩
  rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem delW_rowSub : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  intro p _ T _ N ν g c hg hdet hc F
  constructor
  · exact mem_delW_act p T N ν g c hg hc.le F
  · intro h
    have hinv := fun τ => exists_int_inv p (g τ) (hg τ) (hdet τ)
    choose hm hmI hmul using hinv
    have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
    have := mem_delW_act p T N ν hm c⁻¹ hmI (by rw [norm_inv, hc, inv_one]) _ h
    convert this using 1
    funext y
    simp only [← Matrix.mul_assoc, hmul, Matrix.one_mul]
    rw [inv_mul_cancel_left₀ hc0]

end GlobalTheory.DelWSub
