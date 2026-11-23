import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem mulR_mulR (a b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V a (mulR ℚ_[l] P.R.BdR LL V b x) = mulR ℚ_[l] P.R.BdR LL V (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp [mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem mulR_neg (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V (-a) x = -mulR ℚ_[l] P.R.BdR LL V a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, neg_zero]
  | tmul v c => simp [tmul_neg]
  | add y z hy hz => simp only [map_add, hy, hz, neg_add]

private theorem mulR_one (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem act_mulR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K) ρ g (mulR ℚ_[l] P.R.BdR LL V a x) =
      mulR ℚ_[l] P.R.BdR LL V ((P.PD K).actdR g a) (actVdR (P.PD K) ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private def spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) :
    AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR) where
  carrier := {y | ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
    (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, mulR ℚ_[l] P.R.BdR LL V (b i) (d i)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, b, d, hd, rfl⟩ ⟨n, b', d', hd', rfl⟩
    refine ⟨m + n, Fin.append b b', Fin.append d d', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hd j
      · rw [Fin.append_right]; exact hd' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  neg_mem' := by
    rintro _ ⟨m, b, d, hd, rfl⟩
    refine ⟨m, fun i => -b i, d, hd, ?_⟩
    simp only [mulR_neg, Finset.sum_neg_distrib]

private theorem mulR_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (a : P.R.BdR)
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    mulR ℚ_[l] P.R.BdR LL V a x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => a * b i, d, hd, ?_⟩
  simp only [map_sum, mulR_mulR]

private theorem act_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    actVdR (P.PD K) ρ g x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => (P.PD K).actdR g (b i), d, hd, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act_mulR, (mem_DdR (P.PD K) ρ _).1 (hd i)]

private theorem mem_spanD_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1)
    (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ spanD P K ρ := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine JumpDescent.descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulR ℚ_[l] P.R.BdR LL V (algebraMap (Om l) P.R.BdR c)).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    ⊤ (spanD P K ρ) (fun _ _ _ => trivial) (fun _ _ _ => trivial) (act_mem_spanD P K ρ)
    (fun c => mulR_mem_spanD P K ρ _)
    (fun y _ hy' => ⟨1, fun _ => 1, fun _ => y, fun _ => (mem_DdR (P.PD K) ρ y).2 hy', by
      simp only [mulR_one, Fin.sum_univ_one]⟩) x trivial ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro x
    simp only [map_one, LinearMap.toAddMonoidHom_coe, mulR_one]
  · intro g g' x
    simp only [map_mul, LinearMap.toAddMonoidHom_coe, mulR_mulR]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [add_mul, tmul_add]
    | add y z hy hz => simp only [map_add] at hy hz ⊢; rw [hy, hz]; abel
  · intro g c x
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [act_mulR, P.PD_actdR, P.actQdR_Om]
    rfl
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR (P.PD K') _ x).1 hxH ⟨g.1, hg⟩
    rw [JumpDescent.actVdR_comp P h] at this
    exact this

end

theorem spans_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V),
    Spans (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) → Spans (P.PD K) ρ := by
  intro l _ P K K' LL h V _ _ _ _ ρ hs y
  obtain ⟨m, b, d, hd, rfl⟩ := hs y
  exact (spanD P K ρ).sum_mem fun i _ =>
    mulR_mem_spanD P K ρ _ _ (mem_spanD_of_fixed P h ρ _ (hd i))

end GlobalTheory.DRFil
