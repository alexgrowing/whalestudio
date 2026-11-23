import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SemilinearOfAdditive
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesTens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.FlagDomainConjHostXiEqNeg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rtW_dvd (k : ℕ) : rtW l (k + 2) ^ 3 ∣ rtW l k ∧ (rtW l k).coeff 0 = rt l k := by
  refine ⟨?_, WittVector.teichmuller_coeff_zero l _⟩
  have h := (isRt_rt l).1
  have e : rt l k = rt l (k + 2) ^ (l * l) := by rw [pow_mul, h (k + 1), h k]
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl : 3 ≤ l * l := by nlinarith
  refine ⟨WittVector.teichmuller l (rt l (k + 2) ^ (l * l - 3)), ?_⟩
  rw [rtW, rtW, e, ← map_pow, ← map_mul, ← pow_add, Nat.add_sub_cancel' hl]

theorem des_Un_one (h : ObFacts l) (hU : RU l) (k : ℕ) : Des (UnF l 1) (rtW l k) := by
  have hd := des_tens l h (Ob l ⧸ Ideal.span {pFlat l}) 1 (fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (pFlat l ^ 1 * y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (by rw [pow_one]; exact Ideal.mem_span_singleton_self _))) k
  have hn : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
      tau1 B (((UnF l 1).map f).hom x) = ((toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l})).map f).hom (tau1 A x) := by
    intro A B f x
    obtain ⟨w, rfl⟩ := un_rep x
    have e : ((UnF l 1).map f).hom (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (B.th (PAlg.mapW f w)) := rfl
    rw [e, tau1_mk, tau1_mk, PAlg.mapW, WittVector.map_coeff]
    rfl
  refine (des_semi WittVector.constantCoeff (testι l) (UnF l 1) (toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l}))
    (fun A => tau1 A) (fun A a x => tau1_smul A a x) (fun A => tau1_bijective A hU) hn (rtW l k)).2 ?_
  change DesJ _ _ ((rtW l k).coeff 0)
  rw [(rtW_dvd l k).2]
  exact hd

theorem des_Un (h : ObFacts l) (hU : RU l) (n k : ℕ) : Des (UnF l n) (rtW l k) := by
  induction n generalizing k with
  | zero =>
    refine des_span (testι l) (UnF l 0) {rtW l k} (fun a _ => Or.inr fun A x => ?_) _ (Ideal.subset_span rfl)
    have hz : ∀ z : A.Un 0, z = 0 := fun z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_zero, Ideal.span_singleton_one]; trivial)
    exact hz _
  | succ n ih =>
    have hα : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l 1).obj A),
        (mulQ (l : A.U) n).toAddMonoidHom (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a • (mulQ (l : A.U) n).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change mulQ (l : A.U) n (a • Ideal.Quotient.mk _ u) = a • mulQ (l : A.U) n (Ideal.Quotient.mk _ u)
      rw [algebra_compatible_smul A.U a, LinearMap.map_smul, ← algebra_compatible_smul]
    have hβ : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom
          (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a •
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have nα : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
        (mulQ (l : B.U) n).toAddMonoidHom (((UnF l 1).map f).hom x) = ((UnF l (n + 1)).map f).hom ((mulQ (l : A.U) n).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ ((l : B.U) ^ n * PAlg.mapU f u) = Ideal.Quotient.mk _ (PAlg.mapU f ((l : A.U) ^ n * u))
      rw [map_mul (PAlg.mapU f), map_pow (PAlg.mapU f), map_natCast (PAlg.mapU f)]
    have nβ : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : B.U) n.le_succ))).toAddMonoidHom
          (((UnF l (n + 1)).map f).hom x) = ((UnF l n).map f).hom
        ((Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have key := (des_ses (RingHom.id (Ainf l)) (RingHom.id _) (RingHom.id _) (testι l) (UnF l 1) (UnF l (n + 1)) (UnF l n)
      (fun A => (mulQ (l : A.U) n).toAddMonoidHom)
      (fun A => (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom)
      hα hβ nα nβ (fun A => mulQ_inj _ (hU A).1 n) (fun A => mulQ_exact _ n)
      (fun A y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ z, rfl⟩) (rtW l (k + 2))).1
      (des_Un_one l h hU (k + 2)) (ih (k + 2))
    exact des_span (testι l) (UnF l (n + 1)) {rtW l (k + 2) ^ 3}
      (fun a ha => Or.inl (by rw [Set.mem_singleton_iff.1 ha]; exact key)) _ (Ideal.mem_span_singleton.2 (rtW_dvd l k).1)

theorem wm_span (h : ObFacts l) (s : Ainf l) (hs : InWm l s) (n : ℕ) :
    s ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) := by
  obtain ⟨_, _, _, h4⟩ := h
  have hr : ∀ k, rtW l k ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hl : (l : Ainf l) ^ n ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    Ideal.subset_span (Set.mem_insert _ _)
  cases n with
  | zero =>
    rw [Ideal.eq_top_of_isUnit_mem _ hl (by rw [pow_zero]; exact isUnit_one)]
    exact Submodule.mem_top
  | succ m =>
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff s m
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    refine add_mem (Ideal.mul_mem_right _ _ hl) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
    have hnu : ¬ IsUnit (((frobeniusEquiv (Ob l) l).symm ^ i) (s.coeff i)) := fun hu =>
      hs i ((isUnit_map_iff ((frobeniusEquiv (Ob l) l).symm ^ i) _).1 hu)
    obtain ⟨k, d, hd⟩ := h4 _ hnu
    rw [hd, map_mul]
    exact Ideal.mul_mem_right _ _ (hr k)

end CrystallineSemistableComparison.D
