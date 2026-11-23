import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Tri

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def pairs (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : AddSubgroup (V × V) where
  carrier := {p | p.1 ∈ Λ₃ ∧ p.2 ∈ Λ₂ ∧ p.1 + p.2 ∈ Λ₁}
  zero_mem' := ⟨Λ₃.zero_mem, Λ₂.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨Λ₃.add_mem a1 b1, Λ₂.add_mem a2 b2, ?_⟩
    have h := Λ₁.add_mem a3 b3
    simp only [Prod.fst_add, Prod.snd_add]
    convert h using 1; abel
  neg_mem' := by
    rintro a ⟨a1, a2, a3⟩
    refine ⟨Λ₃.neg_mem a1, Λ₂.neg_mem a2, ?_⟩
    have h := Λ₁.neg_mem a3
    simp only [Prod.fst_neg, Prod.snd_neg]
    convert h using 1; abel

def triv (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : AddSubgroup (V × V) where
  carrier := {p | p.1 ∈ Λ₂ ⊓ Λ₃ ∧ p.1 + p.2 ∈ Λ₁ ⊓ Λ₂}
  zero_mem' := ⟨(Λ₂ ⊓ Λ₃).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨a1, a3⟩ ⟨b1, b3⟩
    refine ⟨(Λ₂ ⊓ Λ₃).add_mem a1 b1, ?_⟩
    have h := (Λ₁ ⊓ Λ₂).add_mem a3 b3
    simp only [Prod.fst_add, Prod.snd_add]
    convert h using 1; abel
  neg_mem' := by
    rintro a ⟨a1, a3⟩
    refine ⟨(Λ₂ ⊓ Λ₃).neg_mem a1, ?_⟩
    have h := (Λ₁ ⊓ Λ₂).neg_mem a3
    simp only [Prod.fst_neg, Prod.snd_neg]
    convert h using 1; abel

abbrev Quo (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : Type :=
  pairs Λ₁ Λ₂ Λ₃ ⧸ (triv Λ₁ Λ₂ Λ₃).addSubgroupOf (pairs Λ₁ Λ₂ Λ₃)

def phi (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) (c : Quo Λ₁ Λ₂ Λ₃) : ℂ :=
  psiT H α (Quotient.out c : pairs Λ₁ Λ₂ Λ₃).1.1 (Quotient.out c : pairs Λ₁ Λ₂ Λ₃).1.2

theorem phi_mk {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ Λ₃ : AddSubgroup V}
    (h4 : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ u' ∈ Λ₁ ⊓ Λ₃, ∀ u ∈ Λ₁ ⊓ Λ₂, ∀ t ∈ Λ₂ ⊓ Λ₃,
      psiT H α (z + u' + t) (y + u - t) = psiT H α z y) (p : pairs Λ₁ Λ₂ Λ₃) :
    phi H α Λ₁ Λ₂ Λ₃ (QuotientAddGroup.mk p) = psiT H α p.1.1 p.1.2 := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add ((triv Λ₁ Λ₂ Λ₃).addSubgroupOf (pairs Λ₁ Λ₂ Λ₃)) p
  have hm : (h.1.1 : V × V) ∈ triv Λ₁ Λ₂ Λ₃ := AddSubgroup.mem_addSubgroupOf.1 h.2
  obtain ⟨p1, p2, p3⟩ := p.2
  have key := h4 p.1.1 p1 p.1.2 p2 p3 0 (Λ₁ ⊓ Λ₃).zero_mem _ hm.2 _ hm.1
  unfold phi
  rw [hh, ← key]
  congr 1
  · simp
  · simp only [AddSubgroup.coe_add, Prod.snd_add]; abel

def idx (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) : Finset (V × V) := by
  classical exact (S₃ ×ˢ S₂).filter fun p => p.1 + p.2 ∈ Λ₁

theorem mem_idx {Λ₁ : AddSubgroup V} {S₂ S₃ : Finset V} {p : V × V} :
    p ∈ idx Λ₁ S₂ S₃ ↔ p.1 ∈ S₃ ∧ p.2 ∈ S₂ ∧ p.1 + p.2 ∈ Λ₁ := by
  classical
  simp [idx, and_assoc]

theorem tripleSum_eq (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) :
    tripleSum H α Λ₁ S₂ S₃ = ∑ p ∈ idx Λ₁ S₂ S₃, psiT H α p.1 p.2 := by
  classical
  unfold tripleSum idx
  rw [Finset.sum_filter, Finset.sum_product]

theorem idx_pairs {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) {p : V × V} (hp : p ∈ idx Λ₁ S₂ S₃) : p ∈ pairs Λ₁ Λ₂ Λ₃ := by
  obtain ⟨a, b, c⟩ := mem_idx.1 hp
  exact ⟨hS₃.1 _ a, hS₂.1 _ b, c⟩

theorem mk_eq_iff {Λ₁ Λ₂ Λ₃ : AddSubgroup V} (p q : pairs Λ₁ Λ₂ Λ₃) :
    (QuotientAddGroup.mk p : Quo Λ₁ Λ₂ Λ₃) = QuotientAddGroup.mk q ↔ p.1 - q.1 ∈ triv Λ₁ Λ₂ Λ₃ := by
  rw [eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : ((-q + p : pairs Λ₁ Λ₂ Λ₃) : V × V) = p.1 - q.1 := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
  rw [this]

theorem idx_inj {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) {p q : V × V} (hp : p ∈ idx Λ₁ S₂ S₃) (hq : q ∈ idx Λ₁ S₂ S₃)
    (h : p - q ∈ triv Λ₁ Λ₂ Λ₃) : p = q := by
  obtain ⟨a, b, _⟩ := mem_idx.1 hp
  obtain ⟨a', b', _⟩ := mem_idx.1 hq
  obtain ⟨h1, h2⟩ := h
  have e1 : p.1 = q.1 := hS₃.2.1 _ a _ a' h1.1
  have e2 : p.2 = q.2 := by
    refine hS₂.2.1 _ b _ b' ?_
    have := h2.1
    simpa [e1] using this
  exact Prod.ext e1 e2

theorem idx_surj {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) {p : V × V} (hp : p ∈ pairs Λ₁ Λ₂ Λ₃) :
    ∃ q ∈ idx Λ₁ S₂ S₃, q - p ∈ triv Λ₁ Λ₂ Λ₃ := by
  obtain ⟨p1, p2, p3⟩ := hp
  obtain ⟨s, hs, hst⟩ := hS₃.2.2 p.1 p1
  have ht3 : p.1 - s ∈ Λ₃ := Λ₃.sub_mem p1 (hS₃.1 _ hs)
  obtain ⟨s₂, hs₂, hsu⟩ := hS₂.2.2 (p.2 + (p.1 - s)) (Λ₂.add_mem p2 hst)
  have hu2 : p.2 + (p.1 - s) - s₂ ∈ Λ₂ := Λ₂.sub_mem (Λ₂.add_mem p2 hst) (hS₂.1 _ hs₂)
  have hsum : s + s₂ ∈ Λ₁ := by
    have := Λ₁.sub_mem p3 hsu
    convert this using 1; abel
  refine ⟨(s, s₂), mem_idx.2 ⟨hs, hs₂, hsum⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := Λ₂.neg_mem hst
    simpa using this
  · have := Λ₃.neg_mem ht3
    simpa using this
  · show (s - p.1) + (s₂ - p.2) ∈ Λ₁
    have e : (s - p.1) + (s₂ - p.2) = -(p.2 + (p.1 - s) - s₂) := by abel
    rw [e]; exact Λ₁.neg_mem hsu
  · show (s - p.1) + (s₂ - p.2) ∈ Λ₂
    have e : (s - p.1) + (s₂ - p.2) = -(p.2 + (p.1 - s) - s₂) := by abel
    rw [e]; exact Λ₂.neg_mem hu2

theorem quo_finite {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) : Finite (Quo Λ₁ Λ₂ Λ₃) := by
  refine Finite.of_surjective
    (fun q : idx Λ₁ S₂ S₃ => (QuotientAddGroup.mk ⟨q.1, idx_pairs hS₂ hS₃ q.2⟩ : Quo Λ₁ Λ₂ Λ₃)) ?_
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨q, hq, hqp⟩ := idx_surj hS₂ hS₃ p.2
    exact ⟨⟨q, hq⟩, (mk_eq_iff _ _).2 hqp⟩

theorem sum_phi {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ Λ₃ : AddSubgroup V}
    (h4 : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ u' ∈ Λ₁ ⊓ Λ₃, ∀ u ∈ Λ₁ ⊓ Λ₂, ∀ t ∈ Λ₂ ⊓ Λ₃,
      psiT H α (z + u' + t) (y + u - t) = psiT H α z y)
    {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂) (hS₃ : IsReps Λ₂ Λ₃ S₃) [Fintype (Quo Λ₁ Λ₂ Λ₃)] :
    tripleSum H α Λ₁ S₂ S₃ = ∑ c : Quo Λ₁ Λ₂ Λ₃, phi H α Λ₁ Λ₂ Λ₃ c := by
  rw [tripleSum_eq]
  refine Finset.sum_bij
    (fun q hq => (QuotientAddGroup.mk ⟨q, idx_pairs hS₂ hS₃ hq⟩ : Quo Λ₁ Λ₂ Λ₃))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro p hp q hq h
    exact idx_inj hS₂ hS₃ hp hq ((mk_eq_iff _ _).1 h)
  · intro c _
    induction c using QuotientAddGroup.induction_on with
    | H p =>
      obtain ⟨q, hq, hqp⟩ := idx_surj hS₂ hS₃ p.2
      exact ⟨q, hq, (mk_eq_iff _ _).2 hqp⟩
  · intro q hq
    rw [phi_mk h4]

end Tri

open Tri

theorem TripleSumEighth_of (hP : PsiQuadratic) (hG : GaussDegenerate) : TripleSumEighth := by
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hT S₂ S₃ hS₂ hS₃ hne
  obtain ⟨h1, h2, h3, h4⟩ := hP V H α Λ₁ Λ₂ Λ₃ hT
  have : Finite (Quo Λ₁ Λ₂ Λ₃) := quo_finite hS₂ hS₃
  let _ : Fintype (Quo Λ₁ Λ₂ Λ₃) := Fintype.ofFinite _
  rw [sum_phi h4 hS₂ hS₃] at hne ⊢
  have hφne : ∀ c, phi H α Λ₁ Λ₂ Λ₃ c ≠ 0 := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H p =>
      rw [phi_mk h4]
      intro h0
      have := h3 _ p.2.1 _ p.2.2.1 p.2.2.2
      rw [h0] at this
      simp at this
  have hb : ∀ p q : pairs Λ₁ Λ₂ Λ₃,
      phi H α Λ₁ Λ₂ Λ₃ (QuotientAddGroup.mk p + QuotientAddGroup.mk q)
        / (phi H α Λ₁ Λ₂ Λ₃ (QuotientAddGroup.mk p) * phi H α Λ₁ Λ₂ Λ₃ (QuotientAddGroup.mk q))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H p.1.2 q.1.1 : ℂ)) := by
    intro p q
    have hp := hφne (QuotientAddGroup.mk p)
    have hq := hφne (QuotientAddGroup.mk q)
    rw [div_eq_iff (mul_ne_zero hp hq), ← QuotientAddGroup.mk_add, phi_mk h4, phi_mk h4, phi_mk h4]
    have := h1 _ p.2.1 _ p.2.2.1 p.2.2.2 _ q.2.1 _ q.2.2.1 q.2.2.2
    simp only [AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add]
    rw [this]; ring
  refine hG (Quo Λ₁ Λ₂ Λ₃) (phi H α Λ₁ Λ₂ Λ₃)
    (fun c c' => phi H α Λ₁ Λ₂ Λ₃ (c + c') / (phi H α Λ₁ Λ₂ Λ₃ c * phi H α Λ₁ Λ₂ Λ₃ c')) ⟨?_, ?_, ?_, hφne⟩ hne
  · intro x y
    rw [mul_div_cancel₀ _ (mul_ne_zero (hφne x) (hφne y))]
  · intro x y z
    induction x using QuotientAddGroup.induction_on with
    | H p =>
    induction y using QuotientAddGroup.induction_on with
    | H q =>
    induction z using QuotientAddGroup.induction_on with
    | H r =>
      rw [← QuotientAddGroup.mk_add, hb, hb, hb, ← Complex.exp_add]
      congr 1
      simp only [AddSubgroup.coe_add, Prod.snd_add, Inv.altE_add_left]
      push_cast; ring
  · intro k x
    induction x using QuotientAddGroup.induction_on with
    | H p =>
      rw [← QuotientAddGroup.mk_nsmul, phi_mk h4, phi_mk h4]
      exact h2 _ p.2.1 _ p.2.2.1 p.2.2.2 k

theorem TripleData.swap {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ}
    {Λ₁ Λ₂ Λ₃ : AddSubgroup V} (h : TripleData H α Λ₁ Λ₂ Λ₃) : TripleData H α Λ₁ Λ₃ Λ₂ :=
  ⟨h.herm, h.sd₁, h.sd₃, h.sd₂, h.sc₁, h.sc₃, h.sc₂, h.i₁₃, h.i₃₁, h.i₁₂, h.i₂₁, h.i₃₂, h.i₂₃⟩

theorem TripleEighth_of (hF : TripleFormula) (hS : TripleSumEighth) (hC : TripleConj) : TripleEighth := by
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hT ⟨F, hFf, hF0⟩ S₂ S₃ hS₂ hS₃
  obtain ⟨S₃', hS₃'⟩ := (repsExist V Λ₁ Λ₃ hT.i₁₃).1
  obtain ⟨S₂', hS₂'⟩ := (repsExist V Λ₃ Λ₂ hT.i₃₂).1
  have hμ' : tripleMu H α Λ₁ Λ₃ Λ₂ S₃' S₂' = conj (tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃) :=
    hC V H α Λ₁ Λ₂ Λ₃ hT S₂ S₃ S₂' S₃' hS₂ hS₃ hS₃' hS₂'
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ := ⟨_, rfl⟩
  rw [← hμ] at hμ' ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = inter H α Λ₁ Λ₂ F := ⟨_, rfl⟩
  have hGf : G ∈ fixedBy H α Λ₂ := by
    rw [hG]; exact interFixed V H hT.herm Λ₁ Λ₂ α hT.sc₂ hT.i₁₂ F hFf
  have hG0 : G ≠ 0 := by
    intro h0
    apply hF0
    funext z
    have := interInv V H hT.herm Λ₁ Λ₂ α hT.sd₁ hT.sd₂ hT.sc₁ hT.sc₂ hT.i₁₂ hT.i₂₁ F hFf z
    rw [← hG, h0, Inv.inter_zero] at this
    exact this.symm
  have e1 : inter H α Λ₂ Λ₃ G = μ • inter H α Λ₁ Λ₃ F := by
    funext v
    rw [hG, hμ]
    exact hF V H α Λ₁ Λ₂ Λ₃ hT S₂ S₃ hS₂ hS₃ F hFf v
  have e2 : inter H α Λ₃ Λ₂ (inter H α Λ₁ Λ₃ F) = conj μ • G := by
    funext v
    have := hF V H α Λ₁ Λ₃ Λ₂ hT.swap S₃' S₂' hS₃' hS₂' F hFf v
    rw [hμ', ← hG] at this
    exact this
  have e3 : G = (μ * conj μ) • G := by
    funext v
    have := interInv V H hT.herm Λ₂ Λ₃ α hT.sd₂ hT.sd₃ hT.sc₂ hT.sc₃ hT.i₂₃ hT.i₃₂ G hGf v
    rw [e1, Inv.inter_smul, e2, smul_smul] at this
    exact this.symm
  have hmm : μ * conj μ = 1 := by
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hG0
    have h := congrFun e3 v
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have hv' : G v ≠ 0 := hv
    exact mul_right_cancel₀ hv' (by rw [one_mul]; exact h.symm)
  have hnorm : ‖μ‖ = 1 := by
    rw [Complex.mul_conj] at hmm
    have h : Complex.normSq μ = 1 := by exact_mod_cast hmm
    rw [Complex.normSq_eq_norm_sq] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg μ) two_ne_zero).1 h
  have hts : tripleSum H α Λ₁ S₂ S₃ ≠ 0 := by
    intro h
    rw [hμ, tripleMu, h, mul_zero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨r, hr, hr8⟩ := hS V H α Λ₁ Λ₂ Λ₃ hT S₂ S₃ hS₂ hS₃ hts
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) :=
    ⟨_, rfl⟩
  have h8 : μ ^ 8 = ((c ^ 8 * r : ℝ) : ℂ) := by
    rw [hμ, tripleMu, ← hc, mul_pow, hr8]
    push_cast; ring
  have hpos : 0 ≤ c ^ 8 * r := mul_nonneg (by positivity) hr.le
  have h1 : ‖μ ^ 8‖ = 1 := by rw [norm_pow, hnorm, one_pow]
  rw [h8, Complex.norm_real, Real.norm_of_nonneg hpos] at h1
  rw [h8, h1]; simp

end Formalism.L2.Th1.H
