import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DifferentialRepresentation
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GapStatement
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleSumEighthOf

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Tri

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem card_reps {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    S.card = Λ₁.relIndex Λ₂ := by
  have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  rw [h1]; rfl

theorem idx_reps {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) : IsReps (triv Λ₁ Λ₂ Λ₃) (pairs Λ₁ Λ₂ Λ₃) (idx Λ₁ S₂ S₃) := by
  refine ⟨fun p hp => idx_pairs hS₂ hS₃ hp, fun p hp q hq h => idx_inj hS₂ hS₃ hp hq h, fun p hp => ?_⟩
  obtain ⟨q, hq, h⟩ := idx_surj hS₂ hS₃ hp
  refine ⟨q, hq, ?_⟩
  have := (triv Λ₁ Λ₂ Λ₃).neg_mem h
  rwa [neg_sub] at this

def big (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : AddSubgroup (V × V) :=
  triv Λ₁ Λ₂ Λ₃ ⊔ (Λ₁ ⊓ Λ₃).map (AddMonoidHom.inl V V)

theorem mem_big {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {p : V × V} :
    p ∈ big Λ₁ Λ₂ Λ₃ ↔ ∃ t ∈ Λ₂ ⊓ Λ₃, p.1 - t ∈ Λ₁ ⊓ Λ₃ ∧ p.2 + t ∈ Λ₁ ⊓ Λ₂ := by
  unfold big
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, z, hz, rfl⟩
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hz
    refine ⟨y.1, hy1, ?_, ?_⟩
    · simpa using hu
    · simpa [add_comm] using hy2
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨(t, p.2), ⟨ht, ?_⟩, (p.1 - t, 0), AddSubgroup.mem_map.2 ⟨p.1 - t, h1, rfl⟩, ?_⟩
    · simpa [add_comm] using h2
    · ext <;> simp

theorem big_le_pairs (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : big Λ₁ Λ₂ Λ₃ ≤ pairs Λ₁ Λ₂ Λ₃ := by
  intro p hp
  obtain ⟨t, ht, h1, h2⟩ := mem_big.1 hp
  refine ⟨?_, ?_, ?_⟩
  · have := Λ₃.add_mem h1.2 ht.2
    simpa using this
  · have := Λ₂.sub_mem h2.2 ht.1
    simpa using this
  · have := Λ₁.add_mem h1.1 h2.1
    convert this using 1; abel

theorem comap_inl_triv (Λ₁ Λ₂ Λ₃ : AddSubgroup V) :
    (triv Λ₁ Λ₂ Λ₃).comap (AddMonoidHom.inl V V) = Λ₁ ⊓ Λ₂ ⊓ Λ₃ := by
  ext x
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : x ∈ Λ₂ ⊓ Λ₃ := h1
    have h2' : x + 0 ∈ Λ₁ ⊓ Λ₂ := h2
    rw [add_zero] at h2'
    exact ⟨h2', h1'.2⟩
  · rintro ⟨⟨a, b⟩, c⟩
    refine ⟨⟨b, c⟩, ?_⟩
    show x + 0 ∈ Λ₁ ⊓ Λ₂
    rw [add_zero]; exact ⟨a, b⟩

theorem card_idx {Λ₁ Λ₂ Λ₃ : AddSubgroup V} {S₂ S₃ : Finset V} (hS₂ : IsReps Λ₁ Λ₂ S₂)
    (hS₃ : IsReps Λ₂ Λ₃ S₃) :
    (idx Λ₁ S₂ S₃).card
      = (Λ₁ ⊓ Λ₂ ⊓ Λ₃).relIndex (Λ₁ ⊓ Λ₃) * (big Λ₁ Λ₂ Λ₃).relIndex (pairs Λ₁ Λ₂ Λ₃) := by
  rw [card_reps (idx_reps hS₂ hS₃),
    ← AddSubgroup.relIndex_mul_relIndex (triv Λ₁ Λ₂ Λ₃) (big Λ₁ Λ₂ Λ₃) (pairs Λ₁ Λ₂ Λ₃) le_sup_left
      (big_le_pairs Λ₁ Λ₂ Λ₃)]
  congr 1
  unfold big
  rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.relIndex_comap, comap_inl_triv]

theorem big_swap (Λ₁ Λ₂ Λ₃ : AddSubgroup V) :
    (big Λ₁ Λ₃ Λ₂).relIndex (pairs Λ₁ Λ₃ Λ₂) = (big Λ₁ Λ₂ Λ₃).relIndex (pairs Λ₁ Λ₂ Λ₃) := by
  have e1 : big Λ₁ Λ₃ Λ₂ = (big Λ₁ Λ₂ Λ₃).comap (AddEquiv.prodComm (M := V) (N := V)).toAddMonoidHom := by
    ext p
    rw [AddSubgroup.mem_comap, mem_big, mem_big]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      refine ⟨-t, (Λ₂ ⊓ Λ₃).neg_mem ⟨ht.2, ht.1⟩, ?_, ?_⟩
      · simpa using h2
      · simpa [sub_eq_add_neg] using h1
    · rintro ⟨t, ht, h1, h2⟩
      refine ⟨-t, (Λ₃ ⊓ Λ₂).neg_mem ⟨ht.2, ht.1⟩, ?_, ?_⟩
      · simpa using h2
      · simpa [sub_eq_add_neg] using h1
  have e2 : (pairs Λ₁ Λ₃ Λ₂).map (AddEquiv.prodComm (M := V) (N := V)).toAddMonoidHom = pairs Λ₁ Λ₂ Λ₃ := by
    ext p
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨q, ⟨q1, q2, q3⟩, rfl⟩
      refine ⟨q2, q1, ?_⟩
      rw [add_comm] at q3
      exact q3
    · rintro ⟨p1, p2, p3⟩
      refine ⟨(p.2, p.1), ⟨p2, p1, ?_⟩, rfl⟩
      rw [add_comm] at p3
      exact p3
  rw [e1, AddSubgroup.relIndex_comap, e2]

theorem psi_conj {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ Λ₃ : AddSubgroup V} (hT : TripleData H α Λ₁ Λ₂ Λ₃)
    {z y : V} (hz : z ∈ Λ₃) (hy : y ∈ Λ₂) (hzy : z + y ∈ Λ₁) :
    psiT H α y z = conj (psiT H α z y) := by
  have r : ∀ {Λ : AddSubgroup V}, IsSemiChar H Λ α → ∀ {x : V}, x ∈ Λ → conj (α x) = α x := by
    intro Λ h x hx
    rcases h.1 x hx with e | e <;> simp [e]
  unfold psiT
  rw [map_mul, map_mul, map_mul, r hT.sc₃ hz, r hT.sc₂ hy, r hT.sc₁ hzy, ← Complex.exp_conj,
    add_comm y z, Inv.altE_swap hT.herm z y]
  congr 1
  · ring
  · congr 1
    simp [Complex.conj_ofReal]

end Tri

open Tri

theorem TripleConj_proof : TripleConj := by
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hT S₂ S₃ S₂' S₃' hS₂ hS₃ hS₃' hS₂'
  obtain ⟨-, -, -, h4⟩ := triplePhaseQuadratic V H α Λ₁ Λ₂ Λ₃ hT
  have hR := idx_reps hS₂ hS₃
  have hR' := idx_reps hS₃' hS₂'
  obtain ⟨R, hRdef⟩ : ∃ R, R = idx Λ₁ S₂ S₃ := ⟨_, rfl⟩
  obtain ⟨R', hR'def⟩ : ∃ R', R' = idx Λ₁ S₃' S₂' := ⟨_, rfl⟩
  rw [← hRdef] at hR
  rw [← hR'def] at hR'

  have hinv : ∀ x ∈ pairs Λ₁ Λ₂ Λ₃, ∀ t ∈ pairs Λ₁ Λ₂ Λ₃, t ∈ triv Λ₁ Λ₂ Λ₃ →
      (fun p : V × V => psiT H α p.1 p.2) (x + t) = (fun p : V × V => psiT H α p.1 p.2) x := by
    rintro x ⟨x1, x2, x3⟩ t - ⟨t1, t2⟩
    have key := h4 x.1 x1 x.2 x2 x3 0 (Λ₁ ⊓ Λ₃).zero_mem _ t2 _ t1
    show psiT H α (x.1 + t.1) (x.2 + t.2) = psiT H α x.1 x.2
    rw [← key]
    congr 1
    · simp
    · abel
  have hinv' : ∀ x ∈ pairs Λ₁ Λ₃ Λ₂, ∀ t ∈ pairs Λ₁ Λ₃ Λ₂, t ∈ triv Λ₁ Λ₃ Λ₂ →
      (fun p : V × V => psiT H α p.2 p.1) (x + t) = (fun p : V × V => psiT H α p.2 p.1) x := by
    rintro x ⟨x1, x2, x3⟩ t - ⟨t1, t2⟩
    rw [add_comm] at x3
    have key := h4 x.2 x2 x.1 x1 x3 _ t2 0 (Λ₁ ⊓ Λ₂).zero_mem _ ((Λ₂ ⊓ Λ₃).neg_mem ⟨t1.2, t1.1⟩)
    show psiT H α (x.2 + t.2) (x.1 + t.1) = psiT H α x.2 x.1
    rw [← key]
    congr 1
    · abel
    · abel
  have h1 : ∑ q ∈ R', ∑ x ∈ R, psiT H α (x.1 + q.2) (x.2 + q.1)
      = (R'.card : ℂ) * ∑ x ∈ R, psiT H α x.1 x.2 := by
    have : ∀ q ∈ R', ∑ x ∈ R, psiT H α (x.1 + q.2) (x.2 + q.1) = ∑ x ∈ R, psiT H α x.1 x.2 := by
      intro q hq
      obtain ⟨q1, q2, q3⟩ := hR'.1 q hq
      rw [add_comm] at q3
      exact CharacterSumTripleLemmas.sum_shift hR (fun p : V × V => psiT H α p.1 p.2) hinv
        (a := (q.2, q.1)) ⟨q2, q1, q3⟩
    rw [Finset.sum_congr rfl this]
    simp
  have h2 : ∑ x ∈ R, ∑ q ∈ R', psiT H α (x.1 + q.2) (x.2 + q.1)
      = (R.card : ℂ) * ∑ q ∈ R', psiT H α q.2 q.1 := by
    have : ∀ x ∈ R, ∑ q ∈ R', psiT H α (x.1 + q.2) (x.2 + q.1) = ∑ q ∈ R', psiT H α q.2 q.1 := by
      intro x hx
      obtain ⟨x1, x2, x3⟩ := hR.1 x hx
      rw [add_comm] at x3
      rw [← CharacterSumTripleLemmas.sum_shift hR' (fun p : V × V => psiT H α p.2 p.1) hinv'
        (a := (x.2, x.1)) ⟨x2, x1, x3⟩]
      refine Finset.sum_congr rfl fun q _ => ?_
      show _ = psiT H α (q.2 + x.1) (q.1 + x.2)
      rw [add_comm x.1, add_comm x.2]
    rw [Finset.sum_congr rfl this]
    simp
  have h3 : (R'.card : ℂ) * ∑ x ∈ R, psiT H α x.1 x.2 = (R.card : ℂ) * ∑ q ∈ R', psiT H α q.2 q.1 := by
    rw [← h1, ← h2, Finset.sum_comm]

  have hB : tripleSum H α Λ₁ S₃' S₂' = conj (∑ q ∈ R', psiT H α q.2 q.1) := by
    rw [tripleSum_eq, ← hR'def, map_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨q1, q2, q3⟩ := hR'.1 q hq
    rw [add_comm] at q3
    exact psi_conj hT q2 q1 q3
  have hA : tripleSum H α Λ₁ S₂ S₃ = ∑ x ∈ R, psiT H α x.1 x.2 := by
    rw [tripleSum_eq, ← hRdef]

  have n13 : relIdx Λ₁ Λ₃ = (Λ₁ ⊓ Λ₃).relIndex Λ₁ := by
    rw [indexEq V H hT.herm Λ₁ Λ₃ hT.sd₁ hT.sd₃ hT.i₁₃ hT.i₃₁, AddSubgroup.inf_relIndex_left]; rfl
  have n12 : relIdx Λ₁ Λ₂ = (Λ₁ ⊓ Λ₂).relIndex Λ₁ := by
    rw [indexEq V H hT.herm Λ₁ Λ₂ hT.sd₁ hT.sd₂ hT.i₁₂ hT.i₂₁, AddSubgroup.inf_relIndex_left]; rfl
  have n23 : relIdx Λ₃ Λ₂ = relIdx Λ₂ Λ₃ := indexEq V H hT.herm Λ₃ Λ₂ hT.sd₃ hT.sd₂ hT.i₃₂ hT.i₂₃
  have hcard : R.card * relIdx Λ₁ Λ₃ = R'.card * relIdx Λ₁ Λ₂ := by
    have a13 := AddSubgroup.relIndex_mul_relIndex (Λ₁ ⊓ Λ₂ ⊓ Λ₃) (Λ₁ ⊓ Λ₃) Λ₁
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_left
    have a12 := AddSubgroup.relIndex_mul_relIndex (Λ₁ ⊓ Λ₂ ⊓ Λ₃) (Λ₁ ⊓ Λ₂) Λ₁ inf_le_left inf_le_left
    rw [hRdef, hR'def, card_idx hS₂ hS₃, card_idx hS₃' hS₂', big_swap, n13, n12,
      inf_right_comm Λ₁ Λ₃ Λ₂, mul_right_comm, a13, mul_right_comm, a12]
  have hR'0 : (R'.card : ℂ) ≠ 0 := by
    obtain ⟨q, hq, -⟩ := hR'.2.2 0 (pairs Λ₁ Λ₃ Λ₂).zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨q, hq⟩).ne'
  obtain ⟨A, hAdef⟩ : ∃ A, A = ∑ x ∈ R, psiT H α x.1 x.2 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = ∑ q ∈ R', psiT H α q.2 q.1 := ⟨_, rfl⟩
  rw [← hAdef, ← hBdef] at h3
  rw [← hAdef] at hA
  rw [← hBdef] at hB
  have hcardC : (R.card : ℂ) * (relIdx Λ₁ Λ₃ : ℂ) = (R'.card : ℂ) * (relIdx Λ₁ Λ₂ : ℂ) := by
    exact_mod_cast hcard
  have hAB : (relIdx Λ₁ Λ₃ : ℂ) * A = (relIdx Λ₁ Λ₂ : ℂ) * B := by
    refine mul_left_cancel₀ hR'0 ?_
    linear_combination (relIdx Λ₁ Λ₃ : ℂ) * h3 + B * hcardC
  have hABc : (relIdx Λ₁ Λ₃ : ℂ) * conj A = (relIdx Λ₁ Λ₂ : ℂ) * conj B := by
    have := congrArg conj hAB
    simpa only [map_mul, map_natCast] using this
  unfold tripleMu
  rw [hA, hB, n23, map_mul, Complex.conj_ofReal]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.sqrt (relIdx Λ₁ Λ₂) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.sqrt (relIdx Λ₁ Λ₃) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.sqrt (relIdx Λ₂ Λ₃) := ⟨_, rfl⟩
  have pos : ∀ n : ℕ, n ≠ 0 → Real.sqrt n ≠ 0 := fun n hn =>
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
  have ha0 : (a : ℂ) ≠ 0 := by rw [ha]; exact_mod_cast pos _ hT.i₁₂
  have hb0 : (b : ℂ) ≠ 0 := by rw [hb]; exact_mod_cast pos _ hT.i₁₃
  have hd0 : (d : ℂ) ≠ 0 := by rw [hd]; exact_mod_cast pos _ hT.i₂₃
  have haa : (a : ℂ) * a = (relIdx Λ₁ Λ₂ : ℂ) := by
    rw [ha]; exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hbb : (b : ℂ) * b = (relIdx Λ₁ Λ₃ : ℂ) := by
    rw [hb]; exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [← ha, ← hb, ← hd]
  rw [← haa, ← hbb] at hABc
  push_cast
  field_simp
  linear_combination -hABc

theorem TripleEighth_proof : TripleEighth :=
  TripleEighth_of TripleFormula_proof (TripleSumEighth_of triplePhaseQuadratic degenerateGaussSum)
    TripleConj_proof

end Formalism.L2.Th1.H
