import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerMassQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreFiniteCard

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.MassChange

open Formalism.L2.SG.Pf.StabilizerMassQuotient

section Orbit

def qmass (Γ X : Type*) [Group Γ] [MulAction Γ X] : ℚ :=
  ∑ᶠ o : Quotient (MulAction.orbitRel Γ X), ((Nat.card (MulAction.stabilizer Γ o.out) : ℕ) : ℚ)⁻¹

theorem fib_sum_q (S X : Type*) [Group S] [MulAction S X] [Finite S] [Finite X]
    [Fintype (Quotient (MulAction.orbitRel S X))] :
    ∑ O : Quotient (MulAction.orbitRel S X), ((Nat.card (MulAction.stabilizer S O.out) : ℕ) : ℚ)⁻¹ =
      (Nat.card X : ℚ) / Nat.card S := by
  have key : ∀ O : Quotient (MulAction.orbitRel S X),
      ((Nat.card (MulAction.stabilizer S O.out) : ℕ) : ℚ)⁻¹ =
        (Nat.card (MulAction.orbit S O.out) : ℚ) / Nat.card S := by
    intro O
    have h : Nat.card (MulAction.stabilizer S O.out) * Nat.card (MulAction.orbit S O.out) = Nat.card S := by
      rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
    have hs : (Nat.card (MulAction.stabilizer S O.out) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer S O.out)).ne'
    haveI : Nonempty (MulAction.orbit S O.out) := ⟨⟨O.out, MulAction.mem_orbit_self _⟩⟩
    have ho : (Nat.card (MulAction.orbit S O.out) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.orbit S O.out)).ne'
    rw [← h, Nat.cast_mul]
    field_simp
  simp_rw [key, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  congr 2
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits S X), Nat.card_sigma]

variable {Γ : Type*} [Group Γ]

theorem qmass_eq_of_fibre {A B : Type*} [MulAction Γ A] [MulAction Γ B] (f : A → B)
    (hf : ∀ (g : Γ) (a : A), f (g • a) = g • f a) (N : ℕ) (hN0 : N ≠ 0)
    (hfin : ∀ b, Finite {a : A // f a = b}) (hN : ∀ b, Nat.card {a : A // f a = b} = N)
    (hS : ∀ b : B, Finite (MulAction.stabilizer Γ b)) :
    qmass Γ A = N * qmass Γ B := by
  have hSA : ∀ a : A, Finite (MulAction.stabilizer Γ a) := by
    intro a
    letI := fibAct f hf (f a)
    haveI := hS (f a)
    exact Finite.of_equiv _ (stabEquiv f hf (f a) ⟨a, rfl⟩)
  have hposA : ∀ a : A, ((Nat.card (MulAction.stabilizer Γ a) : ℕ) : ℚ)⁻¹ ≠ 0 := fun a => by
    haveI := hSA a
    exact inv_ne_zero (by exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer Γ a)).ne')
  have hposB : ∀ b : B, ((Nat.card (MulAction.stabilizer Γ b) : ℕ) : ℚ)⁻¹ ≠ 0 := fun b => by
    haveI := hS b
    exact inv_ne_zero (by exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer Γ b)).ne')
  have hqfin : ∀ oB, Finite ↥(qmap f hf ⁻¹' {oB}) := by
    intro oB
    letI := fibAct f hf oB.out
    haveI := hfin oB.out
    exact Finite.of_equiv _ (orbEquiv f hf oB)
  have hqsurj : Function.Surjective (qmap f hf) := by
    intro oB
    have hne : Nonempty {a : A // f a = oB.out} := by
      haveI := hfin oB.out
      have : 0 < Nat.card {a : A // f a = oB.out} := by rw [hN]; exact Nat.pos_of_ne_zero hN0
      exact (Nat.card_pos_iff.1 this).1
    obtain ⟨⟨a, ha⟩⟩ := hne
    exact ⟨Quotient.mk _ a, by rw [qmap_mk, ha]; exact Quotient.out_eq oB⟩
  unfold qmass
  by_cases hB : Finite (Quotient (MulAction.orbitRel Γ B))
  · haveI := hB
    haveI : Finite (Quotient (MulAction.orbitRel Γ A)) :=
      Finite.of_surjective (fun p : Σ oB, ↥(qmap f hf ⁻¹' {oB}) => p.2.1)
        (fun x => ⟨⟨qmap f hf x, x, rfl⟩, rfl⟩)
    letI := Fintype.ofFinite (Quotient (MulAction.orbitRel Γ B))
    letI := Fintype.ofFinite (Quotient (MulAction.orbitRel Γ A))
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum,
      ← Fintype.sum_fiberwise (qmap f hf)]
    refine Finset.sum_congr rfl fun oB _ => ?_
    letI := fibAct f hf oB.out
    haveI := hS oB.out
    haveI := hfin oB.out
    letI := Fintype.ofFinite
      (Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out}))
    have hc : ∀ O, Nat.card (MulAction.stabilizer Γ
        ((orbEquiv f hf oB O) : Quotient (MulAction.orbitRel Γ A)).out) =
        Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ oB.out) O.out) := by
      intro O
      rw [Nat.card_congr (stabEquiv f hf oB.out O.out)]
      apply card_stab_of_orbitRel
      have e1 : ((orbEquiv f hf oB (Quotient.mk _ O.out)) : Quotient (MulAction.orbitRel Γ A)) =
          Quotient.mk _ O.out.1 := rfl
      rw [Quotient.out_eq] at e1
      rw [e1]
      exact Quotient.mk_out (s := MulAction.orbitRel Γ A) O.out.1
    let e : Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out}) ≃
        {x : Quotient (MulAction.orbitRel Γ A) // qmap f hf x = oB} :=
      (orbEquiv f hf oB).trans (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    rw [← Fintype.sum_equiv e (fun O => ((Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ oB.out) O.out) : ℕ) : ℚ)⁻¹)
      _ (fun O => by rw [← hc O]; rfl)]
    rw [fib_sum_q, hN, div_eq_mul_inv]
  · have hA : ¬ Finite (Quotient (MulAction.orbitRel Γ A)) := fun h => hB (Finite.of_surjective _ hqsurj)
    have iA : (Function.support fun o : Quotient (MulAction.orbitRel Γ A) =>
        ((Nat.card (MulAction.stabilizer Γ o.out) : ℕ) : ℚ)⁻¹).Infinite :=
      Set.Infinite.mono (fun o _ => hposA o.out) (Set.infinite_univ_iff.2 (not_finite_iff_infinite.1 hA))
    have iB : (Function.support fun o : Quotient (MulAction.orbitRel Γ B) =>
        ((Nat.card (MulAction.stabilizer Γ o.out) : ℕ) : ℚ)⁻¹).Infinite :=
      Set.Infinite.mono (fun o _ => hposB o.out) (Set.infinite_univ_iff.2 (not_finite_iff_infinite.1 hB))
    rw [finsum_of_infinite_support iA, finsum_of_infinite_support iB, mul_zero]

end Orbit

section Coset

variable {H : Type} [Group H]

def dmass (A C : Subgroup H) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (C : Set H),
    ((Nat.card (A ⊓ C.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup H) : ℕ) : ℚ)⁻¹

theorem mem_stab_iff (A C : Subgroup H) (g : H) (a : A) :
    a ∈ MulAction.stabilizer A ((g : H ⧸ C)) ↔ (a : H) ∈ C.map (MulAut.conj g).toMonoidHom := by
  rw [MulAction.mem_stabilizer_iff]
  change (((a : H) * g : H) : H ⧸ C) = g ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor <;> intro h
  · have h' := C.inv_mem h
    simpa [mul_assoc] using h'
  · have h' := C.inv_mem h
    simpa [mul_assoc] using h'

def stabEquivInf (A C : Subgroup H) (g : H) :
    MulAction.stabilizer A ((g : H ⧸ C)) ≃ (A ⊓ C.map (MulAut.conj g).toMonoidHom : Subgroup H) where
  toFun s := ⟨(s.1 : H), s.1.2, (mem_stab_iff A C g s.1).1 s.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, (mem_stab_iff A C g ⟨x.1, x.2.1⟩).2 x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def dqEquiv (A C : Subgroup H) :
    DoubleCoset.Quotient (A : Set H) (C : Set H) ≃ Quotient (MulAction.orbitRel A (H ⧸ C)) := by
  refine Equiv.ofBijective
    (Quotient.lift (s := DoubleCoset.setoid (A : Set H) (C : Set H))
      (fun g : H => Quotient.mk (MulAction.orbitRel A (H ⧸ C)) (g : H ⧸ C)) ?_) ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.1 hab
    apply Quotient.sound
    show (a : H ⧸ C) ∈ MulAction.orbit A ((x * a * y : H) : H ⧸ C)
    refine ⟨⟨x⁻¹, A.inv_mem hx⟩, ?_⟩
    change ((x⁻¹ * (x * a * y) : H) : H ⧸ C) = a
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hy
  · intro p q hpq
    obtain ⟨a, rfl⟩ := Quotient.exists_rep p
    obtain ⟨b, rfl⟩ := Quotient.exists_rep q
    have h1 : ((a : H ⧸ C)) ∈ MulAction.orbit A ((b : H ⧸ C)) := Quotient.exact hpq
    obtain ⟨⟨x, hx⟩, hxe⟩ := h1
    change ((x * b : H) : H ⧸ C) = a at hxe
    rw [QuotientGroup.eq] at hxe
    apply Quotient.sound
    refine DoubleCoset.rel_iff.2 ⟨x⁻¹, A.inv_mem hx, ((x * b)⁻¹ * a)⁻¹, C.inv_mem hxe, ?_⟩
    group
  · intro o
    refine ⟨Quotient.mk _ (Quotient.out o).out, ?_⟩
    show Quotient.mk _ (((Quotient.out o).out : H) : H ⧸ C) = o
    rw [QuotientGroup.out_eq', Quotient.out_eq]

theorem card_stab_dq (A C : Subgroup H) (q : DoubleCoset.Quotient (A : Set H) (C : Set H)) :
    Nat.card (MulAction.stabilizer A (dqEquiv A C q).out) =
      Nat.card (A ⊓ C.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup H) := by
  have e : dqEquiv A C q = Quotient.mk _ ((Quotient.out q : H) : H ⧸ C) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [e, card_stab_of_orbitRel (Quotient.mk_out (s := MulAction.orbitRel A (H ⧸ C)) _),
    Nat.card_congr (stabEquivInf A C _)]

theorem dmass_eq_qmass (A C : Subgroup H) : dmass A C = qmass A (H ⧸ C) := by
  unfold dmass qmass
  rw [← finsum_comp_equiv (dqEquiv A C)]
  refine finsum_congr fun q => ?_
  rw [card_stab_dq]

theorem coset_fibre (D C : Subgroup H) (h : D ≤ C) (hDC : D.relIndex C ≠ 0)
    (z : H ⧸ C) : Finite {y : H ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : H ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex C := by
  first
  | exact @_root_.GlobalTheory.FibreEquivalence.fibre_finite_card
  | exact _root_.GlobalTheory.FibreEquivalence.fibre_finite_card
  | (apply _root_.GlobalTheory.FibreEquivalence.fibre_finite_card <;> assumption)
  | (intros; apply _root_.GlobalTheory.FibreEquivalence.fibre_finite_card <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FibreEquivalence.fibre_finite_card <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FibreEquivalence.fibre_finite_card ..)

theorem dmass_of_le (A C D : Subgroup H) (hDC : D ≤ C) (hi : D.relIndex C ≠ 0)
    (hfin : ∀ t : H, Finite (A ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup H)) :
    dmass A D = (D.relIndex C : ℚ) * dmass A C := by
  rw [dmass_eq_qmass, dmass_eq_qmass]
  refine qmass_eq_of_fibre (Subgroup.quotientMapOfLE hDC) ?_ _ hi
    (fun z => (coset_fibre D C hDC hi z).1) (fun z => (coset_fibre D C hDC hi z).2) ?_
  · intro g y
    induction y using QuotientGroup.induction_on with
    | H a => rfl
  · intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    haveI := hfin g
    exact Finite.of_equiv _ (stabEquivInf A C g).symm

end Coset

theorem massC_mul_vol : ∀ {G : Type} [Group G] (Γ' T C C' : Subgroup G), C ≤ T → C' ≤ T →
    C.relIndex C' ≠ 0 → C'.relIndex C ≠ 0 →
    (∀ t ∈ T, ((Γ' ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) →
    (∀ t ∈ T, ((Γ' ⊓ C'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) →
    massC Γ' T C' * vol C C' = massC Γ' T C := by
  intro G _ Γ' T C C' hC hC' h1 h2 hf hf'
  have tr : ∀ E : Subgroup G,
      (∀ t ∈ T, ((Γ' ⊓ E.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) →
      ∀ t : T, Finite (Γ'.subgroupOf T ⊓ (E.subgroupOf T).map (MulAut.conj t).toMonoidHom : Subgroup T) := by
    intro E hfE t
    haveI := (hfE t t.2).to_subtype
    refine Finite.of_injective (β := ↥((Γ' ⊓ E.map (MulAut.conj (t : G)).toMonoidHom : Subgroup G) : Set G))
      (fun x => ⟨((x : T) : G), ?_⟩) ?_
    · have hx := x.2
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv,
        MulAut.conj_symm_apply] at hx
      simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      refine ⟨hx.1, ?_⟩
      simpa using hx.2
    · intro x y hxy
      have hv := congrArg Subtype.val hxy
      simp only at hv
      exact Subtype.ext (Subtype.ext hv)
  have hDC : (C ⊓ C').subgroupOf T ≤ C.subgroupOf T := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
  have hDC' : (C ⊓ C').subgroupOf T ≤ C'.subgroupOf T := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
  have i1 : ((C ⊓ C').subgroupOf T).relIndex (C.subgroupOf T) = C'.relIndex C := by
    rw [Subgroup.relIndex_subgroupOf hC, Subgroup.inf_relIndex_left]
  have i2 : ((C ⊓ C').subgroupOf T).relIndex (C'.subgroupOf T) = C.relIndex C' := by
    rw [Subgroup.relIndex_subgroupOf hC', Subgroup.inf_relIndex_right]
  have eD := dmass_of_le (Γ'.subgroupOf T) (C.subgroupOf T) ((C ⊓ C').subgroupOf T) hDC
    (by rw [i1]; exact h2) (tr C hf)
  have eD' := dmass_of_le (Γ'.subgroupOf T) (C'.subgroupOf T) ((C ⊓ C').subgroupOf T) hDC'
    (by rw [i2]; exact h1) (tr C' hf')
  rw [i1] at eD
  rw [i2] at eD'
  have eC : massC Γ' T C = dmass (Γ'.subgroupOf T) (C.subgroupOf T) := rfl
  have eC' : massC Γ' T C' = dmass (Γ'.subgroupOf T) (C'.subgroupOf T) := rfl
  have ha : ((C'.relIndex C : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h2
  rw [eC, eC', vol, mul_div_assoc', div_eq_iff ha]
  linear_combination eD - eD'

end GlobalTheory.LKCount.MassChange
