import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem relIndex_pi_pi' {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

def twist₂ (ϖ : L) (d : ℤ) : AddSubgroup L :=
  (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ d))

theorem mem_intL {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem relIndex_twO (ϖ : L) (Q : ℕ) (h0 : ϖ ≠ 0) (h1 : Valued.v ϖ ≤ 1)
    (hQ : ∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = Q ^ e) (d : ℤ) :
    (Formalism.UG.intL L).toAddSubgroup.relIndex (twist₂ ϖ d) = Q ^ (max (-d) 0).toNat := by
  rcases le_or_gt 0 d with hd | hd
  · have : max (-d) 0 = 0 := max_eq_right (by omega)
    rw [this, Int.toNat_zero, pow_zero, AddSubgroup.relIndex_eq_one]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    change Valued.v (ϖ ^ (k : ℤ) * x) ≤ 1
    rw [zpow_natCast, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' h1 k) hx
  · obtain ⟨e, he⟩ : ∃ e : ℕ, d = -(e : ℤ) := ⟨(-d).toNat, by omega⟩
    subst he
    have hm : max (-(-(e : ℤ))) 0 = e := by omega
    rw [hm, Int.toNat_natCast, ← hQ e]
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    congr 1
    rw [twist₂, AddSubgroup.map_map]
    convert AddSubgroup.map_id _
    ext x
    simp [_root_.zpow_neg, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero e h0)]

end GlobalTheory.DiagIdx

namespace GlobalTheory.DiagIdx

open GlobalTheory.InertHomIdx

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_eq_pi (r n : ℕ) :
    intMat L r n =
      (AddSubgroup.pi Set.univ (fun _ : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => (Formalism.UG.intL L).toAddSubgroup))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext X
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi, mem_intMat]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi]
  exact Iff.rfl

theorem map_diag_eq_pi (ϖ : L) (h0 : ϖ ≠ 0) (r n : ℕ) (d : Fin r → ℤ) :
    (intMat L r n).map (lmul (Matrix.diagonal (fun i => ϖ ^ d i))) =
      (AddSubgroup.pi Set.univ (fun i : Fin r => AddSubgroup.pi Set.univ
        (fun _ : Fin n => twist₂ ϖ (d i)))).map
        (Matrix.ofAddEquiv : (Fin r → Fin n → L) ≃+ Matrix (Fin r) (Fin n) L).toAddMonoidHom := by
  ext Y
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, AddSubgroup.mem_pi, twist₂, AddSubgroup.mem_map]
  constructor
  · rintro ⟨X, hX, hXY⟩ i j
    refine ⟨X i j, hX i j, ?_⟩
    rw [← hXY]
    change ϖ ^ d i * X i j = (Matrix.diagonal (fun i => ϖ ^ d i) * X) i j
    rw [Matrix.diagonal_mul]
  · intro hY
    refine ⟨Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j, fun i j => ?_, ?_⟩
    · obtain ⟨x, hx, hxe⟩ := hY i j
      change ϖ ^ d i * x = Y i j at hxe
      change (ϖ ^ d i)⁻¹ * Y i j ∈ Formalism.UG.intL L
      rw [← hxe, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ h0), one_mul]
      exact hx
    · ext i j
      change (Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.of fun i j => (ϖ ^ d i)⁻¹ * Y i j) i j = Y i j
      rw [Matrix.diagonal_mul, Matrix.of_apply, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ h0), one_mul]

theorem sum_toNat {r : ℕ} (d : Fin r → ℤ) :
    ∑ i, (max (-d i) 0).toNat = (∑ i, max (-d i) 0).toNat := by
  have h : ((∑ i, (max (-d i) 0).toNat : ℕ) : ℤ) = ∑ i, max (-d i) 0 := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Int.toNat_of_nonneg (le_max_right _ _)
  rw [← h, Int.toNat_natCast]

theorem relIndex_intMat_diag : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro L _ _ ϖ Q h0 h1 hQ r n d
  rw [map_diag_eq_pi ϖ h0, intMat_eq_pi,
    AddSubgroup.relIndex_map_map_of_injective _ _ (AddEquiv.injective _), relIndex_pi_pi']
  simp_rw [relIndex_pi_pi', relIndex_twO ϖ Q h0 h1 hQ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← sum_toNat, Finset.mul_sum,
    mul_comm n]

end GlobalTheory.DiagIdx
