import Mathlib
import GroundTheory.GlobalFields.Artin.Places
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Group

variable {G : Type*} [Group G]

def conjSubgroupOfEquiv (H D : Subgroup G) (x : G) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D ≃
      (MulAut.conj x • D : Subgroup G).subgroupOf H where
  toFun e := ⟨⟨x * ((e : D) : G) * x⁻¹,
      (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 e.2)⟩, by
    rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
    change x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x ∈ D
    rw [show x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x = (e : D) by group]
    exact (e : D).2⟩
  invFun d := ⟨⟨x⁻¹ * ((d : H) : G) * x,
      (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩, by
    rw [Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
    change x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ ∈ H
    rw [show x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ = (d : H) by group]
    exact (d : H).2⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x = (e : D)
    group
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ = (d : H)
    group

end Group

section Finite

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

omit [NumberField K] [NumberField L] [IsGalois K L] in

instance normal_inertia_subgroupOf_stabilizer :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).Normal :=
  ⟨fun n hn g ↦ by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact mul_mul_inv_mem_inertia g.2 hn⟩

theorem inertiaDeg_subfieldPlace (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.inertiaDeg (𝓞 K) =
      frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal
  set I := w.asIdeal.inertia Gal(L/K)
  set u := subfieldPlace H w x
  have hID : I ≤ D := Ideal.inertia_le_stabilizer w.asIdeal

  have ha := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := Gal(L/K)) (w.asIdeal.under (𝓞 K)) w.asIdeal
  have hb := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := H) u.asIdeal (x • w.asIdeal)
  erw [stabilizer_smul_eq, inertia_smul_eq] at hb

  have hc := Ideal.inertiaDeg_tower (R := 𝓞 K) u.asIdeal (x • w.asIdeal)
  rw [Ideal.inertiaDeg_smul] at hc
  have hd := card_mul_card_eq (H := H) hID x
  rw [Nat.card_congr (conjSubgroupOfEquiv H D x)] at hd
  set r := frobIndex H D I x
  set fw := w.asIdeal.inertiaDeg (𝓞 K)
  set fu := u.asIdeal.inertiaDeg (𝓞 K)
  set fP := (x • w.asIdeal).inertiaDeg (𝓞 (fixedField H))
  have hI : 0 < Nat.card I := Nat.card_pos
  have hIx : 0 < Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) := Nat.card_pos
  have hfP : 0 < fP := Ideal.inertiaDeg_pos (x • w.asIdeal) _
  rw [ha, hb] at hd
  have h1 : fw = r * fP := by
    have : Nat.card I * Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) * fw =
        Nat.card I * Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) * (r * fP) := by
      rw [← mul_assoc] at hd
      linarith [hd]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hI hIx) this
  rw [hc] at h1
  exact (Nat.eq_of_mul_eq_mul_right hfP h1)

theorem absNorm_subfieldPlace [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    Ideal.absNorm (subfieldPlace H w x).asIdeal = Ideal.absNorm v.asIdeal ^
      frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  have := subfieldPlace_liesOver H v w x
  rw [← inertiaDeg_subfieldPlace]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal (subfieldPlace H w x).asIdeal).symm

theorem mk_pow_smul_of_isArithFrobAt {P : Ideal (𝓞 L)} {ψ : Gal(L/K)}
    (hψ : IsArithFrobAt (𝓞 K) ψ P) (n : ℕ) (y : 𝓞 L) :
    Ideal.Quotient.mk P ((ψ ^ n) • y) =
      Ideal.Quotient.mk P y ^ (Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ^ n) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul]
    erw [hψ.mk_apply]
    rw [ih, ← pow_mul, ← pow_succ]

theorem card_quotient_subfieldPlace (x : Gal(L/K)) :
    Nat.card (𝓞 (fixedField H) ⧸ (x • w.asIdeal).under (𝓞 (fixedField H))) =
      Nat.card (𝓞 K ⧸ (x • w.asIdeal).under (𝓞 K)) ^
        frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  have hu := inertiaDeg_subfieldPlace H w x
  rw [asIdeal_subfieldPlace] at hu
  have := Ideal.absNorm_pow_inertiaDeg (((x • w.asIdeal).under (𝓞 (fixedField H))).under (𝓞 K))
    ((x • w.asIdeal).under (𝓞 (fixedField H)))
  rw [hu, Ideal.under_under] at this
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    ← Ideal.absNorm_apply, this]

theorem frobElem_of_isArithFrobAt {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (x : Gal(L/K)) (φx : H) (h : IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal)) :
    ∃ i ∈ (MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)),
      (φx : Gal(L/K)) = x * φ ^ (frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.asIdeal.inertia Gal(L/K)) x : ℤ) * x⁻¹ * i := by
  set r := frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x
  have hψ : IsArithFrobAt (𝓞 K) (x * φ * x⁻¹) (x • w.asIdeal) := hφ.conj x
  have hN : Nat.card (𝓞 (fixedField H) ⧸ (x • w.asIdeal).under (𝓞 (fixedField H))) =
      Nat.card (𝓞 K ⧸ (x • w.asIdeal).under (𝓞 K)) ^ r := card_quotient_subfieldPlace H w x

  have hj : (φx : Gal(L/K)) * ((x * φ * x⁻¹) ^ r)⁻¹ ∈ (x • w.asIdeal).inertia Gal(L/K) := by
    intro y
    rw [Submodule.mem_toAddSubgroup, ← Ideal.Quotient.eq, mul_smul]
    have h1 := mk_pow_smul_of_isArithFrobAt hψ r (((x * φ * x⁻¹) ^ r)⁻¹ • y)
    rw [smul_inv_smul] at h1
    rw [h1]
    change Ideal.Quotient.mk _ (φx • (((x * φ * x⁻¹) ^ r)⁻¹ • y)) = _
    erw [h.mk_apply]
    rw [hN]
  have hs : ((x * φ * x⁻¹) ^ r)⁻¹ ∈ MulAction.stabilizer Gal(L/K) (x • w.asIdeal) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hψ.mem_stabilizer r)
  have hi := mul_mul_inv_mem_inertia hs hj
  rw [inv_inv, show ((x * φ * x⁻¹) ^ r)⁻¹ * ((φx : Gal(L/K)) * ((x * φ * x⁻¹) ^ r)⁻¹) *
    (x * φ * x⁻¹) ^ r = ((x * φ * x⁻¹) ^ r)⁻¹ * φx by group] at hi
  refine ⟨((x * φ * x⁻¹) ^ r)⁻¹ * φx, ?_, ?_⟩
  · rw [mem_conj_smul_iff, ← mem_inertia_smul_iff]
    exact hi
  · rw [zpow_natCast, ← conj_pow]
    group

theorem exists_frobElem_isArithFrobAt {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (x : Gal(L/K)) :
    ∃ φx : H, (∃ i ∈ (MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)),
        (φx : Gal(L/K)) = x * φ ^ (frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.asIdeal.inertia Gal(L/K)) x : ℤ) * x⁻¹ * i) ∧
      IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal) := by
  have : (x • w.asIdeal).IsMaximal := (x • w).isMaximal
  obtain ⟨φx, hφx⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 (fixedField H)) H (x • w.asIdeal)
  exact ⟨φx, frobElem_of_isArithFrobAt H w hφ x φx hφx, hφx⟩

end Finite

end GroundTheory.Global.Artin
