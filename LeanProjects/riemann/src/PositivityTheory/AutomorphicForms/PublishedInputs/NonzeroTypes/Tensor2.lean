import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module

namespace UpperTheory.TNZ.Grp.Tensor₂

section Contr

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]

theorem prod_update (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (i : ι) (hi : i ≠ a) (w : Y i) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x i w b) =
      φ i w * ∏ b ∈ (Finset.univ.erase a).erase i, φ b (x b) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

theorem prod_update_self (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (w : Y a) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x a w b) = ∏ b ∈ Finset.univ.erase a, φ b (x b) :=
  Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

def contrML (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : MultilinearMap ℂ Y (Y a) where
  toFun x := (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a
  map_update_add' := by
    intro inst x i u v
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self, smul_add]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c u
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self]
      rw [smul_comm]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul]
      rw [mul_assoc, mul_smul]

def contr (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : (⨂[ℂ] b, Y b) →ₗ[ℂ] Y a :=
  PiTensorProduct.lift (contrML a φ)

theorem contr_tprod (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) :
    contr a φ (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a := by
  rw [contr, PiTensorProduct.lift.tprod]
  rfl

theorem exists_factor_vec {Γ : ι → Type} [∀ b, Group (Γ b)] (ρ : ∀ b, Representation ℂ (Γ b) (Y b)) (a : ι)
    (y : ⨂[ℂ] b, Y b) (hy : y ≠ 0) (S : Set (Γ a)) (c : Γ a → ℂ)
    (h : ∀ g ∈ S, piTensor ρ (Pi.mulSingle a g) y = c g • y) :
    ∃ v : Y a, v ≠ 0 ∧ ∀ g ∈ S, ρ a g v = c g • v := by
  let bs := fun b => Module.Basis.ofVectorSpace ℂ (Y b)
  let B := Basis.piTensorProduct bs
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra H
    simp only [not_exists, not_not] at H
    refine hy (B.repr.injective ?_)
    ext p
    rw [H p, map_zero, Finsupp.zero_apply]
  let φ : ∀ b, Module.Dual ℂ (Y b) := fun b => (bs b).coord (p b)
  have key : ∀ z, (bs a).coord (p a) (contr a φ z) = B.repr z p := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul, contr_tprod, B, Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply,
        smul_eq_mul, Basis.coord_apply, φ]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      ring
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, Finsupp.add_apply]
  have hequiv : ∀ g z, contr a φ (piTensor ρ (Pi.mulSingle a g) z) = ρ a g (contr a φ z) := by
    intro g z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have hpr : ∏ b ∈ Finset.univ.erase a, φ b (ρ b (Pi.mulSingle a g b) (x b)) =
          ∏ b ∈ Finset.univ.erase a, φ b (x b) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb), map_one, Module.End.one_apply]
      simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same, hpr]
    | add z w hz hw => simp only [map_add, hz, hw]
  refine ⟨contr a φ y, fun h0 => hp ?_, fun g hg => ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← hequiv, h g hg, map_smul]

end Contr

end UpperTheory.TNZ.Grp.Tensor₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_tensor {n : ℕ} (G : Grp k n) : G.TensorProductProp := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK

end UpperTheory.TNZ.Grp
