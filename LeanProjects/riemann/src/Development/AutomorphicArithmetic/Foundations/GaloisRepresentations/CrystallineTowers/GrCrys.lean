import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

noncomputable section

open UpperTheory.Gal.Seam
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.Gal.Seam

section Block

variable {F : Type} [Field F] {d : ℕ} (c : Fin d → ℕ)

private def lowSub (v : ℕ) : Submodule F (Fin d → F) where
  carrier := {x | ∀ i, v < c i → x i = 0}
  add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun k x hx i hi => by simp [hx i hi]

private def eqSub (v : ℕ) : Submodule F (Fin d → F) where
  carrier := {x | ∀ i, c i ≠ v → x i = 0}
  add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun k x hx i hi => by simp [hx i hi]

private def prEq (v : ℕ) : (Fin d → F) →ₗ[F] ↥(eqSub (F := F) c v) where
  toFun x := ⟨fun i => if c i = v then x i else 0, fun i hi => by simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases h : c i = v <;> simp [h]
  map_smul' k x := by
    apply Subtype.ext
    funext i
    by_cases h : c i = v <;> simp [h]

private theorem prEq_apply (v : ℕ) (x : Fin d → F) (i : Fin d) :
    (prEq c v x : Fin d → F) i = if c i = v then x i else 0 := rfl

private def eqEquiv : (Fin d → F) ≃ₗ[F] (∀ v : ↥(Set.range c), ↥(eqSub (F := F) c v.1)) where
  toFun x v := prEq c v.1 x
  map_add' x y := by funext v; simp
  map_smul' k x := by funext v; simp
  invFun y i := (y ⟨c i, i, rfl⟩ : Fin d → F) i
  left_inv x := by funext i; simp [prEq_apply]
  right_inv y := by
    funext v
    apply Subtype.ext
    funext i
    rw [prEq_apply]
    by_cases h : c i = v.1
    · rw [if_pos h]
      have : (⟨c i, i, rfl⟩ : ↥(Set.range c)) = v := Subtype.ext h
      exact congrArg (fun w : ↥(Set.range c) => (y w : Fin d → F) i) this
    · rw [if_neg h]
      exact ((y v).2 i h).symm

end Block

section Crys

variable {l : ℕ} [Fact l.Prime]

private theorem isCrys_gr (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K L : FinExt l) {d : ℕ}
    (c : Fin d → ℕ) (ρ₀ ρ : Representation ↥L.1 ↥(GK K) (Fin d → ↥L.1))
    (A : ↥(GK K) → Matrix (Fin d) (Fin d) ↥L.1) (h₀ : ∀ g x, ρ₀ g x = (A g).mulVec x)
    (h₁ : ∀ g x i, ρ g x i = ∑ j, (if c i = c j then A g i j else 0) * x j)
    (hb : ∀ g, (A g).BlockTriangular c) (hc : IsCrys (P.PD K) ρ₀) : IsCrys (P.PD K) ρ := by
  have hW : ∀ (v : ℕ) g, lowSub c v ≤ (lowSub (F := ↥L.1) c v).comap (ρ₀ g) := by
    intro v g x hx i hi
    show (ρ₀ g x) i = 0
    rw [h₀]
    change ∑ j, A g i j * x j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : v < c j
    · rw [hx j hj, mul_zero]
    · rw [hb g (lt_of_le_of_lt (not_lt.1 hj) hi), zero_mul]
  have hU : ∀ (v : ℕ) g, eqSub c v ≤ (eqSub (F := ↥L.1) c v).comap (ρ g) := by
    intro v g x hx i hi
    show (ρ g x) i = 0
    rw [h₁]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : c i = c j
    · rw [hx j (hj ▸ hi), mul_zero]
    · rw [if_neg hj, zero_mul]
  have hblock : ∀ v, IsCrys (P.PD K) (ρ.subrepresentation (eqSub c v) (hU v)) := by
    intro v
    have c1 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L ↥(lowSub c v)
      (ρ₀.subrepresentation (lowSub c v) (hW v)) (Fin d → ↥L.1) ρ₀ (lowSub c v).subtype
      (fun g x => rfl)).1 Subtype.val_injective hc
    refine ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L ↥(lowSub c v)
      (ρ₀.subrepresentation (lowSub c v) (hW v)) ↥(eqSub c v) (ρ.subrepresentation (eqSub c v) (hU v))
      ((prEq c v).comp (lowSub c v).subtype) ?_).2 ?_ c1).1
    · intro g x
      apply Subtype.ext
      funext i
      show (prEq c v (ρ₀ g x.1) : Fin d → ↥L.1) i = ρ g (prEq c v x.1 : Fin d → ↥L.1) i
      rw [prEq_apply, h₁]
      by_cases hi : c i = v
      · rw [if_pos hi, h₀]
        change ∑ j, A g i j * x.1 j = _
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [prEq_apply]
        by_cases hj : c j = v
        · rw [if_pos (hi.trans hj.symm), if_pos hj]
        · rw [if_neg hj, mul_zero]
          by_cases hl : v < c j
          · rw [x.2 j hl, mul_zero]
          · rw [hb g (lt_of_le_of_ne (not_lt.1 hl) hj |>.trans_eq hi.symm), zero_mul]
      · rw [if_neg hi]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        rw [prEq_apply]
        by_cases hj : c j = v
        · rw [if_neg fun h => hi (h.trans hj), zero_mul]
        · rw [if_neg hj, mul_zero]
    · intro y
      refine ⟨⟨y.1, fun i hi => y.2 i (ne_of_gt hi)⟩, ?_⟩
      apply Subtype.ext
      funext i
      show (prEq c v y.1 : Fin d → ↥L.1) i = y.1 i
      rw [prEq_apply]
      by_cases hi : c i = v
      · rw [if_pos hi]
      · rw [if_neg hi, y.2 i hi]
  refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (ι := ↥(Set.range c)) (V := fun v => ↥(eqSub (F := ↥L.1) c v.1))
    (ρ := fun v => ρ.subrepresentation (eqSub c v.1) (hU v.1)) (ρ' := ρ) (E := eqEquiv c) ?_ fun v => hblock v.1
  intro g x v
  apply Subtype.ext
  funext i
  show (prEq c v.1 (ρ g x) : Fin d → ↥L.1) i = ρ g (prEq c v.1 x : Fin d → ↥L.1) i
  rw [prEq_apply, h₁, h₁]
  by_cases hi : c i = v.1
  · rw [if_pos hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [prEq_apply]
    by_cases hj : c i = c j
    · rw [if_pos hj, if_pos (hj.symm.trans hi)]
    · rw [if_neg hj, zero_mul, zero_mul]
  · rw [if_neg hi]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [prEq_apply]
    by_cases hj : c i = c j
    · rw [if_neg fun h => hi (hj.trans h), mul_zero]
    · rw [if_neg hj, zero_mul]

end Crys

end UpperTheory.Gal.Seam

theorem UpperTheory.Gal.Seam.grCrys :
    GrCrys := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw d r₀ r hg h₀
  obtain ⟨T⟩ := hT
  obtain ⟨c, hc⟩ := hg
  obtain ⟨L, r₀', hm, hcr⟩ := h₀
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  have hr₀ : ∀ g, ((r₀' g : Matrix.GeneralLinearGroup (Fin d) ↥L.1) : Matrix (Fin d) (Fin d) ↥L.1).map f =
      (r₀ g : Matrix (Fin d) (Fin d) (Om l)) := fun g => by
    rw [← hm.2]; rfl
  have hmem : ∀ g i j, (r g : Matrix (Fin d) (Fin d) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [(hc g).2 i j]
    split_ifs
    · rw [← hr₀ g]
      exact ((r₀' g : Matrix (Fin d) (Fin d) ↥L.1) i j).2
    · exact zero_mem _
  obtain ⟨r', hr'⟩ := GlobalTheory.CrysSubRep.exists_model_of_mem r L hmem
  have hmod : GlobalTheory.Pst.IsModel Bw r L r' := ⟨hm.1, hr'⟩
  have hr'g : ∀ g, ((r' g : Matrix.GeneralLinearGroup (Fin d) ↥L.1) : Matrix (Fin d) (Fin d) ↥L.1).map f =
      (r g : Matrix (Fin d) (Fin d) (Om l)) := fun g => by
    rw [← hr']; rfl
  have hent : ∀ g i j, (r' g : Matrix (Fin d) (Fin d) ↥L.1) i j =
      if c i = c j then (r₀' g : Matrix (Fin d) (Fin d) ↥L.1) i j else 0 := fun g i j => by
    apply f.injective
    have e := (hc g).2 i j
    rw [← hr'g g, ← hr₀ g] at e
    simp only [Matrix.map_apply] at e
    rw [e]
    split_ifs <;> simp
  refine ⟨L, r', hmod, ?_⟩
  refine isCrys_gr P AI T Bw.Kw L c (Bw.repE L r₀') (Bw.repE L r')
    (fun g => (r₀' (Bw.e.symm g) : Matrix (Fin d) (Fin d) ↥L.1)) (fun _ _ => rfl) ?_ ?_ hcr
  · intro g x i
    show ((r' (Bw.e.symm g) : Matrix (Fin d) (Fin d) ↥L.1).mulVec x) i = _
    simp only [Matrix.mulVec, dotProduct, hent]
  · intro g i j hij
    apply f.injective
    have e := (hc (Bw.e.symm g)).1 hij
    rw [← hr₀] at e
    simpa using e
