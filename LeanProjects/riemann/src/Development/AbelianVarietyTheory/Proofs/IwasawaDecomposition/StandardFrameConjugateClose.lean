import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

namespace GlobalTheory.ConjLt
variable {D : D7}

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
    have : (n : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd n) := rfl
    rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [this, WithZero.exp_le_exp]
    omega

theorem cpt_sg_lt_one (Q : Pl D.host.E) (z : EAf D) (h : Valued.v (cpt Q z) < 1) :
    Valued.v (cpt (cP Q) (sg D z)) < 1 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  set p : D.host.E := (π : D.host.E) with hp
  have hvp : Valued.v (cpt Q (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p)) = WithZero.exp (-1) := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap, hp, ← hπ]
    exact Q.valuation_of_algebraMap π
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero, map_zero, map_zero] at hvp
    exact WithZero.exp_ne_zero hvp.symm
  set a := z * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p⁻¹ with ha
  have hza : z = a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p := by
    rw [ha, mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, mul_one]
  have hva : Valued.v (cpt Q a) ≤ 1 := by
    have e1 : Valued.v (cpt Q a) * WithZero.exp (-1) = Valued.v (cpt Q z) := by
      rw [← hvp, ← Valuation.map_mul, ← map_mul, ← hza]
    have e2 := lt_one_le_exp h
    rw [← e1] at e2
    by_contra hc
    push_neg at hc
    have : WithZero.exp (-1) < Valued.v (cpt Q a) * WithZero.exp (-1) := by
      calc WithZero.exp (-1) = 1 * WithZero.exp (-1) := (one_mul _).symm
        _ < _ := mul_lt_mul_of_pos_right hc (WithZero.exp_pos)
    exact absurd e2 (not_le.2 this)
  have h1 := (cpt_cjA_le_iff Q a).2 hva
  have hs : sg D z = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p) := by
    rw [hza, map_mul]; rfl
  have h2 : Valued.v (cpt (cP Q) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p))) < 1 := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    have e : star p = ((cO D π : 𝓞 D.host.E) : D.host.E) := rfl
    rw [e, (cP Q).valuation_lt_one_iff_mem, mem_cP, cO_cO, ← Q.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hs, map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2

theorem conj_sub_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (β x : GL (Fin n) A)
    (R U' : Matrix (Fin n) (Fin n) A) (hX : Formalism.UG.cT σ x.val * R * x.val = R)
    (hU : U' * (Formalism.UG.cT σ β.val * R * β.val) = 1) :
    (β⁻¹ * x * β).val - 1 = U' * (Formalism.UG.cT σ (β⁻¹ * x⁻¹ * β).val - 1) * (Formalism.UG.cT σ β.val * R * β.val) := by
  set G := Formalism.UG.cT σ β.val * R * β.val with hG
  set Y := (β⁻¹ * x * β).val with hYdef
  set Yi := (β⁻¹ * x⁻¹ * β).val with hYidef
  have hYYi : Y * Yi = 1 := by
    rw [hYdef, hYidef, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Units.val_one]
  have hY : Y = (β⁻¹).val * x.val * β.val := by rw [hYdef, Units.val_mul, Units.val_mul]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ (β⁻¹).val * (Formalism.UG.cT σ β.val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← cT_mul', Units.mul_inv, cT_one', Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) A, β.val * ((β⁻¹).val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hUY : Formalism.UG.cT σ Y * G * Y = G := by
    rw [hY, hG, cT_mul', cT_mul']
    simp only [Matrix.mul_assoc, c1, c2]
    rw [show Formalism.UG.cT σ x.val * (R * (x.val * β.val)) = (Formalism.UG.cT σ x.val * R * x.val) * β.val by
        simp only [Matrix.mul_assoc], hX]
  have hGY : G * Y = Formalism.UG.cT σ Yi * G := by
    have := congrArg (fun Z => Formalism.UG.cT σ Yi * Z) hUY
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', hYYi, cT_one', Matrix.one_mul]
  have e1 : Y = U' * (G * Y) := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc Y - 1 = U' * (G * Y) - U' * G := by rw [← e1, hU]
    _ = U' * (Formalism.UG.cT σ Yi * G) - U' * G := by rw [hGY]
    _ = U' * (Formalism.UG.cT σ Yi - 1) * G := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

theorem frame_mat_sub_one_lt : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hM : ∀ i j, Valued.v (cpt (cP Q) ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j)) < 1 := by
    intro i j
    have e : (Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j =
        sg D ((β⁻¹ * (finE V g)⁻¹ * β).val j i - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) j i) := by
      simp only [Formalism.UG.cT, Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    rw [e]
    exact cpt_sg_lt_one Q _ (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (cP Q) x) ≤ 1 := fun x hx => (mem_OA x).1 hx (cP Q)
  rw [← Matrix.sub_apply, hYsub, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt' _ zero_lt_one fun j _ => ?_
  rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hint _ (hGi j b))) ?_
  refine Valuation.map_sum_lt' _ zero_lt_one fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _ (hU'i a i))) (hM i j)

end GlobalTheory.ConjLt
