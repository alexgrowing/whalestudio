import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotCompatCyc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedPairLineIff

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.LocGlobAll.Model

namespace GlobalTheory.LocGlobDual.Model

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

theorem theta_form (hG : GlobalTheory.Published.GelfandKazhdanDual) (H : GlobalTheory.Published.CaraianiLocalGlobalDual) :
    GlobalTheory.Published.CaraianiLocalGlobal := fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh =>
  H E Ω l ι a ha π (dualIsConj_of_isCsd (hG E a π) hc) hcoh

theorem dualIsConj_iso {π π' : CuspSub L a} (h : π.Iso π') (hd : DualIsConj π) : DualIsConj π' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := hd
  have hT' : ∀ o φ, T.symm (π'.op o φ) = π.op o (T.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hT, LinearEquiv.apply_symm_apply]
  refine ⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ T.symm.injective).1 (h1 _ fun x => by simpa using h (T x))
  · exact (map_eq_zero_iff _ T.symm.injective).1 (h2 _ fun x => by simpa using h (T x))
  · simp [hT', h3]
  · simp [hT', h4]
  · simp [hT', h5]

theorem central_eq_zero {π : CuspSub L a} (hd : DualIsConj π) {c : ℂ} (hc : ∀ φ, π.op (.lie (oneL L a)) φ = c • φ) :
    c = 0 := by
  obtain ⟨B, h1, -, -, -, h5⟩ := hd
  have e : conjOp (.lie (oneL L a)) = (.lie (oneL L a) : Op L a) := by
    change Op.lie _ = _
    congr 1
    funext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  by_contra hne
  refine h0 (congrArg Subtype.val (h1 ⟨φ, hφ⟩ fun ψ => ?_))
  have := h5 (oneL L a) ⟨φ, hφ⟩ ψ
  rw [e, hc, hc, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, ← two_mul] at this
  simpa [hne] using this

variable (Ω : Type) [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem compat_of (H : GlobalTheory.Published.CaraianiLocalGlobalDual) (ha : 2 ≤ a) (π : CuspSub L a) (hc : DualIsConj π)
    (hcoh : GKCoh.IsCohomological π) : ∃ R, Compat Ω ι π R := H L Ω l ι a ha π hc hcoh

theorem triv_all : DualIsConj (CuspSub.triv L (le_refl 1)) ∧ GKCoh.IsCohomological (CuspSub.triv L (le_refl 1)) ∧
    Compat Ω ι (CuspSub.triv L (le_refl 1)) 1 := by
  refine ⟨?_, ⟨_, GKCoh.isCohFor_triv le_rfl⟩, compat_triv Ω ι⟩
  have h := GlobalTheory.ContraPair.Model.polarizedPair_triv (L := L).dual
  rwa [pow_one, GlobalTheory.GalOfCusp.compNorm_quadChar, dualIsConjBy_one] at h

end GlobalTheory.LocGlobDual.Model

end
