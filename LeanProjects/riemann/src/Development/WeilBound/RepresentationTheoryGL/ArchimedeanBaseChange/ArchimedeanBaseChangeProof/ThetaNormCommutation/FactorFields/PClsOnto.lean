import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsOntoP

theorem only_rho {k : Type} [Field k] [CharZero k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type}
    [CommRing B] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (hs0 : s ≠ 0) (hcs : c s = -s)
    (x : GL (Fin n) k) (hx : x * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * x)
    (hk : x * δ * thetaGL n c x = δ) : ∃ u, x.val = ρ u := by
  obtain ⟨u, v, huv⟩ := hF.span x.val (by simpa only [Units.val_mul] using congrArg Units.val hx)
  have hA := ClsEqP.A_delta_theta hF hcs x u v huv
  have e : x.val * (δ * thetaGL n c x).val = (ρ u - s • ρ v) * (δ * thetaGL n c x).val := by
    have hk' : x.val * (δ.val * (thetaGL n c x).val) = δ.val := by
      have := congrArg Units.val hk
      simpa only [Units.val_mul, Matrix.mul_assoc] using this
    rw [Units.val_mul, hA, hk']
  have h0 : x.val = ρ u - s • ρ v := by
    have := congrArg (· * ((δ * thetaGL n c x)⁻¹).val) e
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
  have e2 : s • ρ v = -(s • ρ v) := by
    have := huv.symm.trans h0
    rw [sub_eq_add_neg] at this
    exact add_left_cancel this
  have e3 : (2 * s) • ρ v = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [e2]
    exact add_neg_cancel _
  have hv : ρ v = 0 := (smul_eq_zero.mp e3).resolve_left (mul_ne_zero two_ne_zero hs0)
  exact ⟨u, by rw [huv, hv, smul_zero, add_zero]⟩

end PositivityTheory.Rg.BcB.G3.ClsOntoP

namespace PositivityTheory.Rg.BcB.G3

theorem clsOnto_pf : ClsOnto := by
  intro k _ _ n c hc δ s hs0 hcs B _ d ρ hF hsep y hy
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable k n (δ * thetaGL n c δ) (y * thetaGL n c y)
    hy.symm hsep
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) k, y' = h * y * (thetaGL n c h)⁻¹ := ⟨_, rfl⟩
  have hy'N : y' * thetaGL n c y' = δ * thetaGL n c δ := by
    rw [hy']
    simp only [map_mul, map_inv, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc]
    calc h * y * (thetaGL n c h)⁻¹ * (thetaGL n c h * thetaGL n c y * h⁻¹) = h * (y * thetaGL n c y) * h⁻¹ := by
          group
      _ = δ * thetaGL n c δ := by rw [hh]; group
  have hT : thetaGL n c y' * y' = thetaGL n c δ * δ := by
    have := congrArg (thetaGL n c) hy'N
    simpa only [map_mul, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc] using this
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin n) k, a = y' * δ⁻¹ := ⟨_, rfl⟩
  have hcomm : a * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a := by
    calc a * (δ * thetaGL n c δ) = y' * (thetaGL n c δ * δ) * δ⁻¹ := by rw [ha]; group
      _ = y' * (thetaGL n c y' * y') * δ⁻¹ := by rw [hT]
      _ = (y' * thetaGL n c y') * (y' * δ⁻¹) := by group
      _ = (δ * thetaGL n c δ) * a := by rw [hy'N, ha]
  have hkey : a * δ * thetaGL n c a = δ := by
    rw [ha]
    simp only [map_mul, map_inv]
    calc y' * δ⁻¹ * δ * (thetaGL n c y' * (thetaGL n c δ)⁻¹) = (y' * thetaGL n c y') * (thetaGL n c δ)⁻¹ := by
          group
      _ = δ := by rw [hy'N]; group
  have hcomm' : a⁻¹ * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a⁻¹ := by
    calc a⁻¹ * (δ * thetaGL n c δ) = a⁻¹ * ((δ * thetaGL n c δ) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (δ * thetaGL n c δ)) * a⁻¹ := by rw [hcomm]
      _ = (δ * thetaGL n c δ) * a⁻¹ := by group
  have hkey' : a⁻¹ * δ * thetaGL n c a⁻¹ = δ := by
    calc a⁻¹ * δ * thetaGL n c a⁻¹ = a⁻¹ * (a * δ * thetaGL n c a) * thetaGL n c a⁻¹ := by rw [hkey]
      _ = δ := by rw [map_inv]; group
  obtain ⟨u, hu⟩ := ClsOntoP.only_rho hF hs0 hcs a hcomm hkey
  obtain ⟨u', hu'⟩ := ClsOntoP.only_rho hF hs0 hcs a⁻¹ hcomm' hkey'
  have huu : u * u' = 1 := by
    apply hF.inj
    rw [map_mul, ← hu, ← hu', Units.mul_inv, map_one]
  let t : Bˣ := ⟨u, u', huu, by rw [mul_comm, huu]⟩
  have hta : Units.map ρ.toMonoidHom t = a := by
    apply Units.ext
    rw [ClsNormP.units_map_val, hu]
  refine ⟨t, h, ?_⟩
  have hpt : pt δ ρ t = y' := by
    rw [pt, hta, ha]; group
  rw [hpt, hy']
  group

end PositivityTheory.Rg.BcB.G3

end
