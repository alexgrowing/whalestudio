import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerLLocPolyNeZeroFarRight

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.euler_product_nonvanishing_right :
    ∀ (D : Ad3.Dat) (c : HeckeCharacter ℚ) (S : Set Ad3.Pl) (s : ℂ), 2 < s.re → eulerL ℚ (par D (toH c)) S s ≠ 0 := by
  intro D c S s hs
  have hx : ∀ p : Ad3.Pl, ‖(((toH c).val p : ℂˣ) : ℂ)‖ = 1 := by
    intro p
    have e : (toH c).val p = localChar c p (Formalism.L2.Host.atFin p (Formalism.L2.Host.unif p)) := rfl
    rw [e, GroundTheory.Automorphic.GodementSection.coe_localChar]
    exact Circle.norm_coe _
  have hn : ∀ p : Ad3.Pl, ‖((D.ν p (unif (p.adicCompletion ℚ)) : ℂˣ) : ℂ)‖ = 1 := fun p => (D.unit p).2 _
  refine (eulerL_locPoly_ne_zero_far_right ℚ 3 S
    (fun p => ({D.ν p (unif (p.adicCompletion ℚ)) * (toH c).val p, (toH c).val p,
      (D.ν p (unif (p.adicCompletion ℚ)))⁻¹ * (toH c).val p} : Multiset ℂˣ)) 0 (fun w _ => rfl) ?_ s
    (by simpa using hs)).1
  intro w _ b hb
  rw [Real.rpow_zero]
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · rw [Units.val_mul, norm_mul, hn, hx, one_mul]
  · rw [hx]
  · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hn, hx, inv_one, one_mul]
