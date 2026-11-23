import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PhiEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHasEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPPart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntConj

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw Gam0 rat sim mat th th0 invT_val mem_lev comp_th sim_th th_rat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open GlobalTheory.LFun (KGL)
open Formalism.UG (Hecke conv hAct)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem frame_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]
    {S : Setup A n p} (F : Frame S) (g : GUf E n) : F.th g = th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem th_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} (hn : 0 < n) (w₀ : Plc E) (S₀ : Finset (Plc E))
    (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (hS : ∀ u ∈ S₀, (p : 𝓞 E) ∉ u.asIdeal) (k : GUf E n)
    (h1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) (h2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w n) :
    th k ∈ lev S₀ Kw := by
  have hall : ∀ w : Plc E, comp w k ∈ KGL w n := fun w => by
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · exact h2 w hw
    · rw [h1 w hw]; exact one_mem _
  have hsim : sim k ∈ CertificateRingHomMap.ZU := ((pIntConj E n k w₀ hn).2.1 hall)
  refine mem_lev.2 ⟨by rw [sim_th]; exact inv_mem hsim, fun w hw => ?_, fun w _ _ => ?_⟩
  · rw [comp_th, h1 w (hS w hw)]
    have : GlobalTheory.CuspRep.invT n _ (1 : GLw n w) = 1 := map_one _
    rw [this]; exact one_mem _
  · rw [comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hall w)

theorem eigEx : EigEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  refine ⟨(GlobalTheory.CuspRep.invT n E).prodMap invMonoidHom, fun y => ⟨rfl, rfl⟩, fun J g θ hg => ?_⟩
  obtain ⟨φ, hφ0, hφT, hφj, hφe⟩ := phiEx E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  have hkey : ∀ h, V.Φ (th (F.tr.sec h)) = φ h := fun h => by
    have := hφj (F.tr.sec h) fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _
    rw [frame_th, F.j_tr, F.tr.j_sec] at this
    exact this.symm
  have hfun : (fun h => V.Φ (th (F.tr.sec h))) = φ := funext hkey
  have hCen : Ty.Cen 1 := ⟨fun g => by simp, map_one _⟩
  refine pHasEigOf (pStdForm pMuStar) pPInt (pPPart pJEq) pExtP E A n p S F.tr _ ((CertificateRingHomMap.xi V.W V.jz).comp _) (fun g => V.Φ (th g))
    (fun γ g => ?_) (fun k h1 h2 g => ?_) ?_ Ty.K₀ Ty.cms (fun k hk h => ?_) J (fun j => (g j).fn) θ (Ty.tf 1)
    (fun j => (memFn E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy (g j) (θ j) (hg j)).1)
    (pTfAdm _ _ Ty 1 (map_one _)).1.1 ?_ (fun j => ?_)
  · show V.Φ (th (rat γ * g)) = _
    rw [map_mul, th_rat, V.form.left]
    rfl
  · have hpos : Odd n → 0 < n := Odd.pos
    have hk := th_mem (hpos hn) w₀ V.S V.Kw hOff.1 k h1 h2
    have hw₀ : (p : 𝓞 E) ∉ w₀.asIdeal := hOff.1 _ V.shape.mem
    have hc : comp w₀ (th k) = 1 := by
      rw [comp_th, h1 w₀ hw₀]; exact map_one _
    have hJ : comp w₀ (th k) ∈ V.J := by rw [hc]; exact one_mem _
    show V.Φ (th (g * k)) = V.Φ (th g)
    have hr' := V.form.right (th k) hk hJ (th g)
    have hone : V.χ ⟨comp w₀ (th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (th k), hJ⟩ : V.J) = 1 := Subtype.ext hc
      rw [this, map_one]
    rw [map_mul, hr', hone]
    simp
  · obtain ⟨h, hh⟩ := Function.ne_iff.1 hφ0
    exact ⟨F.tr.sec h, by rw [hkey]; exact hh, fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _⟩
  · rw [hkey, hkey, hφT k (Ty.le hk) h, Ty.ker k hk]
    simp
  · rw [hfun]
    funext a
    have := pTfCen pAvgK pTfAdm _ _ Ty 1 hCen _ φ hφT a
    simpa using this
  · rw [hfun]
    exact hφe (g j) (θ j) (hg j)

end UpperTheory.Gal.Spc
