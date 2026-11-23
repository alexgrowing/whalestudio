import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiDetValues

set_option maxHeartbeats 1000000 in

theorem res_mem {D : D7} (S : Subfield ℂ) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    (hS : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ S)
    (P : Pl D.host.E) (ψ : (kP P)ˣ →* ℂˣ) (hψ : IsRes χ P ψ⁻¹) (u : (kP P)ˣ) : ((ψ u : ℂˣ) : ℂ) ∈ S := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  have h4 := hψ a (Units.mk0 _ ha0) u rfl ha.symm
  have h5 := hc.2 P e he (Units.mk0 _ ha0) (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) rfl
  have h6 := hS (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) (by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add, RingHom.map_one, RingHom.map_mul, hinf,
      zero_mul, add_zero])
  rw [h5, ← h4, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h6
  exact inv_mem_iff.1 h6

set_option maxHeartbeats 1000000 in

theorem chiC_mem_coeff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL t i g
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  have hA := (t.chiR i D.what₂.embLL hσ).2.2.2.1
  have h : ((chiC R i g : ℂˣ) : ℂ) ∈ (res T D.what₂.embLL).fieldRange := by
    unfold chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy, -⟩ := hA x hx
    exact ⟨y, hy.symm⟩
  exact h

end GlobalTheory.ChiDetValues
