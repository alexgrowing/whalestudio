import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open Formalism.UG (Tj Ov IsUnifV)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_⟩
  intro V _ _ ρ x
  rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem sum_mem_forms (hC : LocComm) (hM : LocMem) {w : Plc E} (hw : IsSplitAt w) {h : GLw n w → ℂ}
    (hh : h ∈ Formalism.UG.Hecke ℂ (KGL w n)) {R : Finset (GLw n w)}
    (hR : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
      heckeVec ρ (KGL w n) h v = ∑ g ∈ R, ρ g v)
    {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} (hS : w ∉ S) (hcS : cj w ∉ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ξ : Representation ℂ (Gam0 E n) V} {Φ : GUf E n → V}
    (hΦ : Φ ∈ forms rat (lev S Kw) ξ) :
    (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ := by
  have hloc : ∀ y ∈ KGL w n, loc hw y ∈ lev S Kw := fun y hy => (hM E n S Kw w hw hcS y).2 hS hy
  let ρ : Representation ℂ (GLw n w) (GUf E n → V) := (rightReg ℂ (GUf E n) V).comp (loc hw)
  have hρ : ∀ y (f : GUf E n → V) g, ρ y f g = f (g * loc hw y) := fun _ _ _ => rfl
  have hfix : Φ ∈ fixed ρ (KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    funext g
    rw [hρ]
    exact hΦ.2 _ (hloc k hk) g
  have hΨ := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed (Formalism.UG.Final.GLintComm E w n) hh hfix
  rw [hR] at hΨ
  have hΨ' := GlobalTheory.LGrp.mem_fixed.1 hΨ
  have hev : ∀ g, (∑ y ∈ R, ρ y Φ) g = ∑ y ∈ R, Φ (g * loc hw y) := fun g => by
    rw [Finset.sum_apply]
    rfl
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  · simp only [map_sum, mul_assoc]
    exact Finset.sum_congr rfl fun y _ => hΦ.1 γ _
  · have hx : comp w k ∈ KGL w n := (mem_lev.1 hk).2.2 w hS hcS
    set x := comp w k with hxdef
    set k' := (loc hw x)⁻¹ * k with hk'def
    have hk'm : k' ∈ lev S Kw := (lev S Kw).mul_mem ((lev S Kw).inv_mem (hloc x hx)) hk
    have hk'1 : comp w k' = 1 := by
      rw [hk'def, map_mul, map_inv, comp_loc, ← hxdef, inv_mul_cancel]
    have hcomm := (hC E n w hw).1 k' hk'1
    have hkk : k = loc hw x * k' := by rw [hk'def, mul_inv_cancel_left]
    have e1 : ∀ y, Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y) := fun y => by
      calc Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y * k') := by
            rw [hkk, mul_assoc g, mul_assoc _ k', hcomm y]; simp only [mul_assoc]
        _ = _ := hΦ.2 _ hk'm _
    have e2 := congrFun (hΨ' x hx) g
    rw [hρ, hev, hev] at e2
    show ∑ y ∈ R, Φ (g * k * loc hw y) = ∑ y ∈ R, Φ (g * loc hw y)
    rw [← e2]
    exact Finset.sum_congr rfl fun y _ => e1 y

theorem pHeckePres_of (hC : LocComm) (hM : LocMem) : HeckePres := by
  intro E _ _ _ n w hw ϖ hϖ i
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ i
  obtain ⟨R, hR⟩ := hecke_eq_sum (KGL w n) (Tj ℂ n (Ov E w) ϖ i) (fun g hg => tj_one g hg)
    (Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) hh.2)
  exact ⟨R, hR, fun S Kw hS hcS V _ _ ξ Φ hΦ => sum_mem_forms hC hM hw hh hR hS hcS hΦ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
