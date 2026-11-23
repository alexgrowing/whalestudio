import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Beta

variable {D : D7} (Z : LocDat D) (p : PlF D)

def betaL (β : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  (Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).constr (D.s.atP p).Ep fun i => baseChange₂ D p (β ((VS D).frame i))

theorem baseChangeAt_eq_sum (x : (VS D).V) :
    baseChange₂ D p x = ∑ i, (D.s.atP p).ιE ((VS D).frame.repr x i) • Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i := by
  funext j
  have hj : baseChange₂ D p x j = (D.s.atP p).ιE ((VS D).frame.repr x j) := rfl
  simp [hj, Finset.sum_apply, Pi.single_apply]

theorem betaL_bc (β : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    betaL p β (baseChange₂ D p x) = baseChange₂ D p (β x) := by
  have hx : x = ∑ i, (VS D).frame.repr x i • (VS D).frame i := ((VS D).frame.sum_repr x).symm
  rw [baseChangeAt_eq_sum p x, map_sum]
  conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, baseChange_smul₂]
  congr 1
  simp only [betaL, Module.Basis.constr_basis]

theorem betaL_basis (β : (VS D).V →ₗ[D.host.E] (VS D).V) (i : Fin (nV D)) :
    betaL p β (Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i) = baseChange₂ D p (β ((VS D).frame i)) := by
  simp only [betaL, Module.Basis.constr_basis]

def betaP (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p :=
  LinearEquiv.ofLinear (betaL p (β : (VS D).V →ₗ[D.host.E] (VS D).V))
    (betaL p (β.symm : (VS D).V →ₗ[D.host.E] (VS D).V))
    ((Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [betaL_basis, betaL_bc, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        baseChangeAt_frame, Pi.basisFun_apply])
    ((Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [betaL_basis, betaL_bc, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        baseChangeAt_frame, Pi.basisFun_apply])

theorem betaP_bc (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    betaP p β (baseChange₂ D p x) = baseChange₂ D p (β x) := by
  show betaL p (β : (VS D).V →ₗ[D.host.E] (VS D).V) (baseChange₂ D p x) = _
  rw [betaL_bc]
  rfl

theorem betaP_symm_bc (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    (betaP p β).symm (baseChange₂ D p x) = baseChange₂ D p (β.symm x) := by
  show betaL p (β.symm : (VS D).V →ₗ[D.host.E] (VS D).V) (baseChange₂ D p x) = _
  rw [betaL_bc]
  rfl

theorem vp_eq_sum (v : Vp D p) : v = ∑ i, v i • baseChange₂ D p ((VS D).frame i) := by
  funext j
  simp [baseChangeAt_frame, Finset.sum_apply, Pi.single_apply]

private theorem h_bc_lemma (u w : (VS D).V) :
    (locH Z p).h (baseChange₂ D p u) (baseChange₂ D p w) = (D.s.atP p).ιE (brS (VS D) u w) := by
  have hb : ∀ (v : (VS D).V) (k : Fin (nV D)), baseChange₂ D p v k = (D.s.atP p).ιE ((VS D).frame.repr v k) :=
    fun _ _ => rfl
  have hu : u = ∑ k, (VS D).frame.repr u k • (VS D).frame k := ((VS D).frame.sum_repr u).symm
  have hw : w = ∑ l, (VS D).frame.repr w l • (VS D).frame l := ((VS D).frame.sum_repr w).symm
  show LocFacts₂ Z.M p (baseChange₂ D p u) (baseChange₂ D p w) = _
  simp only [LocFacts₂, hb, cj_iota (Z.hcj p), gramV, brS]
  conv_rhs => rw [hw, hu]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem h_sum_bc {ι : Type} [Fintype ι] (a b : ι → (D.s.atP p).Ep) (x y : ι → (VS D).V) :
    (locH Z p).h (∑ i, a i • baseChange₂ D p (x i)) (∑ j, b j • baseChange₂ D p (y j)) =
      ∑ i, ∑ j, a i * (Z.M p).L.cj (b j) * (D.s.atP p).ιE (brS (VS D) (x i) (y j)) := by
  have hL : ∀ (f : ι → Vp D p) (w : Vp D p),
      (locH Z p).h (∑ i, f i) w = ∑ i, (locH Z p).h (f i) w := fun f w =>
    map_sum (AddMonoidHom.mk' (fun v => (locH Z p).h v w) fun v v' => (locH Z p).h_add_left v v' w) f
      Finset.univ
  have hR : ∀ (v : Vp D p) (g : ι → Vp D p),
      (locH Z p).h v (∑ j, g j) = ∑ j, (locH Z p).h v (g j) := by
    intro v g
    rw [(locH Z p).h_herm (∑ j, g j) v, hL, map_sum]
    exact Finset.sum_congr rfl fun j _ => ((locH Z p).h_herm (g j) v).symm
  have hS : ∀ (v : Vp D p) (c : (D.s.atP p).Ep) (w : Vp D p),
      (locH Z p).h v (c • w) = (Z.M p).L.cj c * (locH Z p).h v w := by
    intro v c w
    rw [(locH Z p).h_herm (c • w) v, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm w v]
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(locH Z p).h_smul_left, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hS, h_bc_lemma]
  ring

theorem betaP_iso (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y) (v w : Vp D p) :
    (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := by
  rw [vp_eq_sum p v, vp_eq_sum p w]
  simp only [map_sum, map_smul, betaP_bc]
  rw [h_sum_bc, h_sum_bc]
  simp only [brS, hiso]

theorem betaP_lat (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hβ : ∀ v ∈ Λ, β v ∈ Λ) {x : Vp D p} (hx : x ∈ lattice₂ D Z.M p Λ) : betaP p β x ∈ lattice₂ D Z.M p Λ := by
  unfold lattice₂ at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [betaP_bc]
    exact Submodule.subset_span ⟨β v, hβ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have e : betaP p β (c • y) = c • betaP p β y := LinearMapClass.map_smul_of_tower _ c y
    rw [e]
    exact Submodule.smul_mem _ c hy

theorem betaP_symm_lat (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hβ : ∀ v ∈ Λ, β.symm v ∈ Λ) {x : Vp D p} (hx : x ∈ lattice₂ D Z.M p Λ) :
    (betaP p β).symm x ∈ lattice₂ D Z.M p Λ := by
  unfold lattice₂ at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [betaP_symm_bc]
    exact Submodule.subset_span ⟨β.symm v, hβ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have e : (betaP p β).symm (c • y) = c • (betaP p β).symm y := LinearMapClass.map_smul_of_tower _ c y
    rw [e]
    exact Submodule.smul_mem _ c hy

theorem bcP_mem_X (u : Fin (D.R.rS + 1) → (VS D).V) (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep)
    (hc : ∀ a, IsUnit (c a)) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => u a.castSucc)) :
    baseChange₂ D p x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a)) := by
  show baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc))
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show baseChange₂ D p (u a.castSucc) ∈ _
    have h1 : baseChange₂ D p (u a.castSucc) =
        (((hc a.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • (c a.castSucc • baseChange₂ D p (u a.castSucc)) := by
      rw [smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hy

theorem betaP_mem_X (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u v : Fin (D.R.rS + 1) → (VS D).V)
    (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hc : ∀ a, IsUnit (c a))
    (hmap : ∀ a : Fin D.R.rS, β (u a.castSucc) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => v b.castSucc))
    {x : Vp D p} (hx : x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a))) :
    betaP p β x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (v a)) := by
  show betaP p β x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (v a.castSucc))
  replace hx : x ∈ Submodule.span (D.s.atP p).Ep
      (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc)) := hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show betaP p β (c a.castSucc • baseChange₂ D p (u a.castSucc)) ∈ _
    rw [map_smul, betaP_bc]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p v c hc (hmap a))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

theorem betaP_symm_mem_X (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u v : Fin (D.R.rS + 1) → (VS D).V)
    (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hc : ∀ a, IsUnit (c a))
    (hmap : ∀ a : Fin D.R.rS, β.symm (v a.castSucc) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => u b.castSucc))
    {x : Vp D p} (hx : x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (v a))) :
    (betaP p β).symm x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a)) := by
  show (betaP p β).symm x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc))
  replace hx : x ∈ Submodule.span (D.s.atP p).Ep
      (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (v a.castSucc)) := hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show (betaP p β).symm (c a.castSucc • baseChange₂ D p (v a.castSucc)) ∈ _
    rw [map_smul, betaP_symm_bc]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p u c hc (hmap a))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

end Beta

end Formalism.L2.SG.Pf.ScalarFramePf
