import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZ
import Lemmata.GeneralBFactThirdTerForm.Imports

noncomputable section

open scoped Classical TensorProduct
open Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Level

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatDict

section Basic

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fix_inv_of_fix (g : X.B.I.Gf) {v : VA X.B.I} (hv : X.B.I.fmat g *ᵥ v = v) :
    X.B.I.fmat g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← hv]
  rw [mulVec_mulVec, fmat_inv_mul, one_mulVec]

theorem fix_sub_prA (g : X.B.I.Gf)
    (he : ∀ a, X.B.I.fmat g *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a))
    (hf : ∀ a, X.B.I.fmat g *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a)) (y : VA X.B.I) :
    X.B.I.fmat g *ᵥ (y - prA X y) = y - prA X y := by
  have e : y - prA X y = ∑ a, hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a) +
      ∑ a, hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a) := by
    rw [prA_apply]; abel
  rw [e, mulVec_add, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, he, hf]

theorem prA_comm (g : X.B.I.Gf)
    (he : ∀ a, X.B.I.fmat g *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a))
    (hf : ∀ a, X.B.I.fmat g *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a)) (y : VA X.B.I) :
    prA X (X.B.I.fmat g *ᵥ y) = X.B.I.fmat g *ᵥ prA X y := by
  have c1 : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat g *ᵥ y) = hA X.B.I (incl X.B.I (X.fR a)) y := by
    intro a
    have := hA_fmat X g (incl X.B.I (X.fR a)) y
    rw [hf a] at this
    exact this
  have c2 : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) (X.B.I.fmat g *ᵥ y) = hA X.B.I (incl X.B.I (X.eR a)) y := by
    intro a
    have := hA_fmat X g (incl X.B.I (X.eR a)) y
    rw [he a] at this
    exact this
  have h1 := fix_sub_prA X g he hf y
  have h2 : prA X (X.B.I.fmat g *ᵥ y) = X.B.I.fmat g *ᵥ y - (y - prA X y) := by
    rw [prA_apply, prA_apply]
    simp only [c1, c2]
    abel
  rw [h2, ← h1, ← mulVec_sub]
  congr 1
  abel

abbrev Tm (h : Hfin X u) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹)

theorem hx_fix_e (h : Hfin X u) (a : Fin D.R.rS) :
    X.B.I.fmat ((h : X.B.I.Gf) * X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := by
  rw [fmat_mul, ← mulVec_mulVec]
  have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
  rw [h1, hfin_fix X u h _ (eR_mem_fix X u a)]

theorem hx_fix_f (h : Hfin X u) (a : Fin D.R.rS) :
    X.B.I.fmat ((h : X.B.I.Gf) * X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := by
  rw [fmat_mul, ← mulVec_mulVec]
  have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  rw [h1, hfin_fix X u h _ (fR_mem_fix X u a)]

theorem Tm_fix_e (h : Hfin X u) (a : Fin D.R.rS) : Tm X u h *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
  fix_inv_of_fix X _ (hx_fix_e X u h a)

theorem Tm_fix_f (h : Hfin X u) (a : Fin D.R.rS) : Tm X u h *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
  fix_inv_of_fix X _ (hx_fix_f X u h a)

theorem mem_latOf (h : Hfin X u) (y : (VS D).V) :
    y ∈ latOf X u h ↔ Tm X u h *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf :=
  Iff.rfl

theorem crd_prV (y : (VS D).V) : X.crd (prV X y) = prE X (X.crd y) := by
  conv_lhs => rw [← toV_crd X y, ← toV_prE, crd_toV]

theorem crd_sub_prV (y : (VS D).V) : X.crd (y - prV X y) = X.crd y - prE X (X.crd y) := by
  conv_lhs => rw [← toV_crd X y, ← toV_prE, ← toV_sub, crd_toV]

theorem mem_hermitianStandardLattice_iff_pairing_integral (v : (VS D).V) : v ∈ (VS D).L0 ↔ X.crd v ∈ X.B.I.L := by
  rw [X.L_eq]
  show v ∈ (VS D).L0 ↔ toV X (X.crd v) ∈ (VS D).L0
  rw [toV_crd]

theorem mem_base_lattice_of_adelic {v : (VS D).V} (hv : incl X.B.I (X.crd v) ∈ X.B.I.Lf) : v ∈ (VS D).L0 :=
  (mem_hermitianStandardLattice_iff_pairing_integral X v).2 (PIW.AdelClassFin.lattice_intersection' X.B.I _ hv)

theorem adelic_mem_of_base_lattice {v : (VS D).V} (hv : v ∈ (VS D).L0) : incl X.B.I (X.crd v) ∈ X.B.I.Lf :=
  incl_mem_Lf X _ ((mem_hermitianStandardLattice_iff_pairing_integral X v).1 hv)

theorem mem_latOf_split (h : Hfin X u) (y : (VS D).V) :
    y ∈ latOf X u h ↔ y - prV X y ∈ (VS D).L0 ∧ prV X y ∈ latOf X u h := by
  have hc1 : incl X.B.I (X.crd (prV X y)) = prA X (incl X.B.I (X.crd y)) := by
    rw [crd_prV, prA_incl]
  have hc2 : incl X.B.I (X.crd (y - prV X y)) =
      incl X.B.I (X.crd y) - prA X (incl X.B.I (X.crd y)) := by
    rw [crd_sub_prV, incl_sub, prA_incl]
  have hfix : Tm X u h *ᵥ (incl X.B.I (X.crd y) - prA X (incl X.B.I (X.crd y))) =
      incl X.B.I (X.crd y) - prA X (incl X.B.I (X.crd y)) :=
    fix_sub_prA X _ (Tm_fix_e X u h) (Tm_fix_f X u h) _
  have hcomm : prA X (Tm X u h *ᵥ incl X.B.I (X.crd y)) = Tm X u h *ᵥ prA X (incl X.B.I (X.crd y)) :=
    prA_comm X _ (Tm_fix_e X u h) (Tm_fix_f X u h) _
  rw [mem_latOf, mem_latOf, hc1]
  constructor
  · intro hy
    have h2 : Tm X u h *ᵥ prA X (incl X.B.I (X.crd y)) ∈ X.B.I.Lf := hcomm ▸ prA_Lf X _ hy
    refine ⟨mem_base_lattice_of_adelic X ?_, h2⟩
    rw [hc2, ← hfix, mulVec_sub]
    exact sub_mem hy h2
  · rintro ⟨h1, h2⟩
    have h1' := adelic_mem_of_base_lattice X h1
    rw [hc2, ← hfix] at h1'
    have e : Tm X u h *ᵥ incl X.B.I (X.crd y) =
        Tm X u h *ᵥ (incl X.B.I (X.crd y) - prA X (incl X.B.I (X.crd y))) +
          Tm X u h *ᵥ prA X (incl X.B.I (X.crd y)) := by
      rw [← mulVec_add, sub_add_cancel]
    rw [e]
    exact add_mem h1' h2

end Basic

section VProj

variable {D : D7} (X : HidaSetting D)

theorem hT_herm (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have h := (VS D).herm.eq x y
  rw [← h]
  rfl

theorem hT_f_prV (a : Fin D.R.rS) (v : (VS D).V) : (VS D).hT (X.fY a) (prV X v) = 0 := by
  simp [prV_apply, map_sub, map_sum, hT_f_e, X.ff]

theorem hT_e_prV (a : Fin D.R.rS) (v : (VS D).V) : (VS D).hT (X.eX a) (prV X v) = 0 := by
  simp [prV_apply, map_sub, map_sum, X.ee, X.ef]

theorem prV_prV (v : (VS D).V) : prV X (prV X v) = prV X v := by
  rw [prV_apply X (prV X v)]
  simp [hT_f_prV, hT_e_prV]

theorem prV_sub_self (v : (VS D).V) : prV X (v - prV X v) = 0 := by
  rw [map_sub, prV_prV, sub_self]

def Xs : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

theorem eX_mem_Xs (a : Fin D.R.rS) : X.eX a ∈ Xs X := Submodule.subset_span ⟨a, rfl⟩

theorem prV_Xs {x : (VS D).V} (hx : x ∈ Xs X) : prV X x = 0 := by
  have : Xs X ≤ LinearMap.ker (prV X) := by
    rw [Xs, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact prV_e X b
  exact this hx

theorem hT_left_span {S : Set (VS D).V} {w : (VS D).V} (hS : ∀ s ∈ S, (VS D).hT s w = 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E S) : (VS D).hT x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]

theorem hT_right_span {S : Set (VS D).V} {w : (VS D).V} (hS : ∀ s ∈ S, (VS D).hT w s = 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E S) : (VS D).hT w x = 0 := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

theorem hT_Xs_prV {x : (VS D).V} (hx : x ∈ Xs X) (w : (VS D).V) : (VS D).hT x (prV X w) = 0 :=
  hT_left_span (by rintro _ ⟨a, rfl⟩; exact hT_e_prV X a w) hx

theorem hT_Xs_Xs {x y : (VS D).V} (hx : x ∈ Xs X) (hy : y ∈ Xs X) : (VS D).hT x y = 0 := by
  refine hT_left_span (fun s hs => ?_) hx
  obtain ⟨a, rfl⟩ := hs
  exact hT_right_span (by rintro _ ⟨b, rfl⟩; exact X.ee a b) hy

theorem sub_prV_eq (v : (VS D).V) :
    v - prV X v = ∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a := by
  rw [prV_apply]; abel

theorem sub_prV_mem_Xs {v : (VS D).V} (hv : ∀ a, (VS D).hT (X.eX a) v = 0) : v - prV X v ∈ Xs X := by
  rw [sub_prV_eq]
  simp only [hv, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (eX_mem_Xs X a)

theorem hT_sub_prV_prV (x y : (VS D).V) : (VS D).hT (x - prV X x) (prV X y) = 0 := by
  rw [sub_prV_eq, map_add, LinearMap.add_apply, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  simp [LinearMap.map_smulₛₗ, hT_e_prV, hT_f_prV]

theorem hT_prV_sub_prV (x y : (VS D).V) : (VS D).hT (prV X x) (y - prV X y) = 0 := by
  rw [hT_herm, hT_sub_prV_prV, star_zero]

theorem hT_decomp (x y : (VS D).V) :
    (VS D).hT x y = (VS D).hT (x - prV X x) (y - prV X y) + (VS D).hT (prV X x) (prV X y) := by
  conv_lhs => rw [← sub_add_cancel x (prV X x), ← sub_add_cancel y (prV X y)]
  simp only [map_add, LinearMap.add_apply, hT_sub_prV_prV, hT_prV_sub_prV, add_zero, zero_add]

end VProj

section GW

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Xa_top : (X.Fu u).Xa D.R.rS = Xs X := by
  rw [FlagG.Xa, Xs, X.Fu_e]
  congr 1
  ext x
  simp

theorem stab_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) (x y : (VS D).V) :
    (VS D).hT (γ x) (γ y) = (VS D).hT x y := hγ.1 x y

theorem stab_Xs {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) {x : (VS D).V}
    (hx : x ∈ Xs X) : γ x ∈ Xs X := by
  have h := hγ.2.1 D.R.rS
  rw [Xa_top] at h
  rw [← h]
  exact Submodule.mem_map_of_mem hx

theorem stab_alt {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) : γ (X.zu u) = X.zu u := by
  have h := hγ.2.2
  rw [X.flagZVector] at h
  exact h

theorem prV_zu : prV X (X.zu u) = X.zu u := by
  simp [prV_apply, (X.zu_orth u _).1, (X.zu_orth u _).2]

def gW (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  (LinearMap.id - prV X) + prV X ∘ₗ (γ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ prV X

theorem gW_apply (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    gW X γ y = (y - prV X y) + prV X (γ (prV X y)) := rfl

theorem prV_gW (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    prV X (gW X γ y) = prV X (γ (prV X y)) := by
  rw [gW_apply, map_add, prV_sub_self, prV_prV, zero_add]

theorem sub_prV_gW (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    gW X γ y - prV X (gW X γ y) = y - prV X y := by
  rw [prV_gW, gW_apply]; abel

theorem stab_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) (w : (VS D).V) :
    γ (prV X w) - prV X (γ (prV X w)) ∈ Xs X := by
  refine sub_prV_mem_Xs X fun a => ?_
  have h1 : (VS D).hT (γ (γ.symm (X.eX a))) (γ (prV X w)) = (VS D).hT (γ.symm (X.eX a)) (prV X w) :=
    stab_isom X u hγ _ _
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  have hs : γ.symm (X.eX a) ∈ Xs X := by
    have h := hγ.2.1 D.R.rS
    rw [Xa_top] at h
    have hm : X.eX a ∈ (Xs X).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := h.symm ▸ eX_mem_Xs X a
    obtain ⟨x, hx, hxe⟩ := hm
    have : γ.symm (X.eX a) = x := by rw [← hxe]; simp
    rw [this]; exact hx
  exact hT_Xs_prV X hs w

theorem hT_prV_stab {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) (x y : (VS D).V) :
    (VS D).hT (prV X (γ (prV X x))) (prV X (γ (prV X y))) = (VS D).hT (prV X x) (prV X y) := by
  have h := hT_decomp X (γ (prV X x)) (γ (prV X y))
  rw [hT_Xs_Xs X (stab_perp X u hγ x) (stab_perp X u hγ y), zero_add, stab_isom X u hγ] at h
  exact h.symm

theorem gW_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) (x y : (VS D).V) :
    (VS D).hT (gW X γ x) (gW X γ y) = (VS D).hT x y := by
  rw [hT_decomp X (gW X γ x), sub_prV_gW, sub_prV_gW, prV_gW, prV_gW, hT_prV_stab X u hγ, ← hT_decomp]

theorem gW_e {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (a : Fin D.R.rS) : gW X γ (X.eX a) = X.eX a := by
  rw [gW_apply, prV_e]; simp

theorem gW_f {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (a : Fin D.R.rS) : gW X γ (X.fY a) = X.fY a := by
  rw [gW_apply, prV_f]; simp

theorem stabilizer_fix_anisotropic {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) : gW X γ (X.zu u) = X.zu u := by
  rw [gW_apply, prV_zu, stab_alt X u hγ, prV_zu]; simp

theorem gW_gW {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) (hδ : δ ∈ stabF D (X.Fu u))
    (hγδ : ∀ w, γ (δ w) = w) (y : (VS D).V) : gW X γ (gW X δ y) = y := by
  have key : prV X (γ (prV X (δ (prV X y)))) = prV X y := by
    have h1 := stab_perp X u hδ y
    have h2 := stab_Xs X u hγ h1
    have h3 := prV_Xs X h2
    rw [map_sub, map_sub, hγδ] at h3
    rw [prV_prV] at h3
    exact (sub_eq_zero.1 h3).symm
  rw [gW_apply X γ, sub_prV_gW, prV_gW, key]
  abel

theorem gW_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h h' : Hfin X u)
    (hmap : ∀ y ∈ latOf X u h, γ y ∈ latOf X u h') {y : (VS D).V} (hy : y ∈ latOf X u h) :
    gW X γ y ∈ latOf X u h' := by
  obtain ⟨h1, h2⟩ := (mem_latOf_split X u h y).1 hy
  have h3 := ((mem_latOf_split X u h' _).1 (hmap _ h2)).2
  refine (mem_latOf_split X u h' _).2 ⟨?_, ?_⟩
  · rw [sub_prV_gW]; exact h1
  · rw [prV_gW]; exact h3

end GW

section Rat

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def ratMat (g : (VS D).V →ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (X.ιE.symm : D.host.E →+* X.B.I.E).mapMatrix (LinearMap.toMatrix X.bas X.bas g)

theorem ratMat_crd (g : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    ratMat X g *ᵥ X.crd y = X.crd (g y) := by
  funext i
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr X.bas X.bas g y) i
  rw [show X.crd (g y) i = X.ιE.symm (X.bas.repr (g y) i) from rfl, ← h2]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ratMat, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem ratMat_comp (f g : (VS D).V →ₗ[D.host.E] (VS D).V) : ratMat X (f ∘ₗ g) = ratMat X f * ratMat X g := by
  rw [ratMat, LinearMap.toMatrix_comp X.bas X.bas X.bas, map_mul]
  rfl

theorem ratMat_id : ratMat X LinearMap.id = 1 := by
  rw [ratMat, LinearMap.toMatrix_id, map_one]

def ratGL (g g' : (VS D).V →ₗ[D.host.E] (VS D).V) (h1 : g ∘ₗ g' = LinearMap.id) (h2 : g' ∘ₗ g = LinearMap.id) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨ratMat X g, ratMat X g', by rw [← ratMat_comp, h1, ratMat_id], by rw [← ratMat_comp, h2, ratMat_id]⟩

theorem hform_crd' (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) = X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crd X v w, RingEquiv.symm_apply_apply]

theorem hform_ratMat (g : (VS D).V →ₗ[D.host.E] (VS D).V) (hg : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y)
    (x y : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (ratMat X g *ᵥ x) (ratMat X g *ᵥ y) =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x y := by
  rw [← crd_toV X x, ← crd_toV X y, ratMat_crd, ratMat_crd, hform_crd', hform_crd', hg]

theorem ratGL_UJ (g g' : (VS D).V →ₗ[D.host.E] (VS D).V) (h1 : g ∘ₗ g' = LinearMap.id)
    (h2 : g' ∘ₗ g = LinearMap.id) (hg : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y) :
    ratGL X g g' h1 h2 ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (ratMat X g) * X.B.I.J * ratMat X g = X.B.I.J
  ext i j
  have := hform_ratMat X g hg (Pi.single i 1) (Pi.single j 1)
  rw [Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single, Formalism.UG.P.hform_single] at this
  exact this

theorem conjT_map (v : InfinitePlace X.B.I.F) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (M.map (X.B.I.φ v))ᴴ = (Formalism.UG.cT (starRingEnd X.B.I.E) M).map (X.B.I.φ v) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply, starRingEnd_apply]
  rw [X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) (M j i)]
  rfl

def rinfU (M : GL (Fin X.B.I.n) X.B.I.E) (v : InfinitePlace X.B.I.F) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ :=
  ⟨(X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v,
    (X.B.I.P v)⁻¹ * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v,
    by
      have e1 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
        rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      calc (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v *
            ((X.B.I.P v)⁻¹ * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)
          = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) *
            ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc ((X.B.I.P v)⁻¹), e1,
              Matrix.mul_one, Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul],
    by
      have e1 : ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      calc (X.B.I.P v)⁻¹ * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v *
            ((X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)
          = (X.B.I.P v)⁻¹ * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
            (X.B.I.P v * (X.B.I.P v)⁻¹) * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc ((X.B.I.P v)⁻¹), e1,
              Matrix.mul_one, Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩

theorem conj_inUJ {m : Type} [Fintype m] [DecidableEq m] (Q A J0 Jm : Matrix m m ℂ) (hQ : Q * Q⁻¹ = 1)
    (hJ : Qᴴ * J0 * Q = Jm) (hA : Aᴴ * J0 * A = J0) : (Q⁻¹ * A * Q)ᴴ * Jm * (Q⁻¹ * A * Q) = Jm := by
  have hQH : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  rw [← hJ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((Q⁻¹)ᴴ) (Qᴴ), hQH, Matrix.one_mul, ← Matrix.mul_assoc Q (Q⁻¹), hQ, Matrix.one_mul,
    ← Matrix.mul_assoc J0 A Q, ← Matrix.mul_assoc Aᴴ (J0 * A) Q, ← Matrix.mul_assoc Aᴴ J0 A, hA]

theorem rinfU_mem (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (v : InfinitePlace X.B.I.F) : rinfU X M v ∈ Formalism.REAL.UJ (X.B.I.ε v) := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hM
  have hA : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v))ᴴ * X.B.I.J.map (X.B.I.φ v) *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = X.B.I.J.map (X.B.I.φ v) := by
    rw [conjT_map, ← Matrix.map_mul, ← Matrix.map_mul, hM']
  exact conj_inUJ _ _ _ _ (Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv X.B.I v) (X.B.I.P_spec v) hA

def rfinU (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) : X.B.I.Gf :=
  ⟨Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) M,
    Formalism.UG.P.rational_points_le_holds X.B.I.F X.B.I.E (Fin X.B.I.n) X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨M, by rw [PIW.AdelClassFin.dictTop_sig]; exact hM, rfl⟩⟩

theorem fmat_rfinU (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    X.B.I.fmat (rfinU X M hM) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := rfl

def ratGam (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y) : Gam X u :=
  ⟨((fun v => ⟨rinfU X M v, rinfU_mem X M hM v⟩), rfinU X M hM), by
    refine Subgroup.mem_inf.2 ⟨⟨M, hM, fun v => rfl, rfl⟩, Subgroup.mem_prod.2 ⟨?_, ?_⟩⟩
    · intro v y hy
      show ((X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) *ᵥ rv X.B.I v y = rv X.B.I v y
      have hφ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ (fun i => X.B.I.φ v (y i)) = fun i => X.B.I.φ v (y i) := by
        funext i
        have h5 := RingHom.map_mulVec (X.B.I.φ v) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i
        rw [hfix y hy] at h5
        exact h5.symm
      simp only [rv]
      rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec _ (X.B.I.P v) ((X.B.I.P v)⁻¹),
        Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, one_mulVec, hφ]
    · intro y hy
      show (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I y = incl X.B.I y
      funext i
      have h5 := RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
        (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i
      rw [hfix y hy] at h5
      exact h5.symm⟩

theorem iotaF_ratGam (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y) :
    ((iotaF X u (ratGam X u M hM hfix) : Hfin X u) : X.B.I.Gf) = rfinU X M hM := rfl

end Rat

section Inj

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem stab_symm {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D (X.Fu u)) :
    γ.symm ∈ stabF D (X.Fu u) := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hγ.1, fun j => ?_, ?_⟩
  · have h := hγ.2.1 j
    ext x
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (FlagG.Xa (X.Fu u) j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := h.symm ▸ hy
      obtain ⟨w, hw, rfl⟩ := hy'
      simpa using hw
    · intro hx
      refine ⟨γ x, ?_, by simp⟩
      rw [← h]
      exact ⟨x, hx, rfl⟩
  · have h := hγ.2.2
    show γ.symm (X.Fu u).z = (X.Fu u).z
    rw [LinearEquiv.symm_apply_eq, h]

theorem kset_iff {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset) (w : VA X.B.I) :
    X.B.I.fmat k⁻¹ *ᵥ w ∈ X.B.I.Lf ↔ w ∈ X.B.I.Lf := by
  have h := hk (X.B.I.fmat k⁻¹ *ᵥ w)
  rw [h]
  show X.B.I.fmat k *ᵥ (X.B.I.fmat k⁻¹ *ᵥ w) ∈ X.B.I.Lf ↔ w ∈ X.B.I.Lf
  rw [mulVec_mulVec, fmat_mul_inv, one_mulVec]

end Inj

section Row

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem int_iff (a : D.host.E) : a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔
    X.ιE.symm a ∈ (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨_, (NumberField.RingOfIntegers.isIntegral_coe b).map
      (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩, rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨⟨_, (NumberField.RingOfIntegers.isIntegral_coe b).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom⟩, ?_⟩
    show X.ιE (b : X.B.I.E) = a
    have hb' : (b : X.B.I.E) = X.ιE.symm a := hb
    rw [hb', RingEquiv.apply_symm_apply]

theorem mem_latOf_Lam (h : Hfin X u) (y : (VS D).V) :
    y ∈ latOf X u h ↔ X.crd y ∈ PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u) := Iff.rfl

theorem crd_smul (c : D.host.E) (y : (VS D).V) : X.crd (c • y) = X.ιE.symm c • X.crd y := by
  conv_lhs => rw [← toV_crd X y, ← RingEquiv.apply_symm_apply X.ιE c, ← toV_smul, crd_toV]

theorem hmem_nsmul (h : Hfin X u) (N : ℕ) (y : (VS D).V) :
    Tm X u h *ᵥ incl X.B.I (X.crd (N • y)) = (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Tm X u h *ᵥ incl X.B.I (X.crd y)) := by
  rw [← mulVec_smul]
  congr 1
  funext i
  simp [incl, HidaSetting.crd, crdOf, nsmul_eq_mul]

theorem incl_crd_nsmul (N : ℕ) (y : (VS D).V) :
    incl X.B.I (X.crd (N • y)) = (N : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.crd y) := by
  funext i
  simp [incl, HidaSetting.crd, crdOf, nsmul_eq_mul]

theorem fg_of_nsmul_le {P L : Submodule (𝓞 D.host.E) (VS D).V} (hL : L.FG) (N : ℕ) (hN : 0 < N)
    (h : ∀ y ∈ P, N • y ∈ L) : P.FG := by
  let f : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := N • LinearMap.id
  have hf : Function.Injective f := by
    intro a b hab
    have e : ((N : D.host.E)) • (a - b) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, smul_sub]
      exact sub_eq_zero.2 hab
    rcases smul_eq_zero.1 e with h0 | h0
    · exact absurd h0 (Nat.cast_ne_zero.2 hN.ne')
    · exact sub_eq_zero.1 h0
  have hle : P.map f ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : ((P.map f).comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 : ((P.map f).comap L.subtype).map L.subtype = P.map f := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.2 hle
  exact Submodule.fg_of_fg_map_injective f hf (h2 ▸ h1.map _)

theorem latOf_isLattice (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : (Λ : Set (VS D).V) = latOf X u h) :
    Submodule.IsLattice D.host.E Λ := by
  obtain ⟨N, hN, hNL⟩ := PIW.AdelClassFin.DictGen.exists_denominator_fmat X.B.I PIW.AdelClassFin.lattice_denominator ((h : X.B.I.Gf) * X.xu u)
  have hL0 := (VS D).standardTuple_isLattice
  have hmemΛ : ∀ y, y ∈ Λ ↔ y ∈ latOf X u h := fun y => by rw [← SetLike.mem_coe, hΛ]
  have h1 : ∀ y ∈ Λ, N • y ∈ (VS D).L0 := by
    intro y hy
    rw [hmemΛ, mem_latOf] at hy
    apply mem_base_lattice_of_adelic X
    rw [incl_crd_nsmul]
    have := (hNL _ hy).1
    rwa [mulVec_mulVec, fmat_mul_inv, one_mulVec] at this
  have h2 : ∀ y ∈ (VS D).L0, N • y ∈ Λ := by
    intro y hy
    rw [hmemΛ, mem_latOf, hmem_nsmul]
    exact (hNL _ (adelic_mem_of_base_lattice X hy)).2
  refine ⟨fg_of_nsmul_le hL0.fg N hN h1, ?_⟩
  rw [eq_top_iff, ← hL0.span_eq_top, Submodule.span_le]
  intro y hy
  have e : y = ((N : D.host.E))⁻¹ • (N • y) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 y hy))

theorem latOf_unimod (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : (Λ : Set (VS D).V) = latOf X u h) :
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  have hSD := PIW.AdelClassFin.lattice_m_dual X.B.I ((h : X.B.I.Gf) * X.xu u)
  have hmemΛ : ∀ y, y ∈ Λ ↔ X.crd y ∈ PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u) :=
    fun y => by rw [← SetLike.mem_coe, hΛ]; rfl
  have key : ∀ y, y ∈ Λ ↔ ∀ w ∈ Λ, (VS D).hT w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [hmemΛ, hSD]
    constructor
    · intro H w hw
      have h3 := H (X.crd w) ((hmemΛ w).1 hw)
      rw [hform_crd'] at h3
      exact (int_iff X _).2 h3
    · intro H w' hw'
      have h3 := H (toV X w') ((hmemΛ _).2 (by rw [crd_toV]; exact hw'))
      rw [int_iff X] at h3
      rw [← crd_toV X w', hform_crd']
      exact h3
  ext y
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [key y]
  rfl

end Row

section Row2

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

open Formalism.MainNotions.S.Lat

theorem fix_line (h : Hfin X u) (c : D.host.E) :
    Tm X u h *ᵥ incl X.B.I (X.crd (c • X.zu u)) = X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (c • X.zu u)) := by
  show X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ _ = _
  have hz := hfin_fix_inv X u h (X.zR u) (zR_mem_fix X u)
  rw [_root_.mul_inv_rev, fmat_mul, ← mulVec_mulVec, crd_smul, incl_smul, mulVec_smul,
    show X.crd (X.zu u) = X.zR u from rfl, hz]

theorem line_mem_iff (h : Hfin X u) (c : D.host.E) : c • X.zu u ∈ latOf X u h ↔ c • X.zu u ∈ (VS D).L0 := by
  rw [mem_latOf, fix_line, kset_iff X (X.xu_K u)]
  exact ⟨mem_base_lattice_of_adelic X, adelic_mem_of_base_lattice X⟩

theorem zero_mem_latOf (h : Hfin X u) : (0 : (VS D).V) ∈ latOf X u h := by
  have := (line_mem_iff X u h 0).2 (by rw [zero_smul]; exact zero_mem _)
  rwa [zero_smul] at this

theorem zu_mem_latOf (h : Hfin X u) : X.zu u ∈ latOf X u h := by
  have := (line_mem_iff X u h 1).2 (by rw [one_smul]; exact Lb_le X (X.zu_Lb u))
  rwa [one_smul] at this

theorem Xsp_eq : Xsp (lf D (X.Fu u)) = Xs X := by
  show (X.Fu u).X = Xs X
  rw [FlagG.X, X.Fu_e]
  rfl

theorem xlam_latOf (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : (Λ : Set (VS D).V) = latOf X u h) :
    XLam Λ (lf D (X.Fu u)) = XLam (VS D).L0 (lf D (X.Fu u)) := by
  have hmemΛ : ∀ y, y ∈ Λ ↔ y ∈ latOf X u h := fun y => by rw [← SetLike.mem_coe, hΛ]
  ext x
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem, Xsp_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := ((mem_latOf_split X u h x).1 ((hmemΛ x).1 h1)).1
    rwa [prV_Xs X h2, sub_zero] at this
  · rintro ⟨h1, h2⟩
    refine ⟨(hmemΛ x).2 ((mem_latOf_split X u h x).2 ⟨?_, ?_⟩), h2⟩
    · rwa [prV_Xs X h2, sub_zero]
    · rw [prV_Xs X h2]; exact zero_mem_latOf X u h

theorem aa_mem_of_eq {a b : Fin D.R.rS} {x : D.host.E} (hx : x ∈ aaD D b) :
    x * (if b = a then 1 else 0) ∈ ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  split_ifs with hba
  · subst hba; rw [mul_one]; exact hx
  · rw [mul_zero]; exact zero_mem _

theorem coef_span1 (a : Fin D.R.rS) {y : (VS D).V} (hy : y ∈ latSpanS (fun a => aaD D a) X.eX) :
    (VS D).hT (X.fY a) y ∈ ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, x, hx, rfl⟩ := hw
    rw [map_smul, hT_f_e, smul_eq_mul]
    exact aa_mem_of_eq hx
  | zero => rw [map_zero]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [map_add]; exact add_mem hw hw'
  | smul o w _ hw =>
    rw [← IsScalarTower.algebraMap_smul D.host.E o w, map_smul, smul_eq_mul, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o hw

theorem coef_span3 (a : Fin D.R.rS) {y : (VS D).V} (hy : y ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY) :
    (VS D).hT (X.fY a) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, x, hx, rfl⟩ := hw
    rw [map_smul, X.ff, smul_zero]
  | zero => rw [map_zero]
  | add w w' _ _ hw hw' => rw [map_add, hw, hw', add_zero]
  | smul o w _ hw =>
    rw [← IsScalarTower.algebraMap_smul D.host.E o w, map_smul, hw, smul_zero]

theorem coefficient_mem_fractional_ideal (a : Fin D.R.rS) {y : (VS D).V} (hy : y ∈ (VS D).L0) :
    (VS D).hT (X.fY a) y ∈ ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  rw [X.Lam_split] at hy
  obtain ⟨y12, hy12, y3, hy3, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy12
  rw [map_add, map_add, (X.Lb_perp y2 hy2 a).2, coef_span3 X a hy3, add_zero, add_zero]
  exact coef_span1 X a hy1

theorem XS_eq : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  rw [XS, X.Fu_e]
  rfl

theorem lattice_of_base_eq_flag : XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) := by
  rw [XS_eq]
  ext y
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem, Xsp_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : y = y - prV X y := by rw [prV_Xs X h2, sub_zero]
    have he : ∀ a, (VS D).hT (X.eX a) y = 0 := fun a => hT_Xs_Xs X (eX_mem_Xs X a) h2
    rw [e1, sub_prV_eq]
    simp only [he, zero_smul, Finset.sum_const_zero, add_zero]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, _, coefficient_mem_fractional_ideal X a h1, rfl⟩
  · intro hy
    refine ⟨?_, ?_⟩
    · rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left hy)
    · have hle : latSpanS (fun a => aaD D a) X.eX ≤ (Xs X).restrictScalars (𝓞 D.host.E) := by
        rw [latSpanS, Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact Submodule.smul_mem _ x (eX_mem_Xs X a)
      exact hle hy

theorem base_lattice_fixed_convex : IsFixedConv (VS D).L0 (gS D) (lf D (X.Fu u)) := by
  have hlf : lf D (X.Fu u) = ⟨X.Fu u, X.zu u⟩ := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : LFlag (VS D) D.R.rS _) = _
    rw [X.flagZVector]
  rw [hlf]
  exact (X.Fu_fixed u).2.2.2

theorem fixedConv_latOf (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : (Λ : Set (VS D).V) = latOf X u h) : IsFixedConv Λ (gS D) (lf D (X.Fu u)) := by
  have hmemΛ : ∀ y, y ∈ Λ ↔ y ∈ latOf X u h := fun y => by rw [← SetLike.mem_coe, hΛ]
  have hc0 := base_lattice_fixed_convex X u
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, h1, h2, h3⟩ := hc0.1 P
    exact ⟨c, h1, h2, by rw [xlam_latOf X u h Λ hΛ]; exact h3⟩
  · have hz : (lf D (X.Fu u)).fl.z = X.zu u := X.flagZVector u
    rw [hz] at hc
    obtain ⟨hsup, horth⟩ := Submodule.mem_inf.1 hc
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsup
    have haΛ : a ∈ latOf X u h := (hmemΛ a).1 (Submodule.mem_inf.1 ha).1
    have hbX : b ∈ Xs X := by
      have := hb
      rw [Submodule.restrictScalars_mem, Xsp_eq] at this
      exact this
    have hcz : c • X.zu u ∈ latOf X u h := by
      have e : c • X.zu u = prV X a := by
        have h1 : prV X (c • X.zu u) = c • X.zu u := by rw [map_smul, prV_zu]
        rw [← h1, ← hab, map_add, prV_Xs X hbX, add_zero]
      rw [e]
      exact ((mem_latOf_split X u h a).1 haΛ).2
    have hL0 := (line_mem_iff X u h c).1 hcz
    refine hc0.2 c ?_
    rw [hz]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩

theorem isRowLat_of (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : (Λ : Set (VS D).V) = latOf X u h) (hG : Formalism.HermitianLatticesTheory.SameGenus (VS D).hT (VS D).L0 Λ) :
    IsRowLat D (X.Fu u) Λ := by
  have hmemΛ : ∀ y, y ∈ Λ ↔ y ∈ latOf X u h := fun y => by rw [← SetLike.mem_coe, hΛ]
  refine ⟨⟨latOf_isLattice X u h Λ hΛ, hG⟩, ⟨latOf_isLattice X u h Λ hΛ, latOf_unimod X u h Λ hΛ,
    ⟨?_, rfl⟩, fixedConv_latOf X u h Λ hΛ⟩, ?_⟩
  · show (X.Fu u).z ∈ Λ
    rw [X.flagZVector, hmemΛ]
    exact zu_mem_latOf X u h
  · rw [xlam_latOf X u h Λ hΛ, lattice_of_base_eq_flag]

end Row2

section Genus

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev ιO : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := NumberField.RingOfIntegers.mapRingEquiv X.ιE

theorem ιO_coe (a : 𝓞 X.B.I.E) : ((ιO X a : 𝓞 D.host.E) : D.host.E) = X.ιE (a : X.B.I.E) :=
  NumberField.RingOfIntegers.mapRingEquiv_apply X.ιE a

theorem ιO_symm_coe (a : 𝓞 D.host.E) : (((ιO X).symm a : 𝓞 X.B.I.E) : X.B.I.E) = X.ιE.symm (a : D.host.E) := by
  apply X.ιE.injective
  rw [← ιO_coe, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem star_ιE (x : X.B.I.E) : X.ιE (star x) = star (X.ιE x) := by
  rw [X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]

theorem gen_iff (p : Ideal (𝓞 D.host.E)) (t : 𝓞 X.B.I.E) :
    (t ∉ p.comap (ιO X) ∧ ∀ t' : 𝓞 X.B.I.E, algebraMap (𝓞 X.B.I.E) X.B.I.E t' =
        star (algebraMap (𝓞 X.B.I.E) X.B.I.E t) → t' ∉ p.comap (ιO X)) ↔
      (ιO X t ∉ p ∧ ∀ s' : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E s' =
        star (algebraMap (𝓞 D.host.E) D.host.E (ιO X t)) → s' ∉ p) := by
  simp only [Ideal.mem_comap]
  refine and_congr Iff.rfl ⟨fun H s' hs' => ?_, fun H t' ht' => ?_⟩
  · have h1 := H ((ιO X).symm s') (by
      show (((ιO X).symm s' : 𝓞 X.B.I.E) : X.B.I.E) = star ((t : 𝓞 X.B.I.E) : X.B.I.E)
      apply X.ιE.injective
      rw [← ιO_coe, RingEquiv.apply_symm_apply, star_ιE, ← ιO_coe]
      exact hs')
    rwa [RingEquiv.apply_symm_apply] at h1
  · refine H (ιO X t') ?_
    show ((ιO X t' : 𝓞 D.host.E) : D.host.E) = star ((ιO X t : 𝓞 D.host.E) : D.host.E)
    rw [ιO_coe, ιO_coe, ← star_ιE]
    exact congrArg X.ιE ht'

theorem hcompl_iff (p : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := D.host.E) p ↔ (ιO X).symm s ∈ Formalism.HermitianLatticesTheory.hcompl (K := X.B.I.E) (p.comap (ιO X)) := by
  have himg : ((ιO X).symm : 𝓞 D.host.E →* 𝓞 X.B.I.E) ''
      {s | s ∉ p ∧ ∀ t : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E t =
        star (algebraMap (𝓞 D.host.E) D.host.E s) → t ∉ p} =
      {t | t ∉ p.comap (ιO X) ∧ ∀ t' : 𝓞 X.B.I.E, algebraMap (𝓞 X.B.I.E) X.B.I.E t' =
        star (algebraMap (𝓞 X.B.I.E) X.B.I.E t) → t' ∉ p.comap (ιO X)} := by
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    rw [gen_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have e : ιO X (((ιO X).symm : 𝓞 D.host.E →* 𝓞 X.B.I.E) s) = s := (ιO X).apply_symm_apply s
      simp only [e]
      exact hs
    · intro ht
      exact ⟨ιO X t, ht, by simp⟩
  unfold Formalism.HermitianLatticesTheory.hcompl
  rw [← himg, ← MonoidHom.map_mclosure]
  exact (Submonoid.mem_map_iff_mem (f := ((ιO X).symm : 𝓞 D.host.E →* 𝓞 X.B.I.E)) (ιO X).symm.injective).symm

theorem crd_osmul (s : 𝓞 D.host.E) (y : (VS D).V) : X.crd (s • y) = (ιO X).symm s • X.crd y := by
  rw [← IsScalarTower.algebraMap_smul D.host.E s y, crd_smul]
  rw [show (ιO X).symm s • X.crd y = (((ιO X).symm s : 𝓞 X.B.I.E) : X.B.I.E) • X.crd y from
    (IsScalarTower.algebraMap_smul X.B.I.E _ _).symm, ιO_symm_coe]

theorem loc_iff (p : Ideal (𝓞 D.host.E)) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (N : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E)) (hMN : ∀ y, y ∈ M ↔ X.crd y ∈ N) (y : (VS D).V) :
    y ∈ Formalism.HermitianLatticesTheory.loc (K := D.host.E) p M ↔ X.crd y ∈ Formalism.HermitianLatticesTheory.loc (K := X.B.I.E) (p.comap (ιO X)) N := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨(ιO X).symm s, (hcompl_iff X p s).1 hs, ?_⟩
    rw [← crd_osmul, ← hMN]
    exact hsy
  · rintro ⟨t, ht, hty⟩
    refine ⟨ιO X t, (hcompl_iff X p _).2 (by rw [RingEquiv.symm_apply_apply]; exact ht), ?_⟩
    rw [hMN, crd_osmul, RingEquiv.symm_apply_apply]
    exact hty

theorem sameGenus_of (hLG : LatDictZ.LamGenus) (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : (Λ : Set (VS D).V) = latOf X u h) : Formalism.HermitianLatticesTheory.SameGenus (VS D).hT (VS D).L0 Λ := by
  intro p hp
  have hp' : (p.comap (ιO X)).IsMaximal := Ideal.comap_isMaximal_of_surjective (ιO X) (ιO X).surjective
  obtain ⟨γ, hγ, hloc⟩ := hLG X.B.I ((h : X.B.I.Gf) * X.xu u) (p.comap (ιO X)) hp'
  have hL0 : ∀ y, y ∈ (VS D).L0 ↔ X.crd y ∈ X.B.I.L := mem_hermitianStandardLattice_iff_pairing_integral X
  have hΛ' : ∀ y, y ∈ Λ ↔ X.crd y ∈ PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u) :=
    fun y => by rw [← SetLike.mem_coe, hΛ]; rfl
  refine ⟨matE X γ, matE_isom X γ hγ, ?_⟩
  ext y
  rw [loc_iff X p Λ _ hΛ' y, show X.crd y ∈ Formalism.HermitianLatticesTheory.loc (K := X.B.I.E) (p.comap (ιO X))
      (PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u)) ↔ _ from hloc (X.crd y)]
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨X.crd w, (loc_iff X p _ _ hL0 w).1 hw, (matE_crd X γ w).symm⟩
  · rintro ⟨w', hw', hwy⟩
    refine ⟨toV X w', (loc_iff X p _ _ hL0 _).2 (by rw [crd_toV]; exact hw'), ?_⟩
    have e : X.crd (matE X γ (toV X w')) = X.crd y := by rw [matE_crd, crd_toV, hwy]
    have e2 := congrArg (toV X) e
    rwa [toV_crd, toV_crd] at e2

end Genus

section Hyp

variable {D : D7} (e g : Fin D.R.rS → (VS D).V)

def prH (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (g a) v • e a - ∑ a, (VS D).hT (e a) v • g a

variable {e g}

section
variable (hee : ∀ a b, (VS D).hT (e a) (e b) = 0) (hgg : ∀ a b, (VS D).hT (g a) (g b) = 0)
  (heg : ∀ a b, (VS D).hT (e a) (g b) = if a = b then 1 else 0)
include hee hgg heg

theorem hT_g_e (a b : Fin D.R.rS) : (VS D).hT (g a) (e b) = if b = a then 1 else 0 := by
  rw [hT_herm, heg]; split_ifs <;> simp

theorem hT_g_prH (a : Fin D.R.rS) (v : (VS D).V) : (VS D).hT (g a) (prH e g v) = 0 := by
  simp [prH, map_sub, map_sum, hT_g_e hee hgg heg, hgg]

theorem hT_e_prH (a : Fin D.R.rS) (v : (VS D).V) : (VS D).hT (e a) (prH e g v) = 0 := by
  simp [prH, map_sub, map_sum, hee, heg]

theorem hT_hyp (α β α' β' : Fin D.R.rS → D.host.E) (p p' : (VS D).V)
    (hp : ∀ a, (VS D).hT (e a) p = 0 ∧ (VS D).hT (g a) p = 0)
    (hp' : ∀ a, (VS D).hT (e a) p' = 0 ∧ (VS D).hT (g a) p' = 0) :
    (VS D).hT (∑ a, α a • e a + ∑ a, β a • g a + p) (∑ a, α' a • e a + ∑ a, β' a • g a + p') =
      ∑ a, (star (α a) * β' a + star (β a) * α' a) + (VS D).hT p p' := by
  have hpe : ∀ a, (VS D).hT p (e a) = 0 := fun a => by rw [hT_herm, (hp a).1, star_zero]
  have hpg : ∀ a, (VS D).hT p (g a) = 0 := fun a => by rw [hT_herm, (hp a).2, star_zero]
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, hee, heg, hgg, hT_g_e hee hgg heg, (hp' _).1, (hp' _).2, hpe, hpg,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply]
  rw [Finset.sum_add_distrib]
  simp only [RingHom.id_apply]
  rw [add_comm (∑ x, α' x * star (β x))]
  congr 1
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem decomp_H (v : (VS D).V) :
    v = ∑ a, (VS D).hT (g a) v • e a + ∑ a, (VS D).hT (e a) v • g a + prH e g v := by
  simp only [prH]; abel

end

end Hyp

section Delta

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def prHL (e g : Fin D.R.rS → (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (g a)).smulRight (e a) - ∑ a, ((VS D).hT (e a)).smulRight (g a)

theorem prHL_apply (e g : Fin D.R.rS → (VS D).V) (v : (VS D).V) : prHL e g v = prH e g v := by
  simp [prHL, prH, LinearMap.sub_apply, LinearMap.sum_apply]

def dlt (f' : Fin D.R.rS → (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) + ∑ a, ((VS D).hT (X.eX a)).smulRight (f' a) +
    prHL X.eX f' ∘ₗ prV X

theorem dlt_apply (f' : Fin D.R.rS → (VS D).V) (v : (VS D).V) :
    dlt X f' v = ∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • f' a + prH X.eX f' (prV X v) := by
  simp [dlt, LinearMap.add_apply, LinearMap.sum_apply, prHL_apply]

variable {f' : Fin D.R.rS → (VS D).V} (hff : ∀ a b, (VS D).hT (f' a) (f' b) = 0)
  (hef : ∀ a b, (VS D).hT (X.eX a) (f' b) = if a = b then 1 else 0)

theorem prH_zero : prH (D := D) X.eX f' 0 = 0 := by simp [prH]

theorem dlt_e (b : Fin D.R.rS) : dlt X f' (X.eX b) = X.eX b := by
  rw [dlt_apply, prV_e, prH_zero]
  simp [hT_f_e, X.ee]

include hef in
theorem dlt_f (b : Fin D.R.rS) : dlt X f' (X.fY b) = f' b := by
  rw [dlt_apply, prV_f, prH_zero]
  simp [X.ff, X.ef]

theorem delta_fix_anisotropic (hz : ∀ a, (VS D).hT (f' a) (X.zu u) = 0) : dlt X f' (X.zu u) = X.zu u := by
  rw [dlt_apply, prV_zu]
  simp [prH, (X.zu_orth u _).1, (X.zu_orth u _).2, hz]

include hff hef in
theorem dlt_isom (v v' : (VS D).V) : (VS D).hT (dlt X f' v) (dlt X f' v') = (VS D).hT v v' := by
  have hee := X.ee
  have hpv : ∀ w : (VS D).V, ∀ a, (VS D).hT (X.eX a) (prH X.eX f' (prV X w)) = 0 ∧
      (VS D).hT (f' a) (prH X.eX f' (prV X w)) = 0 :=
    fun w a => ⟨hT_e_prH hee hff hef a _, hT_g_prH hee hff hef a _⟩
  have hpw : ∀ w : (VS D).V, ∀ a, (VS D).hT (X.eX a) (prV X w) = 0 ∧ (VS D).hT (X.fY a) (prV X w) = 0 :=
    fun w a => ⟨hT_e_prV X a w, hT_f_prV X a w⟩

  have hxi : ∀ w : (VS D).V, prH X.eX f' (prV X w) =
      prV X w - ∑ a, (VS D).hT (f' a) (prV X w) • X.eX a := by
    intro w
    simp [prH, hT_e_prV]
  have hXi : ∀ w : (VS D).V, ∑ a, (VS D).hT (f' a) (prV X w) • X.eX a ∈ Xs X :=
    fun w => Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (eX_mem_Xs X a)
  have hW : (VS D).hT (prH X.eX f' (prV X v)) (prH X.eX f' (prV X v')) = (VS D).hT (prV X v) (prV X v') := by
    rw [hxi, hxi]
    have h1 := hT_Xs_Xs X (hXi v) (hXi v')
    have h2 : (VS D).hT (∑ a, (VS D).hT (f' a) (prV X v) • X.eX a) (prV X v') = 0 := hT_Xs_prV X (hXi v) v'
    have h3 : (VS D).hT (prV X v) (∑ a, (VS D).hT (f' a) (prV X v') • X.eX a) = 0 := by
      rw [hT_herm, hT_Xs_prV X (hXi v') v, star_zero]
    simp only [map_sub, LinearMap.sub_apply, h1, h2, h3, sub_zero]
  have hd1 := hT_hyp hee hff hef (fun a => (VS D).hT (X.fY a) v) (fun a => (VS D).hT (X.eX a) v)
    (fun a => (VS D).hT (X.fY a) v') (fun a => (VS D).hT (X.eX a) v') _ _ (hpv v) (hpv v')
  have hd2 := hT_hyp hee X.ff X.ef (fun a => (VS D).hT (X.fY a) v) (fun a => (VS D).hT (X.eX a) v)
    (fun a => (VS D).hT (X.fY a) v') (fun a => (VS D).hT (X.eX a) v') _ _ (hpw v) (hpw v')
  have ev : ∀ w : (VS D).V, w = ∑ a, (VS D).hT (X.fY a) w • X.eX a + ∑ a, (VS D).hT (X.eX a) w • X.fY a + prV X w :=
    fun w => by rw [← sub_prV_eq]; abel
  beta_reduce at hd1 hd2
  rw [dlt_apply, dlt_apply, hd1, hW]
  conv_rhs => rw [ev v, ev v']
  rw [hd2]

end Delta

section Surj

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

open Formalism.MainNotions.S.Lat

theorem gmap_symm_mem (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V) (y : (VS D).V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap g.symm L ↔ g y ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨g y, h, by simp⟩

theorem gmap_gmap_symm (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.gmap g.symm L) = L := by
  ext y
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩; simpa using hw
  · intro h; exact ⟨g.symm y, ⟨y, h, rfl⟩, by simp⟩

theorem latSpan_map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) {r : ℕ} (v w : Fin r → (VS D).V)
    (h : ∀ b, φ (v b) = w b) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    {y : (VS D).V} (hy : y ∈ latSpanS aa v) : φ y ∈ latSpanS aa w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, x, hx, rfl⟩ := hz
    rw [map_smul, h]
    exact Submodule.subset_span ⟨b, x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o z _ hz =>
    rw [← IsScalarTower.algebraMap_smul D.host.E o z, map_smul, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ o hz

theorem latSpan_le_span {r : ℕ} (v : Fin r → (VS D).V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
  rw [latSpanS, Submodule.span_le]
  rintro _ ⟨b, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨b, rfl⟩)

theorem prV_span_e {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.eX)) : prV X y = 0 :=
  prV_Xs X hy

theorem prV_span_f {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.fY)) : prV X y = 0 := by
  have : Submodule.span D.host.E (Set.range X.fY) ≤ LinearMap.ker (prV X) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact prV_f X b
  exact this hy

theorem prV_of_perp {w : (VS D).V} (he : ∀ a, (VS D).hT (X.eX a) w = 0) (hf : ∀ a, (VS D).hT (X.fY a) w = 0) :
    prV X w = w := by
  simp [prV_apply, he, hf]

theorem smulMem {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (Λ : Submodule (𝓞 K) W) [hΛ : Submodule.IsLattice K Λ] (v : W) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ s • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_ter_form.goal1 .. | (apply Bl.general_b_fact_third_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_ter_form.goal1 <;> assumption)

theorem uniform_mul {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {A B : Submodule (𝓞 K) W} (hA : A.FG) [hB : Submodule.IsLattice K B] :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ a ∈ A, c • a ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  choose cs hcs0 hcs using fun s : W => smulMem B s
  refine ⟨∏ s ∈ S, cs s, Finset.prod_ne_zero_iff.2 fun s _ => hcs0 s, fun a ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem s hs =>
    rw [← Finset.mul_prod_erase S cs hs, mul_comm, mul_smul]
    exact B.smul_mem _ (hcs s)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact B.smul_mem _ hx

theorem fg_of_smul_le {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {P L : Submodule (𝓞 K) W} (hL : L.FG) (c : 𝓞 K) (hc : c ≠ 0)
    (h : ∀ y ∈ P, c • y ∈ L) : P.FG := by
  let f : W →ₗ[𝓞 K] W := c • LinearMap.id
  have hf : Function.Injective f := by
    intro a b hab
    have e : ((c : K)) • (a - b) = 0 := by
      rw [IsScalarTower.algebraMap_smul (R := 𝓞 K) K c, smul_sub]
      exact sub_eq_zero.2 hab
    rcases smul_eq_zero.1 e with h0 | h0
    · exact absurd (by exact_mod_cast h0) hc
    · exact sub_eq_zero.1 h0
  have hle : P.map f ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : ((P.map f).comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 : ((P.map f).comap L.subtype).map L.subtype = P.map f := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.2 hle
  exact Submodule.fg_of_fg_map_injective f hf (h2 ▸ h1.map _)

end Surj

section Surj2

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

open Formalism.MainNotions.S.Lat

theorem dlt_inj {f' : Fin D.R.rS → (VS D).V} (hff : ∀ a b, (VS D).hT (f' a) (f' b) = 0)
    (hef : ∀ a b, (VS D).hT (X.eX a) (f' b) = if a = b then 1 else 0) : Function.Injective (dlt X f') := by
  intro v w hvw
  have h0 : ∀ y, (VS D).hT (v - w) y = 0 := by
    intro y
    have := dlt_isom X hff hef (v - w) y
    rw [map_sub, hvw, sub_self, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  exact sub_eq_zero.1 ((VS D).nondeg.1 _ h0)

def dltE {f' : Fin D.R.rS → (VS D).V} (hff : ∀ a b, (VS D).hT (f' a) (f' b) = 0)
    (hef : ∀ a b, (VS D).hT (X.eX a) (f' b) = if a = b then 1 else 0) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofInjectiveEndo (dlt X f') (dlt_inj X hff hef)

theorem dltE_apply {f' : Fin D.R.rS → (VS D).V} (hff : ∀ a b, (VS D).hT (f' a) (f' b) = 0)
    (hef : ∀ a b, (VS D).hT (X.eX a) (f' b) = if a = b then 1 else 0) (v : (VS D).V) :
    dltE X hff hef v = dlt X f' v := rfl

theorem dltE_stab {f' : Fin D.R.rS → (VS D).V} (hff : ∀ a b, (VS D).hT (f' a) (f' b) = 0)
    (hef : ∀ a b, (VS D).hT (X.eX a) (f' b) = if a = b then 1 else 0)
    (hz : ∀ a, (VS D).hT (f' a) (X.zu u) = 0) : dltE X hff hef ∈ stabF D (X.Fu u) := by
  refine ⟨fun x y => dlt_isom X hff hef x y, fun j => ?_, ?_⟩
  · rw [FlagG.Xa, X.Fu_e, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun b _ => dlt_e X b
  · show dlt X f' (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector]
    exact delta_fix_anisotropic X u hz

theorem crd_add (x y : (VS D).V) : X.crd (x + y) = X.crd x + X.crd y := by
  funext i; simp [HidaSetting.crd, crdOf]

def crdHom : (VS D).V →+ (Fin X.B.I.n → X.B.I.E) := AddMonoidHom.mk' X.crd (crd_add X)

theorem toV_osmul (t : 𝓞 X.B.I.E) (v : Fin X.B.I.n → X.B.I.E) : toV X (t • v) = ιO X t • toV X v := by
  rw [← IsScalarTower.algebraMap_smul X.B.I.E t v, toV_smul, ← IsScalarTower.algebraMap_smul D.host.E (ιO X t)]
  rfl

theorem hform_crd_mem (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) ∈ (algebraMap (𝓞 X.B.I.E) X.B.I.E).range ↔
      (VS D).hT v w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  rw [hform_crd', int_iff X]

theorem hE_crd_zero {v w : (VS D).V} (h : (VS D).hT v w = 0) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) = 0 := by
  rw [hform_crd', h, map_zero]

theorem lattice_surjective_of_orbit (hZ : LatDictZ.ZOrbit) : LatSurj X u := by
  intro Λ hrow
  obtain ⟨f', L, hff, hef0, hL0, hzL0, hΛs0⟩ := Formalism.L2.SG.Closed.IsSplitRow_holds D u (X.Fu u) Λ hrow
  rw [X.Fu_e] at hef0 hL0 hΛs0
  rw [X.flagZVector] at hzL0
  have hef := hef0
  have hL := hL0
  have hzL := hzL0
  have hΛs : Λ = latSpanS (fun a => aaD D a) X.eX ⊔ L ⊔ latSpanS (fun a => (aaD D a)⁻¹) f' := hΛs0
  have hz' : ∀ a, (VS D).hT (f' a) (X.zu u) = 0 := fun a => (hL _ hzL a).2
  set δ := dltE X hff hef with hδdef
  have hδ : δ ∈ stabF D (X.Fu u) := dltE_stab X u hff hef hz'
  have hδap : ∀ v, δ v = dlt X f' v := fun v => rfl
  set Λ2 := Formalism.HermitianLatticesTheory.gmap δ.symm Λ with hΛ2
  have hmem2 : ∀ y, y ∈ Λ2 ↔ δ y ∈ Λ := gmap_symm_mem δ Λ
  have hA : ∀ a ∈ latSpanS (fun a => aaD D a) X.eX, a ∈ Λ := fun a ha => by
    rw [hΛs]; exact Submodule.mem_sup_left (Submodule.mem_sup_left ha)
  have hLΛ : ∀ l ∈ L, l ∈ Λ := fun l hl => by
    rw [hΛs]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl)
  have hC : ∀ c ∈ latSpanS (fun a => (aaD D a)⁻¹) f', c ∈ Λ := fun c hc => by
    rw [hΛs]; exact Submodule.mem_sup_right hc
  have hA0 : ∀ a ∈ latSpanS (fun a => aaD D a) X.eX, a ∈ (VS D).L0 := fun a ha => by
    rw [X.Lam_split]; exact Submodule.mem_sup_left (Submodule.mem_sup_left ha)
  have hC0 : ∀ c ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY, c ∈ (VS D).L0 := fun c hc => by
    rw [X.Lam_split]; exact Submodule.mem_sup_right hc
  have hδe : ∀ b, δ.symm (X.eX b) = X.eX b := fun b => by
    rw [LinearEquiv.symm_apply_eq, hδap]; exact (dlt_e X b).symm
  have hδf : ∀ b, δ.symm (f' b) = X.fY b := fun b => by
    rw [LinearEquiv.symm_apply_eq, hδap]; exact (dlt_f X hef b).symm
  have hdec : ∀ y ∈ Λ2, ∃ a ∈ latSpanS (fun a => aaD D a) X.eX, ∃ l ∈ L,
      ∃ c ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY, y = a + δ.symm l + c := by
    intro y hy
    rw [hmem2, hΛs] at hy
    obtain ⟨y12, hy12, c, hc, he⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, ha, l, hl, rfl⟩ := Submodule.mem_sup.1 hy12
    refine ⟨δ.symm a, latSpan_map (δ.symm : (VS D).V →ₗ[D.host.E] (VS D).V) X.eX X.eX hδe _ ha, l, hl,
      δ.symm c, latSpan_map (δ.symm : (VS D).V →ₗ[D.host.E] (VS D).V) f' X.fY hδf _ hc, ?_⟩
    calc y = δ.symm (δ y) := (δ.symm_apply_apply y).symm
      _ = δ.symm (a + l + c) := by rw [he]
      _ = δ.symm a + δ.symm l + δ.symm c := by rw [map_add, map_add]
  have hprA : ∀ a ∈ latSpanS (fun a => aaD D a) X.eX, prV X a = 0 :=
    fun a ha => prV_span_e X (latSpan_le_span X.eX _ ha)
  have hprC : ∀ c ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY, prV X c = 0 :=
    fun c hc => prV_span_f X (latSpan_le_span X.fY _ hc)
  have hperpL : ∀ l ∈ L, prV X (δ.symm l) = δ.symm l := by
    intro l hl
    apply prV_of_perp X
    · intro b
      have h1 := dlt_isom X hff hef (X.eX b) (δ.symm l)
      rw [dlt_e, show dlt X f' (δ.symm l) = l from (hδap _).symm.trans (δ.apply_symm_apply l)] at h1
      rw [← h1]; exact (hL l hl b).1
    · intro b
      have h1 := dlt_isom X hff hef (X.fY b) (δ.symm l)
      rw [dlt_f X hef, show dlt X f' (δ.symm l) = l from (hδap _).symm.trans (δ.apply_symm_apply l)] at h1
      rw [← h1]; exact (hL l hl b).2
  have hsplit2 : ∀ y ∈ Λ2, prV X y ∈ Λ2 ∧ y - prV X y ∈ (VS D).L0 := by
    intro y hy
    obtain ⟨a, ha, l, hl, c, hc, rfl⟩ := hdec y hy
    have hp : prV X (a + δ.symm l + c) = δ.symm l := by
      rw [map_add, map_add, hprA a ha, hprC c hc, hperpL l hl, zero_add, add_zero]
    rw [hp]
    refine ⟨(hmem2 _).2 (by rw [δ.apply_symm_apply]; exact hLΛ l hl), ?_⟩
    rw [show a + δ.symm l + c - δ.symm l = a + c by abel]
    exact add_mem (hA0 a ha) (hC0 c hc)
  have hagree : ∀ y, prV X y = 0 → (y ∈ Λ2 ↔ y ∈ (VS D).L0) := by
    intro y hy0
    constructor
    · intro hy
      have := (hsplit2 y hy).2
      rwa [hy0, sub_zero] at this
    · intro hy
      rw [X.Lam_split] at hy
      obtain ⟨y12, hy12, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy12
      have hb0 : b = 0 := by
        have h1 := hy0
        rw [map_add, map_add, hprA a ha, prV_Lb X b hb, hprC c hc, zero_add, add_zero] at h1
        exact h1
      subst hb0
      rw [hmem2, add_zero, map_add]
      exact add_mem (hA _ (latSpan_map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) X.eX X.eX
          (fun b => by rw [LinearEquiv.coe_coe, hδap, dlt_e]) _ ha))
        (hC _ (latSpan_map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) X.fY f'
          (fun b => by rw [LinearEquiv.coe_coe, hδap, dlt_f X hef]) _ hc))
  have hδz : δ (X.zu u) = X.zu u := by rw [hδap]; exact delta_fix_anisotropic X u hz'
  have hz2 : X.zu u ∈ Λ2 := (hmem2 _).2 (by rw [hδz]; exact hLΛ _ hzL)
  have horth : ∀ c : D.host.E, c • X.zu u ∈ toO (VS D) (orth (VS D) (Xsp (lf D (X.Fu u)))) := by
    intro c
    simp only [toO, Submodule.restrictScalars_mem, orth, Submodule.mem_iInf, LinearMap.mem_ker, Xsp_eq]
    intro x hx
    rw [map_smul, ← prV_zu X u, hT_Xs_prV X hx, smul_zero]
  have hprimΛ : ∀ c : D.host.E, c • X.zu u ∈ Λ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    have hconv := hrow.2.1.2.2.2
    refine hconv.2 c ?_
    rw [show (lf D (X.Fu u)).fl.z = X.zu u from X.flagZVector u]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth c⟩), horth c⟩
  have hprimL0 : ∀ c : D.host.E, c • X.zu u ∈ (VS D).L0 → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    refine (base_lattice_fixed_convex X u).2 c ?_
    rw [show (lf D (X.Fu u)).fl.z = X.zu u from X.flagZVector u]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth c⟩), horth c⟩
  have hΛlat := hrow.2.1.1
  have hlat : Submodule.IsLattice D.host.E Λ2 := by
    refine ⟨hΛlat.fg.map _, ?_⟩
    rw [hΛ2, Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [show ((δ.symm : (VS D).V →ₗ[D.host.E] (VS D).V) : (VS D).V → (VS D).V) '' (Λ : Set (VS D).V) =
      ((δ.symm : (VS D).V →ₗ[D.host.E] (VS D).V) : (VS D).V → (VS D).V) '' (Λ : Set (VS D).V) from rfl,
      ← Submodule.map_span, hΛlat.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hUΛ : ∀ y, y ∈ Λ ↔ ∀ w ∈ Λ, (VS D).hT w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    conv_lhs => rw [← hrow.2.1.2.1]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
    rfl
  have hU2 : ∀ y, y ∈ Λ2 ↔ ∀ w ∈ Λ2, (VS D).hT w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [hmem2, hUΛ]
    constructor
    · intro H w hw
      have := H (δ w) ((hmem2 w).1 hw)
      rwa [show (VS D).hT (δ w) (δ y) = (VS D).hT w y from hδ.1 w y] at this
    · intro H w' hw'
      have := H (δ.symm w') ((hmem2 _).2 (by rw [δ.apply_symm_apply]; exact hw'))
      rwa [← hδ.1 (δ.symm w') y, δ.apply_symm_apply] at this
  haveI := (VS D).standardTuple_isLattice
  obtain ⟨c1, hc1, hc1m⟩ := uniform_mul (B := (VS D).L0) hlat.fg
  haveI := hlat
  obtain ⟨c2, hc2, hc2m⟩ := uniform_mul (B := Λ2) (VS D).standardTuple_isLattice.fg
  let M : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E) :=
    { carrier := {v | toV X v ∈ Λ2}
      add_mem' := fun {a b} ha hb => by
        show toV X (a + b) ∈ Λ2
        rw [toV_add]; exact add_mem ha hb
      zero_mem' := by
        show toV X 0 ∈ Λ2
        have : toV X 0 = 0 := by simp [toV]
        rw [this]; exact zero_mem _
      smul_mem' := fun t v hv => by
        show toV X (t • v) ∈ Λ2
        rw [toV_osmul]; exact Λ2.smul_mem _ hv }
  have hMv : ∀ v, v ∈ M ↔ toV X v ∈ Λ2 := fun v => Iff.rfl
  have hMmem : ∀ y, y ∈ Λ2 ↔ X.crd y ∈ M := fun y => by rw [hMv, toV_crd]
  have hLv : ∀ v, v ∈ X.B.I.L ↔ toV X v ∈ (VS D).L0 := fun v => by rw [mem_hermitianStandardLattice_iff_pairing_integral, crd_toV]
  have hc1' : (ιO X).symm c1 ≠ 0 := fun h => hc1 ((ιO X).symm.injective (h.trans (map_zero _).symm))
  have hc2' : (ιO X).symm c2 ≠ 0 := fun h => hc2 ((ιO X).symm.injective (h.trans (map_zero _).symm))
  have hMfg : M.FG := by
    refine fg_of_smul_le X.B.I.L_fg ((ιO X).symm c1) hc1' fun v hv => ?_
    rw [hLv, toV_osmul, RingEquiv.apply_symm_apply]
    exact hc1m _ hv
  have hMspan : Submodule.span X.B.I.E (M : Set (Fin X.B.I.n → X.B.I.E)) = ⊤ := by
    rw [eq_top_iff, ← X.B.I.L_span, Submodule.span_le]
    intro w hw
    have hm : (ιO X).symm c2 • w ∈ M := by
      rw [hMv, toV_osmul, RingEquiv.apply_symm_apply]
      exact hc2m _ ((hLv w).1 hw)
    have hne : ((((ιO X).symm c2 : 𝓞 X.B.I.E)) : X.B.I.E) ≠ 0 := by exact_mod_cast hc2'
    have e : w = (((((ιO X).symm c2 : 𝓞 X.B.I.E)) : X.B.I.E))⁻¹ • ((ιO X).symm c2 • w) := by
      rw [← IsScalarTower.algebraMap_smul X.B.I.E ((ιO X).symm c2) w, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  have hMsd : PIW.AdelClassFin.SelfDual X.B.I.J M := by
    intro v
    rw [hMv, hU2]
    constructor
    · intro H y hy
      rw [← crd_toV X y, ← crd_toV X v, hform_crd_mem]
      exact H _ hy
    · intro H w hw
      have := H (X.crd w) ((hMmem w).1 hw)
      rwa [← crd_toV X v, hform_crd_mem] at this
  let s : Fin (D.R.rS + D.R.rS) → Fin X.B.I.n → X.B.I.E := Fin.append X.eR X.fR
  have hs_e : ∀ a, s (Fin.castAdd D.R.rS a) = X.eR a := fun a => Fin.append_left _ _ a
  have hs_f : ∀ a, s (Fin.natAdd D.R.rS a) = X.fR a := fun a => Fin.append_right _ _ a
  have hsV : ∀ i, prV X (toV X (s i)) = 0 := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hs_e, HidaSetting.eR, toV_crd, prV_e]
    · rw [hs_f, HidaSetting.fR, toV_crd, prV_f]
  have hspanV : ∀ w ∈ Submodule.span X.B.I.E (Set.range s), prV X (toV X w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hsV i
    | zero => have : toV X 0 = 0 := by simp [toV]
              rw [this, map_zero]
    | add x y _ _ hx hy => rw [toV_add, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [toV_smul, map_smul, hx, smul_zero]
  have hsz : ∀ a, LatDictZ.hE X.B.I (s a) (X.zR u) = 0 := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hs_e]; exact hE_crd_zero X (X.zu_orth u a).1
    · rw [hs_f]; exact hE_crd_zero X (X.zu_orth u a).2
  have hsum_mem : ∀ v : (VS D).V, X.crd (v - prV X v) ∈ Submodule.span X.B.I.E (Set.range s) := by
    intro v
    rw [sub_prV_eq]
    have e1 : X.crd (∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a) =
        ∑ a, X.ιE.symm ((VS D).hT (X.fY a) v) • X.eR a + ∑ a, X.ιE.symm ((VS D).hT (X.eX a) v) • X.fR a := by
      have h1 := map_sum (crdHom X) (fun a => (VS D).hT (X.fY a) v • X.eX a) Finset.univ
      have h2 := map_sum (crdHom X) (fun a => (VS D).hT (X.eX a) v • X.fY a) Finset.univ
      simp only [crdHom, AddMonoidHom.mk'_apply] at h1 h2
      rw [crd_add, h1, h2]
      simp only [crd_smul, HidaSetting.eR, HidaSetting.fR]
    rw [e1]
    refine add_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs_e a⟩))
      (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs_f a⟩))
  have hperp_s : ∀ (v : (VS D).V) (i : Fin (D.R.rS + D.R.rS)), LatDictZ.hE X.B.I (s i) (X.crd (prV X v)) = 0 := by
    intro v i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hs_e]; exact hE_crd_zero X (hT_e_prV X a v)
    · rw [hs_f]; exact hE_crd_zero X (hT_f_prV X a v)
  have hdiff : ∀ v : (VS D).V, X.crd v - X.crd (v - prV X v) = X.crd (prV X v) := by
    intro v
    rw [sub_eq_iff_eq_add, ← crd_add]
    congr 1; abel
  have hsplitL : LatDictZ.SplitU X.B.I s X.B.I.L := by
    intro w hw
    have hv : toV X w ∈ (VS D).L0 := (hLv w).1 hw
    have hw' : w - X.crd (toV X w - prV X (toV X w)) = X.crd (prV X (toV X w)) := by
      rw [← hdiff, crd_toV]
    refine ⟨X.crd (toV X w - prV X (toV X w)), (mem_hermitianStandardLattice_iff_pairing_integral X _).1 (sub_mem hv (projection_preserves_lattice X _ hv)),
      hsum_mem _, fun i => ?_⟩
    rw [hw']
    exact hperp_s _ i
  have hsplitM : LatDictZ.SplitU X.B.I s M := by
    intro w hw
    have hv : toV X w ∈ Λ2 := hw
    have hw' : w - X.crd (toV X w - prV X (toV X w)) = X.crd (prV X (toV X w)) := by
      rw [← hdiff, crd_toV]
    refine ⟨X.crd (toV X w - prV X (toV X w)), (hMmem _).1 (sub_mem hv (hsplit2 _ hv).1),
      hsum_mem _, fun i => ?_⟩
    rw [hw']
    exact hperp_s _ i
  have hagreeC : ∀ w ∈ Submodule.span X.B.I.E (Set.range s), w ∈ X.B.I.L ↔ w ∈ M :=
    fun w hw => by rw [hLv, hMv]; exact (hagree _ (hspanV w hw)).symm
  have hzL' : X.zR u ∈ X.B.I.L := (mem_hermitianStandardLattice_iff_pairing_integral X _).1 (Lb_le X (X.zu_Lb u))
  have hzM : X.zR u ∈ M := (hMmem _).1 hz2
  have hprimL : LatDictZ.Prim X.B.I X.B.I.L (X.zR u) := by
    intro c hc
    have h1 : X.ιE c • X.zu u ∈ (VS D).L0 := by
      rw [mem_hermitianStandardLattice_iff_pairing_integral, crd_smul, RingEquiv.symm_apply_apply]; exact hc
    obtain ⟨o, ho⟩ := hprimL0 _ h1
    have h2 : X.ιE c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := ⟨o, ho⟩
    rw [int_iff, RingEquiv.symm_apply_apply] at h2
    exact h2
  have hprimM : LatDictZ.Prim X.B.I M (X.zR u) := by
    intro c hc
    have h1 : X.ιE c • X.zu u ∈ Λ2 := by
      rw [hMmem, crd_smul, RingEquiv.symm_apply_apply]; exact hc
    rw [hmem2, map_smul, hδz] at h1
    obtain ⟨o, ho⟩ := hprimΛ _ h1
    have h2 : X.ιE c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := ⟨o, ho⟩
    rw [int_iff, RingEquiv.symm_apply_apply] at h2
    exact h2
  obtain ⟨x, hxs, hxz, hxM⟩ := hZ X.B.I s (X.zR u) M hMfg hMspan hMsd hsz hagreeC hsplitL hsplitM hzL' hzM
    hprimL hprimM
  have hxfix : x ∈ Hfin X u := by
    show ∀ y ∈ fixSet X u, X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y
    rintro y ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hy)
    · have := hxs (Fin.castAdd _ a); rw [hs_e] at this; exact this
    · have := hxs (Fin.natAdd _ a); rw [hs_f] at this; exact this
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact hxz
  refine ⟨⟨x, hxfix⟩, Λ2, ?_, δ, hδ, gmap_gmap_symm δ Λ⟩
  ext y
  show y ∈ Λ2 ↔ X.B.I.fmat ((x * X.xu u)⁻¹) *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf
  rw [_root_.mul_inv_rev, fmat_mul, ← mulVec_mulVec, kset_iff X (X.xu_K u), hMmem, ← hxM]
  rfl

end Surj2

end LatDict

open LatDict

theorem latInj {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : LatInj X u := by
  intro h h' Λ Λ' hΛ hΛ' hE
  obtain ⟨γ, hγ, hγΛ⟩ := hE
  have hγ' := stab_symm X u hγ
  have hmap : ∀ y ∈ latOf X u h, γ y ∈ latOf X u h' := by
    intro y hy
    have hy' : y ∈ Λ := by rw [← SetLike.mem_coe, hΛ]; exact hy
    have h2 : γ y ∈ Λ' := by rw [← hγΛ]; exact ⟨y, hy', rfl⟩
    rw [← SetLike.mem_coe, hΛ'] at h2
    exact h2
  have hmap' : ∀ y ∈ latOf X u h', γ.symm y ∈ latOf X u h := by
    intro y hy
    have hy' : y ∈ Λ' := by rw [← SetLike.mem_coe, hΛ']; exact hy
    rw [← hγΛ] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    have e : γ.symm y = x := by rw [← hxy]; simp
    rw [e, ← hΛ]
    exact hx
  have h1 : gW X γ ∘ₗ gW X γ.symm = LinearMap.id :=
    LinearMap.ext fun y => gW_gW X u hγ hγ' (fun w => γ.apply_symm_apply w) y
  have h2 : gW X γ.symm ∘ₗ gW X γ = LinearMap.id :=
    LinearMap.ext fun y => gW_gW X u hγ' hγ (fun w => γ.symm_apply_apply w) y
  have hM := ratGL_UJ X (gW X γ) (gW X γ.symm) h1 h2 (gW_isom X u hγ)
  have hfix : ∀ y ∈ fixSet X u, ((ratGL X (gW X γ) (gW X γ.symm) h1 h2 : GL (Fin X.B.I.n) X.B.I.E) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
    rintro y ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hy)
    · show ratMat X (gW X γ) *ᵥ X.crd (X.eX a) = X.crd (X.eX a)
      rw [ratMat_crd, gW_e]
    · show ratMat X (gW X γ) *ᵥ X.crd (X.fY a) = X.crd (X.fY a)
      rw [ratMat_crd, gW_f]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      show ratMat X (gW X γ) *ᵥ X.crd (X.zu u) = X.crd (X.zu u)
      rw [ratMat_crd, stabilizer_fix_anisotropic X u hγ]
  set c := ratGam X u _ hM hfix with hc
  have e2 : ∀ y, X.B.I.fmat (rfinU X _ hM)⁻¹ *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (gW X γ.symm y)) := by
    intro y
    have h3 : X.B.I.fmat (rfinU X _ hM) *ᵥ incl X.B.I (X.crd (gW X γ.symm y)) = incl X.B.I (X.crd y) := by
      rw [fmat_rfinU]
      have h4 : incl X.B.I (ratMat X (gW X γ) *ᵥ X.crd (gW X γ.symm y)) =
          (ratMat X (gW X γ)).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
            incl X.B.I (X.crd (gW X γ.symm y)) := by
        funext i
        exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (ratMat X (gW X γ))
          (X.crd (gW X γ.symm y)) i
      show (ratMat X (gW X γ)).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
          incl X.B.I (X.crd (gW X γ.symm y)) = _
      rw [← h4, ratMat_crd, gW_gW X u hγ hγ' (fun w => γ.apply_symm_apply w) y]
    rw [← h3, mulVec_mulVec, fmat_inv_mul, one_mulVec]
  have hlat : ∀ y, y ∈ latOf X u (iotaF X u c * h) ↔ y ∈ latOf X u h' := by
    intro y
    have e : (((iotaF X u c * h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ =
        ((h : X.B.I.Gf) * X.xu u)⁻¹ * (rfinU X _ hM)⁻¹ := by
      rw [Subgroup.coe_mul, hc, iotaF_ratGam]
      group
    rw [mem_latOf, mem_latOf]
    show X.B.I.fmat ((((iotaF X u c * h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
    rw [e, fmat_mul, ← mulVec_mulVec, e2, ← mem_latOf, ← mem_latOf]
    constructor
    · intro hy
      have h5 := gW_mem X u h h' hmap hy
      rwa [gW_gW X u hγ hγ' (fun w => γ.apply_symm_apply w) y] at h5
    · intro hy
      exact gW_mem X u h' h hmap' hy
  have hL : PIW.AdelClassFin.abelian₂ X.B.I (((iotaF X u c * h : Hfin X u) : X.B.I.Gf) * X.xu u) =
      PIW.AdelClassFin.abelian₂ X.B.I ((h' : X.B.I.Gf) * X.xu u) := by
    ext v
    show X.B.I.fmat _ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf ↔ X.B.I.fmat _ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf
    have e : PIW.AdelClassFin.iv X.B.I v = incl X.B.I (X.crd (toV X v)) := by rw [crd_toV]; rfl
    rw [e]
    exact hlat (toV X v)
  obtain ⟨k0, hk0, hk0eq⟩ := PIW.AdelClassFin.lattice_map_injective X.B.I _ _ hL
  refine ⟨c, (iotaF X u c * h)⁻¹ * h', by group, ?_⟩
  have hcoe : ((h * ((iotaF X u c * h)⁻¹ * h') : Hfin X u) : X.B.I.Gf) * X.xu u =
      ((h : X.B.I.Gf) * X.xu u) * k0 := by
    have key : (h' : X.B.I.Gf) =
        ((iotaF X u c : Hfin X u) : X.B.I.Gf) * (h : X.B.I.Gf) * X.xu u * k0 * (X.xu u)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, hk0eq]
      simp only [Subgroup.coe_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [key]
    group
  ext y
  show X.B.I.fmat ((((h * ((iotaF X u c * h)⁻¹ * h') : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ
      incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹) *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf
  rw [hcoe, _root_.mul_inv_rev, fmat_mul, ← mulVec_mulVec]
  exact kset_iff X hk0 _

theorem latRowLat_of (hLG : LatDictZ.LamGenus) {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : LatRowLat X u :=
  fun h Λ hΛ => isRowLat_of X u h Λ hΛ (sameGenus_of X u hLG h Λ hΛ)

theorem latSurj_of (hZ : LatDictZ.ZOrbit) {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : LatSurj X u :=
  lattice_surjective_of_orbit X u hZ

end Formalism.L2.SG.Pf
