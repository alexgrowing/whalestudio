import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CSDForm

variable (S : CSD K)

def csumForm : S.Forms →ₗ⋆[K] S.Forms →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun f g => S.csum (f : S.Cl → S.V) (g : S.Cl → S.V))
    (fun f f' g => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply, mul_add,
        Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by ring)
    (fun f g g' => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun c _ => by ring)

theorem csumForm_apply (f g : S.Forms) : csumForm S f g = S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) := rfl

end CSDForm

namespace BlockGood

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)

def goodR (ℓ : Lvl K G) : Submodule K B.S.Forms :=
  LinearMap.range ((B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin)

theorem toF_mem_goodR (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ goodR B ℓ := by
  unfold goodR
  exact LinearMap.mem_range.2 ⟨(B.zE ℓ Z).mulVecLin y, rfl⟩

theorem toF_mem (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [← hs]
    exact ⟨y, rfl⟩
  obtain ⟨f, hf, he⟩ := hy
  have : B.toF ℓ Z y = f := by
    have he' : B.S.basis.equivFun f = (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) := he
    change B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) = f
    rw [← he', LinearEquiv.symm_apply_apply]
  rw [this]
  exact hf

theorem csum_toF (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (B.toF ℓ Z y : B.S.Cl → B.S.V) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HZ ℓ Z).mulVec y) := by
  change B.S.csum (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec x))) (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y))) = _
  rw [B.S.csum_sum]
  have h1 : ∀ u w : Fin B.S.dim → K, (∑ i, ∑ j, star (u i) * B.S.H i j * w j) = star u ⬝ᵥ B.S.H.mulVec w := by
    intro u w
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : (B.vE ℓ * B.zE ℓ Z)ᴴ * (B.S.H * B.vE ℓ) * B.zE ℓ Z = (Nat.card ℓ.P : K) • B.HZ ℓ Z := by
    simp only [BlockDat.HZ, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, Matrix.conjTranspose_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hP, one_smul, Matrix.mul_assoc]
  rw [h2]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csum_toF_at {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    v0.embedding (CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z y)) =
      ((Nat.card ℓ.P : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v0 x y := by
  rw [CSDForm.csumForm_apply, csum_toF, map_mul, map_natCast, Formalism.L2.DIV.majAt_eq]
  have hm : metOf (B.XQ ℓ Z v0) = (B.HZ ℓ Z).map v0.embedding := (BlockDat.XQ_herm hv0 h hX (Z := Z)).2
  rw [hm]
  push_cast
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0]
  rfl

end BlockGood

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem opC_adjoint (hK : X.KFormR) (cv : CrdV A) (hJ : X.JIsoR cv) (t : Bs.Tup) (i i' : A.OpR t)
    (h : ∀ f g, cv.hR t (A.opR t i f) g = cv.hR t f (A.opR t i' g)) :
    X.opC t i' = LinearMap.adjoint (X.opC t i) := by
  have h1 : X.opC t i = LinearMap.adjoint (X.opC t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK t).1 (hK t).2.ge) (Basis.mk (hK t).1 (hK t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jR_opR X hK, ← jR_opR X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

theorem opLC_adjoint (hK : X.KFormL) (cv : CrdV A) (hJ : X.JIsoL cv) (j : Bs.J) (t : Bs.Tup) (i i' : A.OpL j t)
    (h : ∀ f g, cv.hL j t (A.opL j t i f) g = cv.hL j t f (A.opL j t i' g)) :
    X.opLC j t i' = LinearMap.adjoint (X.opLC j t i) := by
  have h1 : X.opLC j t i = LinearMap.adjoint (X.opLC j t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK j t).1 (hK j t).2.ge) (Basis.mk (hK j t).1 (hK j t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jL_opL X hK, ← jL_opL X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def cvOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A.fam.amb where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A.fam.R t) (A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A.fam.R t) (A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A.fam.R t).S
  hL j t := CSDForm.csumForm (A.fam.L j t).S

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

theorem crdZ_of (X : CxData A.fam.amb) (b : Bool) : X.CrdZ (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b
  · exact BlockGood.toF_mem _ _ _ _
  · exact BlockGood.toF_mem _ _ _ _

theorem coordinates_in_good_part_of_definite (X : CxData A.fam.amb) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b
  · exact BlockGood.toF_mem_goodR _ _ _ _
  · exact BlockGood.toF_mem_goodR _ _ _ _

theorem crdZL_of (X : CxData A.fam.amb) (b : Bool) : X.CrdZL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b
  · exact BlockGood.toF_mem _ _ _ _
  · exact BlockGood.toF_mem _ _ _ _

theorem lift_coordinates_in_good_part_of_definite (X : CxData A.fam.amb) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b
  · exact BlockGood.toF_mem_goodR _ _ _ _
  · exact BlockGood.toF_mem_goodR _ _ _ _

def NPTie (X : CxData A.fam.amb) (P0 P1 : Subgroup G) : Prop :=
  X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)

theorem isoR_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1))
    (hn : NPTie X P0 P1) (b : Bool) : X.IsoR (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  rw [hJ t]
  cases b
  · rw [hn.1]
    exact BlockGood.csum_toF_at (A.fam.R t) hok.conj (hok.what₂ t) (A.fam.lvl P0 ψ0) hok.irr (X.zs.Z t) x y
  · rw [hn.2]
    exact BlockGood.csum_toF_at (A.fam.R t) hok.conj (hok.what₂ t) (A.fam.lvl P1 ψ1) hok.irr (X.zs.Z t) x y

theorem isoL_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1))
    (hn : NPTie X P0 P1) (b : Bool) : X.IsoL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  rw [hJ j t]
  cases b
  · rw [hn.1]
    exact BlockGood.csum_toF_at (A.fam.L j t) hok.conj (hok.lifts j t) (A.fam.lvlA P0 ψ0) hok.irr (X.zs.Zl j t) x y
  · rw [hn.2]
    exact BlockGood.csum_toF_at (A.fam.L j t) hok.conj (hok.lifts j t) (A.fam.lvlA P1 ψ1) hok.irr (X.zs.Zl j t) x y

def HeckeRatAllR (A : FamIn K G Pl0 T m) : Prop := ∀ t, (A.fam.R t).OkH

def HeckeRatAllL (A : FamIn K G Pl0 T m) : Prop := ∀ j t, (A.fam.L j t).OkH

theorem csum_act_inv {B : BlockDat K G Pl0} (h : B.S.ActGood B.r) (g : G) (f f' : B.S.Forms) :
    B.S.csum (B.r g f : B.S.Cl → B.S.V) (f' : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (B.r g⁻¹ f' : B.S.Cl → B.S.V) := by
  have h1 := h.unitary g f (B.r g⁻¹ f')
  have h2 : B.r g (B.r g⁻¹ f') = f' := by
    show (B.r g * B.r g⁻¹) f' = f'
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h2] at h1
  exact h1

theorem adjClosedR_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hH : HeckeRatAllR A) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with p | g
  · obtain ⟨p', hp'⟩ := (hH t).adj p
    exact ⟨Sum.inl p', X.opC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ t (Sum.inl p) (Sum.inl p') fun f f' => hp' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.what₂ t).act g f f'⟩

theorem adjClosedL_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hH : HeckeRatAllL A) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with p | g
  · obtain ⟨p', hp'⟩ := (hH j t).adj p
    exact ⟨Sum.inl p', X.opLC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ j t (Sum.inl p) (Sum.inl p') fun f f' => hp' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.lifts j t).act g f f'⟩

end Concrete

end Formalism.IndefR.Cx
