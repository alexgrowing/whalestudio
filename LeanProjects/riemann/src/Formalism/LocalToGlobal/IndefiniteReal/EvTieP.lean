import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

open Matrix
open scoped Matrix

noncomputable section

namespace Formalism.IndefR.Links.EvTie

open Formalism.L2.DIV Formalism.IndefR.Cx

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem dot_eq (S : CSD K) (u w : Fin S.dim → K) :
    S.csum (S.I u) (S.I w) = star u ⬝ᵥ S.H *ᵥ w := by
  simp only [CSD.csum, CSD.I, CSD.H, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun c => ?_
  rw [Pi.star_apply]
  ring

theorem proj_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) :
    ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z) =
      (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
  have hc : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hM : (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hinv : B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  calc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z)
      = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) * B.zE ℓ Z * B.Pq ℓ Z := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Nat.card ℓ.P : K) • (B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ)) := by
        rw [hM]
        simp only [BlockDat.HZ, BlockDat.Pq, orthPr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
        rw [hinv, Matrix.one_mul, Matrix.conjTranspose_mul,
          show (B.zE ℓ Z)ᴴ * (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) by
            simp only [Matrix.mul_assoc], hM, Matrix.mul_smul]

theorem dot_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ℓ Z) → K)
    (w : Fin (B.nV ℓ) → K) :
    star ((B.vE ℓ) *ᵥ ((B.zE ℓ Z) *ᵥ x)) ⬝ᵥ B.S.H *ᵥ ((B.vE ℓ) *ᵥ w) =
      star x ⬝ᵥ (((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem evTie_block (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) (x : Fin (B.dZ ℓ Z) → K) (y : Fin (B.nV ℓ) → K) :
    CSDForm.csumForm B.S (B.toF ℓ Z x) (B.S.basis.equivFun.symm ((B.vE ℓ) *ᵥ y)) =
      CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z ((B.Pq ℓ Z) *ᵥ y)) := by
  have key : ∀ a b : Fin B.S.dim → K, CSDForm.csumForm B.S (B.S.basis.equivFun.symm a)
      (B.S.basis.equivFun.symm b) = star a ⬝ᵥ B.S.H *ᵥ b := fun a b => dot_eq B.S a b
  have hT : ∀ v, B.toF ℓ Z v = B.S.basis.equivFun.symm (B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ v)) := fun v => rfl
  rw [hT, hT, key, key, dot_key, dot_key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ), proj_key B ℓ Z hdet]

end Block

section Face

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_det {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (F : Face3 D A3) (X : CxData A3.fam3.amb3)
    (hdet : ∀ t, IsUnit ((A3.A.fam.R t).HZ (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t)).det) :
    X.EVTie F.cr F.cv (F.eV X.zs) := by
  refine ⟨fun t y => ⟨y, rfl⟩, fun t y x => ?_⟩
  exact evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t) (hdet t) x y

end Face

section Ok

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_ok {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {s : ℕ} (hOk : A3.fam3.Ok3 s) (F : Face3 D A3)
    (X : CxData A3.fam3.amb3) : X.EVTie F.cr F.cv (F.eV X.zs) :=
  evTie_of_det F X fun t =>
    BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)

theorem evTie_real {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (hOk : ∃ s, A3.fam3.Ok3 s) (R : RealDat3 D A3 Ks) (F : Face3 D A3) :
    (R.toCx3 F).EVTie F.cr F.cv (F.eV (R.toCx3 F).zs) := by
  obtain ⟨s, hs⟩ := hOk
  exact evTie_of_ok hs F (R.toCx3 F)

end Ok

end Formalism.IndefR.Links.EvTie

end
