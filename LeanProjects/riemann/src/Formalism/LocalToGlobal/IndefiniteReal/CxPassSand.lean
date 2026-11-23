import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.GlobalTheory.PassageBaseSymmetricLevels
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass.Sand

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

def IsPr (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (u p : Fin n → K) : Prop :=
  p ∈ W ∧ ∀ w ∈ W, star w ⬝ᵥ H *ᵥ (u - p) = 0

theorem star_mulVec_dot {m : ℕ} (A : Matrix (Fin n) (Fin m) K) (y : Fin m → K) (v : Fin n → K) :
    star (A *ᵥ y) ⬝ᵥ v = star y ⬝ᵥ Aᴴ *ᵥ v := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem IsPr.unique {H : Matrix (Fin n) (Fin n) K} (hH : ∀ x, star x ⬝ᵥ H *ᵥ x = 0 → x = 0)
    {W : Submodule K (Fin n → K)} {u p p' : Fin n → K} (h : IsPr H W u p) (h' : IsPr H W u p') :
    p = p' := by
  have hw : p' - p ∈ W := W.sub_mem h'.1 h.1
  have e : star (p' - p) ⬝ᵥ H *ᵥ (p' - p) =
      star (p' - p) ⬝ᵥ H *ᵥ (u - p) - star (p' - p) ⬝ᵥ H *ᵥ (u - p') := by
    rw [← dotProduct_sub, ← Matrix.mulVec_sub]
    congr 2
    abel
  rw [h.2 _ hw, h'.2 _ hw, sub_zero] at e
  exact (sub_eq_zero.mp (hH _ e)).symm

theorem IsPr.map {H : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)} {u p : Fin n → K}
    (h : IsPr H W u p) {M M' : Matrix (Fin n) (Fin n) K} (hM : ∀ x ∈ W, M *ᵥ x ∈ W)
    (hM' : ∀ x ∈ W, M' *ᵥ x ∈ W) (hadj : H * M = M'ᴴ * H) : IsPr H W (M *ᵥ u) (M *ᵥ p) := by
  refine ⟨hM p h.1, fun w hw => ?_⟩
  rw [← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, ← star_mulVec_dot]
  exact h.2 _ (hM' w hw)

theorem IsPr.smul {H : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)} {u p : Fin n → K}
    (h : IsPr H W u p) (c : K) : IsPr H W (c • u) (c • p) := by
  refine ⟨W.smul_mem c h.1, fun w hw => ?_⟩
  rw [← smul_sub, Matrix.mulVec_smul, dotProduct_smul, h.2 w hw, smul_zero]

theorem IsPr.mono {H : Matrix (Fin n) (Fin n) K} {W W' : Submodule K (Fin n → K)} {u p : Fin n → K}
    (h : IsPr H W u p) (hle : W' ≤ W) (hp : p ∈ W') : IsPr H W' u p := by
  exact ⟨hp, fun w hw => h.2 w (hle hw)⟩

end Gen

section Aniso

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

theorem aniso {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {H : Matrix (Fin n) (Fin n) K}
    (hH : (H.map v0.embedding).PosDef) (x : Fin n → K) (hx : star x ⬝ᵥ H *ᵥ x = 0) : x = 0 := by
  have hs : ∀ a : K, v0.embedding (star a) = star (v0.embedding a) := fun a => by
    rw [hv0 a]; rfl
  by_contra hne
  have hy : (fun i => v0.embedding (x i)) ≠ 0 := by
    intro h0
    apply hne
    funext i
    have hi := congrFun h0 i
    simpa using hi
  have key : star (fun i => v0.embedding (x i)) ⬝ᵥ (H.map v0.embedding) *ᵥ (fun i => v0.embedding (x i)) =
      v0.embedding (star x ⬝ᵥ H *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, Pi.star_apply, hs]
  have hpos := hH.dotProduct_mulVec_pos hy
  rw [key, hx, map_zero] at hpos
  exact lt_irrefl _ hpos

end Aniso

section Lv

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

def Wl (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) : Submodule K (Fin B.S.dim → K) :=
  B.coord Z ⊓ LinearMap.range (B.vE ℓ).mulVecLin

def Phi (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (f : Fin (B.nV ℓ) → K) : Fin B.S.dim → K :=
  B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ (B.Pq ℓ Z *ᵥ f))

theorem HV_eq (ℓ : Lvl K G) : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl

theorem toF_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (f : Fin (B.nV ℓ) → K) :
    B.toF ℓ Z (B.Pq ℓ Z *ᵥ f) = B.S.basis.equivFun.symm (Phi B ℓ Z f) := rfl

theorem isPr_Phi {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hOk : B.Ok s) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (f : Fin (B.nV ℓ) → K) :
    IsPr B.S.H (Wl B ℓ Z) (B.vE ℓ *ᵥ f) (Phi B ℓ Z f) := by
  obtain ⟨_, h2⟩ := BlockDat.Pq_orth (B := B) (ℓ := ℓ) (Z := Z) hv0 hOk hX
  refine ⟨⟨?_, ⟨_, rfl⟩⟩, ?_⟩
  · exact B.zE_mem ℓ Z (B.Pq ℓ Z *ᵥ f)
  · rintro w ⟨hwZ, ⟨z, rfl⟩⟩
    have hz : z ∈ B.Z0 ℓ Z := hwZ
    obtain ⟨y, rfl⟩ := B.exists_zE ℓ Z hz
    have hc : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h3 : (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) * (1 - B.zE ℓ Z * B.Pq ℓ Z) = 0 := by
      rw [HV_eq, Matrix.mul_smul, Matrix.smul_mul] at h2
      exact (smul_eq_zero.1 h2).resolve_left (inv_ne_zero hc)
    have h4 : (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * (B.S.H * (B.vE ℓ * (1 - B.zE ℓ Z * B.Pq ℓ Z)))) = 0 := by
      simpa only [Matrix.mul_assoc] using h3
    have e : B.vE ℓ *ᵥ f - Phi B ℓ Z f = (B.vE ℓ * (1 - B.zE ℓ Z * B.Pq ℓ Z)) *ᵥ f := by
      unfold Phi
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    show star ((B.vE ℓ).mulVecLin (B.zE ℓ Z *ᵥ y)) ⬝ᵥ B.S.H *ᵥ (B.vE ℓ *ᵥ f - Phi B ℓ Z f) = 0
    rw [Matrix.mulVecLin_apply, e, star_mulVec_dot, star_mulVec_dot, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [h4, Matrix.zero_mulVec, dotProduct_zero]

theorem range_vE_full (X : Finset (G → K)) :
    LinearMap.range (B.vE (Lvl.full X)).mulVecLin = LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X (⊥ : Subgroup G) 1))).2
  simp only [goodAt, level_idempotent_bot K G, mul_one] at h
  exact h

theorem range_vE_lvl {X : Finset (G → K)} (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin ⊓ B.S.lvlPart B.r P ψ := by
  exact good_part_spec_of_central idempotent_central K B.S G B.r X hX P ψ

theorem equivFun_symm_act (g : G) (x : Fin B.S.dim → K) :
    B.r g (B.S.basis.equivFun.symm x) = B.S.basis.equivFun.symm (B.S.actMat B.r g *ᵥ x) := by
  apply B.S.basis.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  conv_rhs => rw [← B.S.basis.equivFun.apply_symm_apply x]
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact (LinearMap.toMatrix_mulVec_repr ..).symm

theorem actMat_coord {Z : Submodule K B.S.Forms} (hZ : ∀ g : G, Z ≤ Z.comap (B.r g)) (g : G)
    {x : Fin B.S.dim → K} (hx : x ∈ B.coord Z) : B.S.actMat B.r g *ᵥ x ∈ B.coord Z := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨B.r g z, hZ g hz, ?_⟩
  have h1 := equivFun_symm_act B g (B.S.basis.equivFun z)
  rw [LinearEquiv.symm_apply_apply] at h1
  simp only [LinearEquiv.coe_coe]
  rw [h1, LinearEquiv.apply_symm_apply]

private theorem gaMat_single_lemma (g : G) :
    B.S.gaMat B.r (MonoidAlgebra.single g 1) = B.S.actMat B.r g := by
  first
  | (simp [CSD.gaMat, MonoidAlgebra.coeff_single, Finset.sum_ite_eq']; done)
  | (simp [CSD.gaMat, Finsupp.single_apply]; done)
  | (simp [CSD.gaMat, MonoidAlgebra.single_apply]; done)
  | (unfold CSD.gaMat; rw [Finset.sum_eq_single g] <;> simp_all [Finsupp.single_apply]; done)
  | simp only [CSD.gaMat]

theorem action_preserves_idempotent_range {X : Finset (G → K)} (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (g : G)
    {x : Fin B.S.dim → K} (hx : x ∈ LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin) :
    B.S.actMat B.r g *ᵥ x ∈ LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
  have hs := gaMat_single_lemma B g
  obtain ⟨y, rfl⟩ := hx
  have hc := (idempotent_central K G X hX).2 (MonoidAlgebra.single g 1)
  have hm := (group_action_matrix_hom K B.S G B.r).2
  refine ⟨B.S.actMat B.r g *ᵥ y, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hs, ← hm, ← hm, hc]

theorem gaMat_mem {V : Submodule K (Fin B.S.dim → K)} (hV : ∀ g : G, ∀ x ∈ V, B.S.actMat B.r g *ᵥ x ∈ V)
    (a : MonoidAlgebra K G) {x : Fin B.S.dim → K} (hx : x ∈ V) : B.S.gaMat B.r a *ᵥ x ∈ V := by
  show (∑ t : G, a.coeff t • B.S.actMat B.r t) *ᵥ x ∈ V
  refine Finset.sum_induction _ (fun M => M *ᵥ x ∈ V) (fun M N hM hN => ?_) ?_ (fun t _ => ?_)
  · try dsimp only at hM hN ⊢
    rw [Matrix.add_mulVec]
    exact V.add_mem hM hN
  · try dsimp only
    rw [Matrix.zero_mulVec]
    exact V.zero_mem
  · try dsimp only
    first
    | rw [Matrix.smul_mulVec]
    | rw [Matrix.smul_mulVec_assoc]
    | rw [Matrix.mulVec_smul_assoc]
    exact V.smul_mem _ (hV t x hx)

theorem actMat_alt {X : Finset (G → K)} (hX : ∀ χ ∈ X, IsAbsIrrChar χ) {Z : Submodule K B.S.Forms}
    (hZ : ∀ g : G, Z ≤ Z.comap (B.r g)) (g : G) :
    ∀ x ∈ Wl B (Lvl.full X) Z, B.S.actMat B.r g *ᵥ x ∈ Wl B (Lvl.full X) Z := by
  intro x hx
  unfold Wl at hx ⊢
  rw [range_vE_full B X] at hx ⊢
  exact ⟨actMat_coord B hZ g hx.1, action_preserves_idempotent_range B hX g hx.2⟩

end Lv

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hOk : B.Ok s)
  {X : Finset (G → K)} (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms)
  (hZ : ∀ g : G, Z ≤ Z.comap (B.r g)) (P : Subgroup G) (ψ : P →* Kˣ)

include hX in
theorem W_le : Wl B ⟨X, P, ψ⟩ Z ≤ Wl B (Lvl.full X) Z := by
  unfold Wl
  rw [range_vE_lvl B hX P ψ, range_vE_full B X]
  exact inf_le_inf_left _ inf_le_left

include hX in
theorem mem_WP {p : Fin B.S.dim → K} (h : p ∈ Wl B (Lvl.full X) Z) (hp : p ∈ B.S.lvlPart B.r P ψ) :
    p ∈ Wl B ⟨X, P, ψ⟩ Z := by
  unfold Wl at h ⊢
  rw [range_vE_lvl B hX P ψ]
  rw [range_vE_full B X] at h
  exact ⟨h.1, h.2, hp⟩

include hv0 hOk hX hZ in
theorem isPr_e {u p : Fin B.S.dim → K} (h : IsPr B.S.H (Wl B (Lvl.full X) Z) u p) :
    IsPr B.S.H (Wl B (Lvl.full X) Z) (B.S.gaMat B.r (lvlIdem P ψ) *ᵥ u)
      (B.S.gaMat B.r (lvlIdem P ψ) *ᵥ p) := by
  have hst : ∀ x ∈ Wl B (Lvl.full X) Z, B.S.gaMat B.r (lvlIdem P ψ) *ᵥ x ∈ Wl B (Lvl.full X) Z :=
    fun x hx => gaMat_mem B (actMat_alt B hX hZ) (lvlIdem P ψ) hx
  refine h.map hst hst ?_
  have h1 := group_action_matrix_adjoint K B.S G B.r hOk.act (lvlIdem P ψ)
  rw [(level_idempotent_spec K v0 hv0 G P ψ).1.selfAdj] at h1
  exact h1.symm

include hv0 hOk hX hZ in
theorem isPr_down {u p : Fin B.S.dim → K} (h : IsPr B.S.H (Wl B (Lvl.full X) Z) u p)
    (hu : u ∈ B.S.lvlPart B.r P ψ) : IsPr B.S.H (Wl B ⟨X, P, ψ⟩ Z) u p := by
  have hH := aniso hv0 (hOk.hpos v0)
  have he := isPr_e B hv0 hOk hX Z hZ P ψ h
  rw [B.S.lvlIdem_mulVec_of_mem B.r P ψ u hu] at he
  have hep : B.S.gaMat B.r (lvlIdem P ψ) *ᵥ p = p := (h.unique hH he).symm
  have hpl : p ∈ B.S.lvlPart B.r P ψ := by
    rw [← level_part_spec K B.S G B.r P ψ]
    exact ⟨p, hep⟩
  exact h.mono (W_le B hX Z P ψ) (mem_WP B hX Z P ψ h.1 hpl)

theorem M_eq [Fintype P] : (∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G)) =
    (Nat.card P : K) • B.S.gaMat B.r (lvlIdem P ψ) := by
  classical
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : ∀ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G) =
      (Nat.card P : K) • (((Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K)) • B.S.actMat B.r (k : G)) := by
    intro k
    rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, map_inv]
  rw [CSD.gaMat_lvlIdem, Finset.smul_sum]
  calc _ = ∑ k : P, (Nat.card P : K) • (((Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K)) •
          B.S.actMat B.r (k : G)) := Finset.sum_congr rfl fun k _ => key k
    _ = _ := by
        congr 1
        ext a
        simp

include hv0 hOk hX hZ in

theorem sub_toF : ∀ f ∈ B.Mt ⟨X, P, ψ⟩, ∃ f' ∈ B.Mt (Lvl.full X),
    B.toF ⟨X, P, ψ⟩ Z ((B.Pq ⟨X, P, ψ⟩ Z).mulVec f) = B.toF (Lvl.full X) Z ((B.Pq (Lvl.full X) Z).mulVec f') := by
  intro f hf
  have hH := aniso hv0 (hOk.hpos v0)
  have hfN : B.vE ⟨X, P, ψ⟩ *ᵥ f ∈ B.S.nabLat := hf
  have hmem := (range_vE_lvl B hX P ψ).le (⟨f, rfl⟩ : B.vE ⟨X, P, ψ⟩ *ᵥ f ∈ LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin)
  have hu : B.vE ⟨X, P, ψ⟩ *ᵥ f ∈ LinearMap.range (B.vE (Lvl.full X)).mulVecLin := by
    rw [range_vE_full]
    exact hmem.1
  obtain ⟨f', hf'⟩ := hu
  rw [Matrix.mulVecLin_apply] at hf'
  refine ⟨f', ?_, ?_⟩
  · show B.vE (Lvl.full X) *ᵥ f' ∈ B.S.nabLat
    rw [hf']
    exact hfN
  · rw [toF_eq, toF_eq]
    refine congrArg B.S.basis.equivFun.symm ?_
    have h0 := isPr_Phi B hv0 hOk (Lvl.full X) hX Z f'
    rw [hf'] at h0
    have hP := isPr_Phi B hv0 hOk ⟨X, P, ψ⟩ hX Z f
    exact hP.unique hH (isPr_down B hv0 hOk hX Z hZ P ψ h0 hmem.2)

include hv0 hOk hX hZ in

theorem act_toF (g : G) : ∀ f ∈ B.Mt (Lvl.full X), ∃ f' ∈ B.Mt (Lvl.full X),
    B.r g (B.toF (Lvl.full X) Z ((B.Pq (Lvl.full X) Z).mulVec f)) =
      B.toF (Lvl.full X) Z ((B.Pq (Lvl.full X) Z).mulVec f') := by
  intro f hf
  have hH := aniso hv0 (hOk.hpos v0)
  have hfN : B.vE (Lvl.full X) *ᵥ f ∈ B.S.nabLat := hf
  have hu0 : B.vE (Lvl.full X) *ᵥ f ∈ LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
    rw [← range_vE_full]
    exact ⟨f, rfl⟩
  have hu : B.S.actMat B.r g *ᵥ (B.vE (Lvl.full X) *ᵥ f) ∈ LinearMap.range (B.vE (Lvl.full X)).mulVecLin := by
    rw [range_vE_full]
    exact action_preserves_idempotent_range B hX g hu0
  obtain ⟨f', hf'⟩ := hu
  rw [Matrix.mulVecLin_apply] at hf'
  refine ⟨f', ?_, ?_⟩
  · show B.vE (Lvl.full X) *ᵥ f' ∈ B.S.nabLat
    rw [hf']
    exact (action_preserves_lattice K B.S G B.r hOk.act g).1 _ hfN
  · rw [toF_eq, toF_eq, equivFun_symm_act]
    refine congrArg B.S.basis.equivFun.symm ?_
    have hadj : B.S.H * B.S.actMat B.r g = (B.S.actMat B.r g⁻¹)ᴴ * B.S.H := by
      rw [CSD.actMat_adj B.S B.r hOk.act g⁻¹, inv_inv]
    have h0 := isPr_Phi B hv0 hOk (Lvl.full X) hX Z f
    have h1 := h0.map (actMat_alt B hX hZ g) (actMat_alt B hX hZ g⁻¹) hadj
    have h2 := isPr_Phi B hv0 hOk (Lvl.full X) hX Z f'
    rw [hf'] at h2
    exact h1.unique hH h2

include hv0 hOk hX hZ in

theorem avg_toF [Fintype P] : ∀ f ∈ B.Mt (Lvl.full X), ∃ f' ∈ B.Mt ⟨X, P, ψ⟩,
    ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.r (k : G) (B.toF (Lvl.full X) Z ((B.Pq (Lvl.full X) Z).mulVec f)) =
      B.toF ⟨X, P, ψ⟩ Z ((B.Pq ⟨X, P, ψ⟩ Z).mulVec f') := by
  intro f hf
  have hH := aniso hv0 (hOk.hpos v0)
  have hfN : B.vE (Lvl.full X) *ᵥ f ∈ B.S.nabLat := hf
  have hM := M_eq B P ψ
  have hu0 : B.vE (Lvl.full X) *ᵥ f ∈ LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
    rw [← range_vE_full]
    exact ⟨f, rfl⟩
  have hMuN : (∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G)) *ᵥ (B.vE (Lvl.full X) *ᵥ f) ∈
      B.S.nabLat := by
    rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.smul_mulVec]
    have hpow : ((((ψ k)⁻¹ : Kˣ) : K)) ^ Nat.card P = 1 := by
      rw [← map_inv]
      exact psi_pow P ψ k⁻¹
    obtain ⟨b, hb⟩ := exists_int_of_pow_eq_one Nat.card_pos.ne' hpow
    rw [← hb]
    exact Submodule.smul_mem _ b ((action_preserves_lattice K B.S G B.r hOk.act k).1 _ hfN)
  have hMul : (∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G)) *ᵥ (B.vE (Lvl.full X) *ᵥ f) ∈
      B.S.lvlPart B.r P ψ := by
    rw [hM, Matrix.smul_mulVec, ← level_part_spec K B.S G B.r P ψ]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  have hMuE : (∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G)) *ᵥ (B.vE (Lvl.full X) *ᵥ f) ∈
      LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
    rw [hM, Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (gaMat_mem B (fun g x hx => action_preserves_idempotent_range B hX g hx) _ hu0)
  have hMu : (∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • B.S.actMat B.r (k : G)) *ᵥ (B.vE (Lvl.full X) *ᵥ f) ∈
      LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin := by
    rw [range_vE_lvl B hX P ψ]
    exact ⟨hMuE, hMul⟩
  obtain ⟨fb, hfb⟩ := hMu
  rw [Matrix.mulVecLin_apply] at hfb
  refine ⟨fb, ?_, ?_⟩
  · show B.vE ⟨X, P, ψ⟩ *ᵥ fb ∈ B.S.nabLat
    rw [hfb]
    exact hMuN
  · have h0 := isPr_Phi B hv0 hOk (Lvl.full X) hX Z f
    have h1 := (isPr_e B hv0 hOk hX Z hZ P ψ h0).smul (Nat.card P : K)
    rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← hM] at h1
    have h2 := isPr_down B hv0 hOk hX Z hZ P ψ h1 hMul
    have h3 := isPr_Phi B hv0 hOk ⟨X, P, ψ⟩ hX Z fb
    rw [hfb] at h3
    have h4 := h2.unique hH h3
    rw [toF_eq B ⟨X, P, ψ⟩ Z fb, ← h4, Matrix.sum_mulVec, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toF_eq, equivFun_symm_act, Matrix.smul_mulVec, map_smul]

end Main

end Formalism.IndefR.CxPass.Sand

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace Sand

section Glue

variable {K : Type} [Field K] [NumberField K]

theorem glue_lattice {D : ℕ} {T : Type} [Finite T] (t0 : T) (μ : HeightOneSpectrum (𝓞 K) → T)
    (L : T → Submodule (𝓞 K) (Fin D → K)) (hL : ∀ t, Submodule.IsLattice K (L t)) :
    Submodule.IsLattice K (glueLat fun w => L (μ w)) := by
  classical
  have := Fintype.ofFinite T
  have hGmem : ∀ x, x ∈ glueLat (fun w => L (μ w)) ↔
      ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L (μ w)) := by
    intro x
    unfold glueLat
    exact Submodule.mem_iInf _
  choose a ha0 ha using fun t => GluingInclusion.denom (K := K) (L t0) (L t) (Submodule.IsLattice.fg (self := hL t0))
    (Submodule.IsLattice.span_eq_top (self := hL t))
  have hc0 : (∏ t, a t) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => ha0 t)
  have hcL : ∀ x ∈ L t0, (∏ t, a t) • x ∈ glueLat (fun w => L (μ w)) := by
    intro x hx
    rw [hGmem]
    intro w
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ (μ w))
    rw [hr, mul_comm, mul_smul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ ((L (μ w)).smul_mem r (ha (μ w) x hx))
  have hle : glueLat (fun w => L (μ w)) ≤ ⨆ t, L t := by
    intro x hx
    refine GluingInclusion.lg (RingOfIntegers.not_isField K) _ x fun w => ?_
    exact Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (le_iSup L (μ w)) ((hGmem x).mp hx w)
  have hNfg : (⨆ t, L t).FG := Submodule.fg_iSup L fun t => Submodule.IsLattice.fg (self := hL t)
  have hinvsmul : ∀ (r : 𝓞 K), r ≠ 0 → ∀ y : Fin D → K, (algebraMap (𝓞 K) K r)⁻¹ • (r • y) = y := by
    intro r hr y
    have : algebraMap (𝓞 K) K r ≠ 0 := by simpa using (IsFractionRing.injective (𝓞 K) K).ne hr
    rw [← algebraMap_smul K r y, smul_smul, inv_mul_cancel₀ this, one_smul]
  refine ⟨Submodule.FG.of_le hNfg hle, ?_⟩
  rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (self := hL t0), Submodule.span_le]
  intro x hx
  rw [← hinvsmul _ hc0 x]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hcL x hx))

end Glue

theorem cpt_sum_smul {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (c : ι → K)
    (x : ι → Fin n → K) : cpt σ (∑ i ∈ s, c i • x i) = ∑ i ∈ s, σ (c i) • cpt σ (x i) := by
  funext j
  simp only [cpt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]

end Sand

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem mem_RRg {x : Fin I.Sg.D → K} : x ∈ I.Sg.RR ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ c ∈ w.asIdeal.primeCompl,
    ∃ z ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      I.X.rowMat I.cg false (I.X.μ w) *ᵥ z = c • x := by
  constructor
  · intro h w
    obtain ⟨c, hc, hcx⟩ := (Submodule.mem_iInf _).mp h w
    exact ⟨c, hc, (exponent_index_lattice.mem_matLat _ _ _).mp hcx⟩
  · intro h
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    obtain ⟨c, hc, z, hz, e⟩ := h w
    exact ⟨c, hc, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨z, hz, e⟩⟩

theorem mem_RRb (b : Bool) {x : Fin (I.Sb b).D → K} : x ∈ (I.Sb b).RR ↔ ∀ w : HeightOneSpectrum (𝓞 K),
    ∃ c ∈ w.asIdeal.primeCompl, ∃ z ∈ (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ (I.X.μ w),
      I.X.rowMat I.cr b (I.X.μ w) *ᵥ z = c • x := by
  constructor
  · intro h w
    obtain ⟨c, hc, hcx⟩ := (Submodule.mem_iInf _).mp h w
    exact ⟨c, hc, (exponent_index_lattice.mem_matLat _ _ _).mp hcx⟩
  · intro h
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    obtain ⟨c, hc, z, hz, e⟩ := h w
    exact ⟨c, hc, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨z, hz, e⟩⟩

section Prin

variable {I} {s : ℕ} (hH : I.Hyp s)
include hH

theorem hZ_of (t : T) : ∀ g : G, I.X.Z t ≤ (I.X.Z t).comap ((I.A.fam.R t).r g) :=
  fun g _ hz => hH.stable.1 t (Sum.inr g) (Submodule.mem_map_of_mem hz)

theorem key_g (t : T) (x : Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t) → K) :
    I.iCg (cpt I.A.fam.base.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.Θ t (I.X.jR t (I.cg.toR I.X.zs false t x)) := by
  have h1 : I.iCg (cpt I.A.fam.base.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding x) := by
    rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hH.ratMug t)]
    refine relMat_spec _ _ (fun k => ?_) _
    rw [← (hH.h2g.2 t).2]
    exact ⟨_, rfl⟩
  rw [h1, CxData.iC_eq_comp, CxData.lin_uQ_cpt]

theorem inj_g {x y : Fin I.Sg.D → K}
    (h : I.iCg (cpt I.A.fam.base.v0.embedding x) = I.iCg (cpt I.A.fam.base.v0.embedding y)) : x = y :=
  cpt_injective _ (hH.h2g.1 h)

theorem rowG_surj (t : T) : Function.Surjective (I.X.rowMat I.cg false t).mulVec :=
  (bij_of_map I.A.fam.base.v0.embedding _ (by
    rw [CxData.rowMat, kMat_map _ (hH.ratMug t)]
    exact relMat_bij _ _ hH.h2g.1 (hH.h2g.2 t).1 (hH.h2g.2 t).2)).2

theorem epM_idem (hρ : I.PRho) (P : Subgroup G) (ψ : P →* Kˣ) : I.epM P ψ * I.epM P ψ = I.epM P ψ := by
  obtain ⟨h1, hmul, -⟩ := hρ s hH
  let ρh : G →* Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
    { toFun := I.ρf, map_one' := h1, map_mul' := hmul }
  have e : I.epM P ψ = Formalism.L2.GlobalTheoryTheory.DivPassage2.typeProj ρh P ψ := rfl
  rw [e]
  exact Formalism.L2.GlobalTheoryTheory.DivPassage2.typeProj_mul_self ρh P ψ

theorem toRg_inj (t : T) : Function.Injective (I.cg.toR I.X.zs false t) :=
  BlockDat.toF_injective (I.A.fam.R t) (Lvl.full I.A.fam.X) (I.X.Z t)

theorem sub_g (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      J *ᵥ y ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  obtain ⟨f', hf', he⟩ := Sand.sub_toF (B := I.A.fam.R t) (hv0 := hH.ok.conj) (hOk := hH.ok.what₂ t)
    (hX := hH.ok.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      I.cg.toR I.X.zs false t z =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he.symm⟩
  obtain ⟨z, hz, hze⟩ := hex
  have e : J *ᵥ ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) = z := toRg_inj hH t (by rw [hJ, hze])
  rw [e]
  exact hz

theorem avg_g (hρ : I.PRho) (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
        (Nat.card P : K) • (I.epM P ψ *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) = I.X.rowMat I.cg false t *ᵥ (J *ᵥ z) := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  let _ : Fintype P := Fintype.ofFinite P
  obtain ⟨fb, hfb, he⟩ := Sand.avg_toF (B := I.A.fam.R t) (hv0 := hH.ok.conj) (hOk := hH.ok.what₂ t)
    (hX := hH.ok.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • (I.A.fam.R t).r (k : G)
        (I.cg.toR I.X.zs false t ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)) =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨fb, hfb, rfl⟩, he⟩
  obtain ⟨z, hz, hze⟩ := hex
  refine ⟨z, hz, ?_⟩
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hep : I.epM P ψ = (Nat.card P : K)⁻¹ • ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G) := rfl
  apply inj_g hH
  rw [key_g hH, hJ, ← hze, hep, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  erw [Sand.cpt_sum_smul]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  erw [map_smul, (hρ s hH).2.2 (k : G) (I.X.rowMat I.cg false t *ᵥ ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)),
    key_g hH t ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f), LinearMap.map_smulₛₗ, map_smul]
  exact congrArg _ (hH.gequiv t k _).symm

theorem sub_b (hJt : I.PJt) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
      I.Jt b t *ᵥ y ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  cases b
  · exact sub_g hH t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact sub_g hH t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

theorem avg_b (hJt : I.PJt) (hρ : I.PRho) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
        (Nat.card (I.lvP b) : K) • (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) =
          I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ z) := by
  cases b
  · exact avg_g hH hρ t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact avg_g hH hρ t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

end Prin

theorem pLat_of (_hJt : I.PJt) : I.PLat := by
  intro s hH
  have : Finite T := hH.ok.tup_fin
  exact Sand.glue_lattice I.A.fam.base.μ0 I.X.μ
    (fun t => matLat (I.X.rowMat I.cg false t) ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t))
    (fun t => GluingInclusion.matLat_lattice' _ (rowG_surj hH t) _
      (show Submodule.IsLattice K ((I.A.fam.R t).abelian₂ (Lvl.full I.A.fam.X) (I.X.Z t)) from
        BlockDat.Lam_lat hH.ok.conj (hH.ok.what₂ t) hH.ok.irr))

theorem pGLat_of (_hJt : I.PJt) (hρ : I.PRho) : I.PGLat := by
  intro s hH g x hx
  rw [mem_RRg] at hx ⊢
  intro w
  obtain ⟨c, hc, z, hz, hzx⟩ := hx w
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hz
  obtain ⟨f', hf', he⟩ := Sand.act_toF (B := I.A.fam.R (I.X.μ w)) (hv0 := hH.ok.conj) (hOk := hH.ok.what₂ _)
    (hX := hH.ok.irr) (Z := I.X.Z (I.X.μ w)) (hZ := hZ_of hH _) g f hf
  have hex : ∃ z ∈ (lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      (I.A.fam.R (I.X.μ w)).r g (I.cg.toR I.X.zs false (I.X.μ w)
        ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)) =
        I.cg.toR I.X.zs false (I.X.μ w) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he⟩
  obtain ⟨z', hz', hze⟩ := hex
  refine ⟨c, hc, z', hz', ?_⟩
  rw [← exponent_index_lattice.mulVec_osmul, ← hzx]
  apply inj_g hH
  erw [key_g hH, (hρ s hH).2.2 g (I.X.rowMat I.cg false (I.X.μ w) *ᵥ ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)),
    key_g hH (I.X.μ w) ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f), ← hze]
  exact hH.gequiv _ g _

theorem pSand_of (hJt : I.PJt) (hJ : I.PJ) (hρ : I.PRho) (hR : I.PRange) : I.PSand := by
  intro s hH b
  refine ⟨fun x hx => ?_, fun y hy hyr => ?_⟩
  · rw [mem_RRb] at hx
    rw [mem_RRg]
    intro w
    obtain ⟨c, hc, z, hz, hzx⟩ := hx w
    refine ⟨c, hc, I.Jt b (I.X.μ w) *ᵥ z, sub_b hH hJt b _ z hz, ?_⟩
    exact ((hJt s hH b _).2.2 z).symm.trans
      ((congrArg (fun v => I.Jm b *ᵥ v) hzx).trans (exponent_index_lattice.mulVec_osmul _ _ _))
  · obtain ⟨z0, hz0⟩ := LinearMap.mem_range.mp hyr
    have hyr' := hyr
    rw [← hR s hH b] at hyr'
    obtain ⟨x0, hx0⟩ := LinearMap.mem_range.mp hyr'
    rw [Matrix.mulVecLin_apply] at hz0 hx0
    have hidem : I.epM (I.lvP b) (I.lvψ b) *ᵥ y = y := by
      rw [← hz0, Matrix.mulVec_mulVec, epM_idem hH hρ]
    refine ⟨((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0, ?_, by rw [exponent_index_lattice.mulVec_osmul, hx0]⟩
    rw [mem_RRg] at hy
    rw [mem_RRb]
    intro w
    obtain ⟨c, hc, z, hz, hzy⟩ := hy w
    obtain ⟨zb, hzb, he⟩ := avg_b hH hJt hρ b (I.X.μ w) z hz
    refine ⟨c, hc, zb, hzb, ?_⟩
    apply (hJ s hH b).2
    have h3 : (Nat.card (I.lvP b) : K) •
        (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z)) =
        I.Jm b *ᵥ (c • (((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0)) := by
      have h4 : I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z) = c • y :=
        (congrArg (fun v => I.epM (I.lvP b) (I.lvψ b) *ᵥ v) hzy).trans (by rw [exponent_index_lattice.mulVec_osmul, hidem])
      rw [h4]
      simp only [exponent_index_lattice.mulVec_osmul]
      rw [hx0, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K), smul_comm]
    exact ((hJt s hH b _).2.2 zb).trans (he.symm.trans h3)

end In

end Formalism.IndefR.CxPass
