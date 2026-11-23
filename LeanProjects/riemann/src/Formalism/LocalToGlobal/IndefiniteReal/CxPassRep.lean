import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

def cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : Fin B.S.dim → K :=
  (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)

theorem toF_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y = B.S.basis.equivFun.symm (cv B ℓ Z y) := rfl

theorem cv_injective (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) : Function.Injective (cv B ℓ Z) := by
  intro x y h
  exact (subspace_image_spec K _ (B.Z0 ℓ Z)).1
    ((image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).1 h)

theorem cv_add (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    cv B ℓ Z (x + y) = cv B ℓ Z x + cv B ℓ Z y := by
  simp only [cv, Matrix.mulVec_add]

theorem cv_mulVec (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) {n : ℕ} (M : Matrix (Fin (B.dZ ℓ Z)) (Fin n) K)
    (x : Fin n → K) : cv B ℓ Z (M.mulVec x) = (B.vE ℓ * B.zE ℓ Z * M).mulVec x := by
  simp only [cv, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_coord (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    w ∈ B.coord Z ↔ B.S.basis.equivFun.symm w ∈ Z := by
  unfold BlockDat.coord
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa using hf
  · intro h
    exact ⟨_, h, B.S.basis.equivFun.apply_symm_apply w⟩

theorem range_cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    (∃ y, cv B ℓ Z y = w) ↔ w ∈ B.coord Z ∧ w ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
      rw [← hs]
      exact ⟨y, rfl⟩
    exact ⟨hy, ⟨_, rfl⟩⟩
  · rintro ⟨hZ, u, rfl⟩
    have hu : u ∈ B.Z0 ℓ Z := hZ
    rw [← hs] at hu
    obtain ⟨y, rfl⟩ := hu
    exact ⟨y, rfl⟩

theorem range_vE_bot (X : Finset (G → K)) :
    LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin = LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X (⊥ : Subgroup G) 1))).2
  have hb : goodAt X (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = idemOf X := by
    unfold goodAt
    rw [level_idempotent_bot K G, mul_one]
  rw [← hb]
  exact h

theorem range_vE_le (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin ≤ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
  rw [range_vE_bot]
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X P ψ))).2
  change LinearMap.range (imE (B.S.gaMat B.r (goodAt X P ψ))).mulVecLin ≤ _
  rw [h]
  unfold goodAt
  rw [(group_action_matrix_hom K B.S G B.r).2, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem range_vE_lvl (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin ⊓ B.S.lvlPart B.r P ψ :=
  good_part_spec K B.S G B.r X hX P ψ

theorem toF_sub (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms)
    (x : Fin (B.dZ ⟨X, P, ψ⟩ Z) → K) :
    ∃ y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K, B.toF ⟨X, ⊥, 1⟩ Z y = B.toF ⟨X, P, ψ⟩ Z x := by
  obtain ⟨hZ, hV⟩ := (range_cv B ⟨X, P, ψ⟩ Z _).1 ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).2 ⟨hZ, range_vE_le B X P ψ hV⟩
  exact ⟨y, by rw [toF_eq, toF_eq, hy]⟩

theorem actMat_coord (g : G) (w : Fin B.S.dim → K) :
    (B.S.actMat B.r g).mulVec w = B.S.basis.equivFun (B.r g (B.S.basis.equivFun.symm w)) := by
  have h := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm w)
  have hx : (B.S.basis.repr (B.S.basis.equivFun.symm w) : Fin B.S.dim → K) = w := by
    rw [← Basis.equivFun_apply]
    exact B.S.basis.equivFun.apply_symm_apply w
  rw [hx] at h
  unfold CSD.actMat
  rw [h, Basis.equivFun_apply]

theorem coord_act (Z : Submodule K B.S.Forms) (g : G) (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (w : Fin B.S.dim → K)
    (hw : w ∈ B.coord Z) : (B.S.actMat B.r g).mulVec w ∈ B.coord Z := by
  rw [mem_coord] at hw ⊢
  rw [actMat_coord, LinearEquiv.symm_apply_apply]
  exact hZ _ hw

theorem gaMat_single (g : G) : B.S.gaMat B.r (MonoidAlgebra.single g 1) = B.S.actMat B.r g := by
  rw [CSD.gaMat_eq_lift, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem comm_idem (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (a : MonoidAlgebra K G) :
    B.S.gaMat B.r a * B.S.gaMat B.r (idemOf X) = B.S.gaMat B.r (idemOf X) * B.S.gaMat B.r a := by
  have hm := (group_action_matrix_hom K B.S G B.r).2
  rw [← hm, ← hm, (idempotent_central K G X hX).2 a]

theorem toF_act (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (g : G)
    (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (x : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    ∃ y, B.toF ⟨X, ⊥, 1⟩ Z y = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) := by
  obtain ⟨hZx, hV⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨x, rfl⟩
  rw [range_vE_bot] at hV
  obtain ⟨w, hw⟩ := hV
  have h1 : (B.S.actMat B.r g).mulVec (cv B ⟨X, ⊥, 1⟩ Z x) ∈ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
    rw [range_vE_bot]
    refine ⟨(B.S.actMat B.r g).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hw ⊢
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← gaMat_single, comm_idem B X hX]
  obtain ⟨y, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).2 ⟨coord_act B Z g hZ _ hZx, h1⟩
  refine ⟨y, ?_⟩
  rw [toF_eq, toF_eq, hy, actMat_coord, LinearEquiv.symm_apply_apply]

end Block

section Rel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases h : i = k <;> simp [cpt, h]

theorem relK (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (g : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hg : ∀ x : Fin n → K, ∃ y : Fin D → K, f (cpt σ y) = g (cpt σ x)) :
    IsRat σ (relMat f g) ∧ ∀ x : Fin n → K, f (cpt σ ((kMat σ (relMat f g)).mulVec x)) = g (cpt σ x) := by
  have hk : ∀ k, g (Pi.single k 1) ∈ LinearMap.range f := fun k => by
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    exact ⟨_, hy⟩
  have hrat : IsRat σ (relMat f g) := by
    intro i k
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    have hs : solve f (g (Pi.single k 1)) = cpt σ y := hf (by rw [solve_spec f (hk k), hy])
    exact ⟨y i, by simp only [relMat, Matrix.of_apply, hs, cpt]⟩
  refine ⟨hrat, fun x => ?_⟩
  rw [cpt_mulVec, kMat_map σ hrat, relMat_spec f g hk]

theorem iC_cpt {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, CxData.iC, lin_apply, cpt]

theorem key_row' {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (hr : ∀ t, LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b Bs.μ0)) (hq : X.RATmu cr b)
    (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec x)) = X.iC cr b t (cpt Bs.v0.embedding x) := by
  rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hq t)]
  refine relMat_spec _ _ (fun k => ?_) _
  rw [← hr t]
  exact ⟨_, rfl⟩

end Rel

theorem mat_ext {K : Type} [Field K] {n k : ℕ} (M N : Matrix (Fin n) (Fin k) K) (h : ∀ x, M.mulVec x = N.mulVec x) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa only [Matrix.toLin'_apply] using h x)

section Block2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

theorem cv_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    cv B ℓ Z y = (B.vE ℓ * B.zE ℓ Z).mulVec y := by
  simp only [cv, Matrix.mulVec_mulVec]

theorem cv_of_toF {ℓ ℓ' : Lvl K G} {Z : Submodule K B.S.Forms} {x : Fin (B.dZ ℓ Z) → K} {y : Fin (B.dZ ℓ' Z) → K}
    (h : B.toF ℓ Z x = B.toF ℓ' Z y) : cv B ℓ Z x = cv B ℓ' Z y :=
  B.S.basis.equivFun.symm.injective h

theorem range_eq_block (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms)
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, cv B ⟨X, ⊥, 1⟩ Z (J.mulVec x) = cv B ⟨X, P, ψ⟩ Z x)
    (Ep : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hE : ∀ y, cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) =
      (B.S.gaMat B.r (lvlIdem P ψ)).mulVec (cv B ⟨X, ⊥, 1⟩ Z y)) :
    LinearMap.range J.mulVecLin = LinearMap.range Ep.mulVecLin := by
  have hinj := cv_injective B ⟨X, ⊥, 1⟩ Z
  have hlvl := range_vE_lvl B X hX P ψ
  ext z
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨J.mulVec x, hinj ?_⟩
    rw [hE, hJ]
    have hx : cv B ⟨X, P, ψ⟩ Z x ∈ B.S.lvlPart B.r P ψ := by
      have := ((range_cv B ⟨X, P, ψ⟩ Z _).1 ⟨x, rfl⟩).2
      rw [hlvl, Submodule.mem_inf] at this
      exact this.2
    exact B.S.lvlIdem_mulVec_of_mem B.r P ψ _ hx
  · rintro ⟨y, rfl⟩
    obtain ⟨hZ, -⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨Ep.mulVec y, rfl⟩
    have hV : cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) ∈ LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin := by
      rw [hlvl, hE, Submodule.mem_inf]
      obtain ⟨-, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨y, rfl⟩
      rw [range_vE_bot] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨⟨(B.S.gaMat B.r (lvlIdem P ψ)).mulVec u, ?_⟩, ?_⟩
      · simp only [Matrix.mulVecLin_apply] at hu ⊢
        rw [← hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, comm_idem B X hX]
      · rw [← level_part_spec K B.S G B.r P ψ]
        exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := (range_cv B ⟨X, P, ψ⟩ Z _).2 ⟨hZ, hV⟩
    exact ⟨x, hinj (by rw [hJ, hx])⟩

theorem cv_typeProj (X : Finset (G → K)) (Z : Submodule K B.S.Forms)
    (ρ : G → Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hρ : ∀ g x, cv B ⟨X, ⊥, 1⟩ Z ((ρ g).mulVec x) = (B.S.actMat B.r g).mulVec (cv B ⟨X, ⊥, 1⟩ Z x))
    (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    haveI : Fintype P := Fintype.ofFinite P
    cv B ⟨X, ⊥, 1⟩ Z ((((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • ρ (h : G)).mulVec y) =
      (B.S.gaMat B.r (lvlIdem P ψ)).mulVec (cv B ⟨X, ⊥, 1⟩ Z y) := by
  classical
  have hC : ∀ g : G, B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z * ρ g =
      B.S.actMat B.r g * (B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z) := fun g =>
    mat_ext _ _ fun x => by
      have := hρ g x
      rw [cv_eq, cv_eq] at this
      rw [← Matrix.mulVec_mulVec (M := B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z) (N := ρ g), this, Matrix.mulVec_mulVec]
  rw [cv_eq, cv_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_sum, CSD.gaMat_lvlIdem, Matrix.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => @Finset.mem_univ _ (Fintype.ofFinite P) x) fun h _ => ?_
  simp only [Matrix.mul_smul, hC, Matrix.smul_mul, smul_smul, map_inv]

end Block2

section Lev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem sub_lvl (b : Bool) (t : I.A.fam.base.Tup)
    (x : Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t) → K) :
    ∃ y, I.cg.toR I.X.zs false t y = I.cr.toR I.X.zs b t x := by
  cases b
  · exact toF_sub (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x
  · exact toF_sub (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x

theorem jt_spec (h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)) (b : Bool) (t : I.A.fam.base.Tup) :
    (∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x)) ∧
    ∀ x, I.cg.toR I.X.zs false t ((I.Jt b t).mulVec x) = I.cr.toR I.X.zs b t x := by
  have hinj : Function.Injective (I.X.iC I.cg false t) := (h2g.2 t).1
  have h1 : ∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x) :=
    (relK _ (I.X.iC I.cg false t) (I.X.iC I.cr b t) hinj fun x => by
      obtain ⟨y, hy⟩ := sub_lvl I b t x
      exact ⟨y, by rw [iC_cpt, iC_cpt, hy]⟩).2
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨y, hy⟩ := sub_lvl I b t x
  have e : (I.Jt b t).mulVec x = y := by
    apply cpt_injective I.A.fam.base.v0.embedding
    apply hinj
    rw [h1, iC_cpt, iC_cpt, hy]
  rw [e, hy]

theorem rho_y {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    ∃ y : Fin I.Sg.D → K, I.cg.toR I.X.zs false I.A.fam.base.μ0 y =
      (I.A.fam.R I.A.fam.base.μ0).r g (I.cg.toR I.X.zs false I.A.fam.base.μ0 x) := by
  have hZ : ∀ f ∈ I.X.zs.Z I.A.fam.base.μ0, (I.A.fam.R I.A.fam.base.μ0).r g f ∈ I.X.zs.Z I.A.fam.base.μ0 :=
    fun f hf => H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)
  exact toF_act (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr (I.X.zs.Z I.A.fam.base.μ0) g hZ x

theorem iCg_of_y {s : ℕ} (H : I.Hyp s) (g : G) (x y : Fin I.Sg.D → K)
    (hy : I.cg.toR I.X.zs false I.A.fam.base.μ0 y =
      (I.A.fam.R I.A.fam.base.μ0).r g (I.cg.toR I.X.zs false I.A.fam.base.μ0 x)) :
    I.iCg (cpt I.A.fam.base.v0.embedding y) = I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x)) :=
  (iC_cpt I.X I.cg false _ y).trans ((congrArg (fun f => I.X.Θ I.A.fam.base.μ0 (I.X.jR I.A.fam.base.μ0 f)) hy).trans
    ((H.gequiv _ g _).trans (congrArg (I.gE g) (iC_cpt I.X I.cg false _ x).symm)))

theorem rho_spec {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g).mulVec x)) =
      I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x)) :=
  (relK _ I.iCg ((I.gE g).comp I.iCg) H.h2g.1 fun x => by
    obtain ⟨y, hy⟩ := rho_y I H g x
    exact ⟨y, iCg_of_y I H g x y hy⟩).2 x

theorem rho_cv {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) ((I.ρf g).mulVec x) =
      ((I.A.fam.R I.A.fam.base.μ0).S.actMat (I.A.fam.R I.A.fam.base.μ0).r g).mulVec
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) x) := by
  obtain ⟨y, hy⟩ := rho_y I H g x
  have e : (I.ρf g).mulVec x = y :=
    cpt_injective _ (H.h2g.1 ((rho_spec I H g x).trans (iCg_of_y I H g x y hy).symm))
  rw [e, actMat_coord]
  have hy' : (I.A.fam.R I.A.fam.base.μ0).S.basis.equivFun.symm
      (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) y) =
      (I.A.fam.R I.A.fam.base.μ0).r g ((I.A.fam.R I.A.fam.base.μ0).S.basis.equivFun.symm
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) x)) := hy
  rw [← hy', LinearEquiv.apply_symm_apply]

theorem cv_epM {s : ℕ} (H : I.Hyp s) (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) ((I.epM P ψ).mulVec y) =
      ((I.A.fam.R I.A.fam.base.μ0).S.gaMat (I.A.fam.R I.A.fam.base.μ0).r (lvlIdem P ψ)).mulVec
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) y) :=
  cv_typeProj (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X (I.X.zs.Z I.A.fam.base.μ0) I.ρf (rho_cv I H) P ψ y

end Lev

end PassRep

namespace In

open Formalism.IndefR.CxPass.PassRep

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem pJt : I.PJt := by
  intro s H b t
  obtain ⟨h1, h2⟩ := jt_spec I H.h2g b t
  refine ⟨h1, h2, fun x => ?_⟩
  apply cpt_injective I.A.fam.base.v0.embedding
  apply H.h2g.1
  exact ((jt_spec I H.h2g b I.A.fam.base.μ0).1 _).trans
    ((CxData.key_row I.X I.cr b (H.h2 b) (H.ratMu b) t x).trans
      ((h1 x).symm.trans (key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).symm))

theorem pRho : I.PRho := by
  intro s H
  have hinj : ∀ y y' : Fin I.Sg.D → K, I.iCg (cpt I.A.fam.base.v0.embedding y) =
      I.iCg (cpt I.A.fam.base.v0.embedding y') → y = y' :=
    fun y y' h => cpt_injective _ (H.h2g.1 h)
  refine ⟨mat_ext _ _ fun x => hinj _ _ ?_, fun g h => mat_ext _ _ fun x => hinj _ _ ?_, rho_spec I H⟩
  · exact (rho_spec I H 1 x).trans (by rw [Matrix.one_mulVec, map_one]; rfl)
  · calc I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf (g * h)).mulVec x))
        = I.gE (g * h) (I.iCg (cpt I.A.fam.base.v0.embedding x)) := rho_spec I H (g * h) x
      _ = I.gE g (I.gE h (I.iCg (cpt I.A.fam.base.v0.embedding x))) := by rw [map_mul]; rfl
      _ = I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf h).mulVec x))) :=
          congrArg (I.gE g) (rho_spec I H h x).symm
      _ = I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g).mulVec ((I.ρf h).mulVec x))) :=
          (rho_spec I H g _).symm
      _ = I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g * I.ρf h).mulVec x)) := by rw [Matrix.mulVec_mulVec]

theorem pJ : I.PJ := by
  intro s H b
  have h := (jt_spec I H.h2g b I.A.fam.base.μ0).1
  refine ⟨fun x => h x, fun x y hxy => ?_⟩
  apply cpt_injective I.A.fam.base.v0.embedding
  apply (H.h2 b).1
  exact (h x).symm.trans ((congrArg (fun v : Fin I.Sg.D → K => I.iCg (cpt I.A.fam.base.v0.embedding v)) hxy).trans (h y))

theorem pRange : I.PRange := by
  intro s H b
  cases b
  · exact range_eq_block (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.base.μ0)
      (I.Jm false) (fun x => cv_of_toF _ ((jt_spec I H.h2g false I.A.fam.base.μ0).2 x))
      (I.epM I.P0 I.ψ0) (cv_epM I H I.P0 I.ψ0)
  · exact range_eq_block (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.base.μ0)
      (I.Jm true) (fun x => cv_of_toF _ ((jt_spec I H.h2g true I.A.fam.base.μ0).2 x))
      (I.epM I.P1 I.ψ1) (cv_epM I H I.P1 I.ψ1)

end In

end Formalism.IndefR.CxPass
