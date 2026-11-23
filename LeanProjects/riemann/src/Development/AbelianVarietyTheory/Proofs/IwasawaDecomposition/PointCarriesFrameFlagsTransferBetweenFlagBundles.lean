import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.Transfer

variable {ι : Type} {m : ι → ℕ}

theorem inv_mul_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g⁻¹ * (g * X) = X := by
  rw [← mul_assoc, Mat.inv_mul hg, one_mul]

theorem mul_inv_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g * (g⁻¹ * X) = X := by
  rw [← mul_assoc, Mat.mul_inv hg, one_mul]

theorem det_mul_ne {K : Type} [Field K] {g g' : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (hg' : ∀ τ, (g' τ).det ≠ 0)
    (τ : ι) : ((g * g') τ).det ≠ 0 := by
  rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hg τ) (hg' τ)

theorem par_of_three {K : Type} [Field K] {k : ι → ℕ} {h h' P Q E L : Mat m K} (hP : ∀ τ, (P τ).det ≠ 0)
    (hQ : ∀ τ, (Q τ).det ≠ 0) (hE : ∀ τ, (E τ).det ≠ 0) (hL : Par k ⊤ L) (G1 : Par k ⊤ (h * P⁻¹))
    (G2 : Par k ⊤ (h' * (L * (P * E))⁻¹)) (G3 : Par k ⊤ (h' * (Q * E)⁻¹)) : Par k ⊤ (h * Q⁻¹) := by
  have hh' : ∀ τ, (h' τ).det ≠ 0 := fun τ => by
    have := G3.det_ne τ
    rw [Pi.mul_apply, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hLPE : ∀ τ, ((L * (P * E)) τ).det ≠ 0 := det_mul_ne hL.det_ne (det_mul_ne hP hE)
  have e : h * Q⁻¹ = h * P⁻¹ * L⁻¹ * (h' * (L * (P * E))⁻¹)⁻¹ * (h' * (Q * E)⁻¹) := by
    rw [Mat.mul_inv_rev h', Mat.inv_inv hLPE, Mat.mul_inv_rev Q E]
    simp only [mul_assoc]
    rw [inv_mul_cancel_left hh', mul_inv_cancel_left hE, inv_mul_cancel_left hL.det_ne,
      inv_mul_cancel_left hP]
  rw [e]
  exact ((G1.mul hL.inv).mul G2.inv).mul G3

variable {F : Type} [Field F]

theorem sp_specializes {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) (w : Sp K) :
    p w ⤳ p (IsLocalRing.closedPoint K) := by
  rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]

theorem val_map_mul {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k k' : ι → ℕ} {g g' : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g)
    (hg' : Par k' ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g') :
    (g * g').map ((ratOf Y).val p) = g.map ((ratOf Y).val p) * g'.map ((ratOf Y).val p) :=
  hg.map_mul_of hg' _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem val_map_par {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {g : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g) :
    Par k ⊤ (g.map ((ratOf Y).val p)) :=
  hg.map_of _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem frame_change {X Y : Var F} (ψ : X.Fn →ₐ[F] Y.Fn) (A B : Mat m X.Fn) (hA : ∀ τ, (A τ).det ≠ 0)
    : ∀ C : Mat m Y.Fn, C * (B.map ψ)⁻¹ = (C * (A.map ψ)⁻¹) * (A * B⁻¹).map ψ := by
  intro C
  have hA' : ∀ τ, ((A.map ψ) τ).det ≠ 0 := fun τ => by
    have e : (A.map ψ τ).det = ψ (A τ).det := Mat.det_map A ψ.toRingHom τ
    rw [e]; exact (map_ne_zero _).2 (hA τ)
  have e1 : (A * B⁻¹).map ψ = A.map ψ * B⁻¹.map ψ := Mat.map_mul A B⁻¹ ψ.toRingHom
  have e2 : B⁻¹.map ψ = (B.map ψ)⁻¹ := Mat.map_inv B ψ.toRingHom
  rw [e1, e2]
  show C * (B.map ψ)⁻¹ = C * (A.map ψ)⁻¹ * (A.map ψ * (B.map ψ)⁻¹)
  rw [mul_assoc, inv_mul_cancel_left hA']

theorem val_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {D : Mat m X.Fn}
    (hD : Par k ((ratOf X).O (f (p (IsLocalRing.closedPoint K)))).toSubring D) :
    (D.map ψ).map ((ratOf Y).val p) = D.map ((ratOf X).val (p ≫ f)) := by
  funext τ
  ext i j
  exact (hf.val_comp p (IsLocalRing.closedPoint K) ((hD τ).1 i j)).symm

theorem par_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {z : Y.X} {k : ι → ℕ} {D : Mat m X.Fn} (hD : Par k ((ratOf X).O (f z)).toSubring D) :
    Par k ((ratOf Y).O z).toSubring (D.map ψ) :=
  hD.map ψ.toRingHom fun _ hx => hf.map_mem_O hx

end GlobalTheory.FlagBundle.Transfer

namespace GlobalTheory.FlagBundle

open Transfer

theorem Bears.transfer : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ →
    ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ →
    ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)),
    ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ R₁ R₂ K _ p q hpq A hA B hB h h' b1 b2 b3
  obtain ⟨A₁, hA₁, G1⟩ := b1
  obtain ⟨A₁', hA₁', G2⟩ := b2
  obtain ⟨A₂, hA₂, G3⟩ := b3
  refine ⟨A₂, hA₂, ?_⟩
  have hx1 : f₁ (p (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := rfl
  have hx2 : f₂ (q (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := by rw [hpq]; rfl
  have hD : Par 0 ((ratOf X).O ((p ≫ f₁) (IsLocalRing.closedPoint K))).toSubring (A * B⁻¹) := (Fr.mem_iff hB).1 hA
  have hD1 : Par 0 ((ratOf X).O (f₁ (p (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx1 ▸ hD
  have hD2 : Par 0 ((ratOf X).O (f₂ (q (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx2 ▸ hD
  have C1 := R₁.2.1 _ A₁ hA₁ A (hx1 ▸ hA)
  have C1B := R₁.2.1 _ A₁ hA₁ B (hx1 ▸ hB)
  have C2 := R₂.2.1 _ A₂ hA₂ A (hx2 ▸ hA)
  have L1 := (Fr.mem_iff hA₁).1 hA₁'
  have e1 : A₁' * (B.map φ₁)⁻¹ = (A₁' * A₁⁻¹) * (A₁ * (B.map φ₁)⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left (Fr.det_ne hA₁)]
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  rw [e1, val_map_mul p L1 C1B, frame_change φ₁ A B hAd, val_map_mul p C1 (par_map_hom R₁.1 hD1),
    val_map_hom R₁.1 p hD1] at G2
  rw [frame_change φ₂ A B hAd, val_map_mul q C2 (par_map_hom R₂.1 hD2), val_map_hom R₂.1 q hD2] at G3
  have ev : (A * B⁻¹).map ((ratOf X).val (q ≫ f₂)) = (A * B⁻¹).map ((ratOf X).val (p ≫ f₁)) :=
    congrArg (fun y => (A * B⁻¹).map ((ratOf X).val y)) hpq.symm
  rw [ev] at G3
  have hE : Par 0 ⊤ ((A * B⁻¹).map ((ratOf X).val (p ≫ f₁))) := by
    rw [← val_map_hom R₁.1 p hD1]; exact val_map_par p (par_map_hom R₁.1 hD1)
  exact par_of_three (val_map_par p C1).det_ne (val_map_par q C2).det_ne hE.det_ne (val_map_par p L1) G1 G2 G3

end GlobalTheory.FlagBundle
