import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocksStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Red

section Conj

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def conjHom (X : Matrix m n R) (Y : Matrix n m R) (hXY : X * Y = 1) (hYX : Y * X = 1) : GL n R →* GL m R where
  toFun A := ⟨X * (A : Matrix n n R) * Y, X * ((A⁻¹ : GL n R) : Matrix n n R) * Y, by
      have hA : (A : Matrix n n R) * ((A⁻¹ : GL n R) : Matrix n n R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul, ← Matrix.mul_assoc (A : Matrix n n R), hA, Matrix.one_mul, hXY], by
      have hA : ((A⁻¹ : GL n R) : Matrix n n R) * (A : Matrix n n R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul, ← Matrix.mul_assoc ((A⁻¹ : GL n R) : Matrix n n R), hA,
        Matrix.one_mul, hXY]⟩
  map_one' := by
    ext1
    simp only [Units.val_one, Matrix.mul_one, hXY]
  map_mul' A B := by
    ext1
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul]

theorem conjHom_val (X : Matrix m n R) (Y : Matrix n m R) (hXY : X * Y = 1) (hYX : Y * X = 1) (A : GL n R) :
    ((conjHom X Y hXY hYX A : GL m R) : Matrix m m R) = X * (A : Matrix n n R) * Y := rfl

end Conj

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Transport

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {K : FinExt l} {r : ℕ}

def RatM (r : ℕ) {a b : Type} (X : Matrix a b ↥(MaximalUnramifiedExtension l)) : Prop := ∀ i j, fr l r (X i j) = X i j

theorem map_fr {a b : Type} {X : Matrix a b ↥(MaximalUnramifiedExtension l)} (h : RatM r X) : X.map (fr l r) = X := by
  exact Matrix.ext fun i j => h i j

variable (X : Matrix m n ↥(MaximalUnramifiedExtension l)) (Y : Matrix n m ↥(MaximalUnramifiedExtension l)) (hXY : X * Y = 1) (hYX : Y * X = 1)
  (hX : RatM r X) (hY : RatM r Y) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ' : ↥(GK K) →* GL m ↥(MaximalUnramifiedExtension l))
  (h : ∀ g, (ρ' g : Matrix m m ↥(MaximalUnramifiedExtension l)) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y)

include hX hY h in
theorem isRat_of (hρ : IsRat r ρ) : IsRat r ρ' where
  pos := hρ.pos
  le := hρ.le
  rat g i j := by
    have hρg : (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) = ρ g := Matrix.ext fun a b => hρ.rat g a b
    have e : (X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y).map (fr l r) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y := by
      rw [Matrix.map_mul, Matrix.map_mul, map_fr hX, map_fr hY, hρg]
    rw [h g]
    exact congrFun (congrFun e i) j
  cont i j := by
    have e : (fun g => (((ρ' g : Matrix m m ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, ∑ k', ((X i k' : ↥(MaximalUnramifiedExtension l)) : Om l) * (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k' k : ↥(MaximalUnramifiedExtension l)) : Om l) *
          ((Y k j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [h g]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      change algebraMap ↥(MaximalUnramifiedExtension l) (Om l) _ = _
      simp only [map_sum, map_mul]
      rfl
    rw [e]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun k' _ => ?_
    exact (continuous_const.mul (hρ.cont k' k)).mul continuous_const

include hXY hYX hX hY h in
theorem deRham_of_conjugate_unramified_rational (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1) (hρ : AdmDR P ρ) : AdmDR P ρ' := by
  intro k
  obtain ⟨Q, hQ⟩ := hρ k
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l k)
  have hf : ∀ {a b : Type} (M : Matrix a b ↥(MaximalUnramifiedExtension l)), M.map (fun c => kd P (fr l k c)) = M.map f := fun _ => rfl
  have h1 : X.map f * Y.map f = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero f) (map_one f)]
  have h2 : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero f) (map_one f)]
  have hfix : ∀ g : ↥(GK K), (X.map f).map (P.actQdR (g : GQ l)) = X.map f := fun g =>
    Matrix.ext fun i j => act_kd P g (hle _ (fr_comm (hX i j) k))
  have hfixY : ∀ g : ↥(GK K), (Y.map f).map (P.actQdR (g : GQ l)) = Y.map f := fun g =>
    Matrix.ext fun i j => act_kd P g (hle _ (fr_comm (hY i j) k))
  refine ⟨conjHom (X.map f) (Y.map f) h1 h2 Q, fun g => ?_⟩
  have hm : matD P ρ' k g = X.map f * matD P ρ k g * Y.map f := by
    rw [matD, hf, h g, Matrix.map_mul, Matrix.map_mul, matD, hf]
  rw [conjHom_val, hm, Matrix.map_mul, Matrix.map_mul, hfix, hfixY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Y.map f) (X.map f), h2, Matrix.one_mul, ← Matrix.mul_assoc (matD P ρ k g), hQ]

include hXY hYX hX hY h in
theorem semistable_of_conjugate_unramified_rational (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1) (hρ : AdmSt P ρ) : AdmSt P ρ' := by
  obtain ⟨K', hK, Q, hQ⟩ := hρ
  let f : ↥(MaximalUnramifiedExtension l) →+* Bst P := ks P
  have h1 : X.map f * Y.map f = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero f) (map_one f)]
  have h2 : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero f) (map_one f)]
  have hfix : ∀ g : ↥(GK K'), (X.map f).map (actSt P (g : GQ l)) = X.map f := fun g =>
    Matrix.ext fun i j => act_ks P g (hK (hle _ (hX i j)))
  have hfixY : ∀ g : ↥(GK K'), (Y.map f).map (actSt P (g : GQ l)) = Y.map f := fun g =>
    Matrix.ext fun i j => act_ks P g (hK (hle _ (hY i j)))
  refine ⟨K', hK, conjHom (X.map f) (Y.map f) h1 h2 Q, fun g => ?_⟩
  rw [conjHom_val, h, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hfix, hfixY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Y.map f) (X.map f), h2, Matrix.one_mul, ← Matrix.mul_assoc (((ρ ⟨g, GK_le hK g.2⟩ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)), hQ g]

end Transport

section Blocks

variable {G : Type} [Group G] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {R : Type} [CommRing R]

theorem toBlocks₁₁_mul (A B : Matrix (a ⊕ b) (a ⊕ b) R) (hB : ∀ i j, B (Sum.inr i) (Sum.inl j) = 0) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hB]

theorem toBlocks₂₂_mul (A B : Matrix (a ⊕ b) (a ⊕ b) R) (hA : ∀ i j, A (Sum.inr i) (Sum.inl j) = 0) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, hA]

theorem toBlocks₁₁_one : (1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₂₂_one : (1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ = 1 := by
  ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]

variable (ρ : G →* GL (a ⊕ b) R) (hz : ∀ g i j, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) (Sum.inr i) (Sum.inl j) = 0)

include hz in
theorem blk_mul₁ (g h : G) : (ρ (g * h) : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ =
    (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ * (ρ h : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ := by
  rw [map_mul, Units.val_mul, toBlocks₁₁_mul _ _ (hz h)]

include hz in
theorem blk_mul₂ (g h : G) : (ρ (g * h) : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ =
    (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ * (ρ h : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ := by
  rw [map_mul, Units.val_mul, toBlocks₂₂_mul _ _ (hz g)]

def blk₁ : G →* GL a R where
  toFun g := ⟨(ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁, (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁,
    by rw [← blk_mul₁ ρ hz, mul_inv_cancel, map_one, Units.val_one, toBlocks₁₁_one],
    by rw [← blk_mul₁ ρ hz, inv_mul_cancel, map_one, Units.val_one, toBlocks₁₁_one]⟩
  map_one' := by
    ext1
    show (ρ 1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ = 1
    rw [map_one, Units.val_one, toBlocks₁₁_one]
  map_mul' g h := by
    ext1
    exact blk_mul₁ ρ hz g h

def blk₂ : G →* GL b R where
  toFun g := ⟨(ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂, (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂,
    by rw [← blk_mul₂ ρ hz, mul_inv_cancel, map_one, Units.val_one, toBlocks₂₂_one],
    by rw [← blk_mul₂ ρ hz, inv_mul_cancel, map_one, Units.val_one, toBlocks₂₂_one]⟩
  map_one' := by
    ext1
    show (ρ 1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ = 1
    rw [map_one, Units.val_one, toBlocks₂₂_one]
  map_mul' g h := by
    ext1
    exact blk_mul₂ ρ hz g h

theorem blk_form (g : G) : (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (blk₁ ρ hz g : Matrix a a R)
    ((ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₂) 0 (blk₂ ρ hz g : Matrix b b R) := by
  have h0 : (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₁ = 0 := Matrix.ext fun i j => hz g i j
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (ρ g : Matrix (a ⊕ b) (a ⊕ b) R), h0]
  rfl

end Blocks

section BlocksRat

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {K : FinExt l} {r : ℕ}
  (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l))
  (hz : ∀ g i j, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inl j) = 0)

theorem isRat_blk₁ (hρ : IsRat r ρ) : IsRat r (blk₁ ρ hz) where
  pos := hρ.pos
  le := hρ.le
  rat g i j := hρ.rat g _ _
  cont i j := hρ.cont _ _

theorem isRat_blk₂ (hρ : IsRat r ρ) : IsRat r (blk₂ ρ hz) where
  pos := hρ.pos
  le := hρ.le
  rat g i j := hρ.rat g _ _
  cont i j := hρ.cont _ _

end BlocksRat

theorem rat_inv {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} (p : GL n ↥(MaximalUnramifiedExtension l))
    (hp : ∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) :
    RatM r ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
  have hp' : (p : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) = p := Matrix.ext hp
  set M := ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) with hM
  have h1 : M * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← hp', hM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : M = ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
    calc M = M * ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l))) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = M * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := (mul_assoc _ _ _).symm
      _ = _ := by rw [h1, one_mul]
  intro i j
  exact congrFun (congrFun h2 i) j

theorem redStep : RedStep := by
  intro l _ P AI T n _ _ K r ρ hR hD hS IH
  obtain ⟨s, p, ⟨x, hx⟩, hs, hp, hz⟩ := hS
  obtain ⟨y, hy⟩ : ∃ y, y ∉ s := by
    by_contra hc
    exact hs (Finset.eq_univ_iff_forall.2 fun y => by_contra fun h => hc ⟨y, h⟩)
  let e : {i // i ∈ s} ⊕ {i // i ∉ s} ≃ n := Equiv.sumCompl (· ∈ s)
  let X : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) n ↥(MaximalUnramifiedExtension l) :=
    fun i j => ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) (e i) j
  let Y : Matrix n ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l) := fun i j => (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i (e j)
  have hXY : X * Y = 1 := by
    ext i j
    have h1 : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrFun (congrFun h1 (e i)) (e j)
    rw [Matrix.mul_apply] at h2
    rw [Matrix.mul_apply]
    simp only [X, Y]
    rw [h2]
    simp only [Matrix.one_apply, e.injective.eq_iff]
  have hYX : Y * X = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [X, Y]
    rw [Equiv.sum_comp e (fun k => (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i k * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) k j),
      ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX : RatM r X := fun i j => rat_inv p hp (e i) j
  have hY : RatM r Y := fun i j => hp i (e j)
  let ρ' := (conjHom X Y hXY hYX).comp ρ
  have h : ∀ g, (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y := fun g => rfl
  have h' : ∀ g, (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) = Y * (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) * X := fun g => by
    rw [h g]
    simp only [Matrix.mul_assoc]
    rw [hYX, Matrix.mul_one, ← Matrix.mul_assoc Y X, hYX, Matrix.one_mul]
  have hR' : IsRat r ρ' := isRat_of (X := X) (Y := Y) hX hY ρ ρ' h hR
  have hD' : AdmDR P ρ' := deRham_of_conjugate_unramified_rational P X Y hXY hYX hX hY ρ ρ' h hR.le hD
  have hz' : ∀ g i j, (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inl j) = 0 := fun g i j =>
    hz g i.1 j.1 i.2 j.2
  have hform := blk_form ρ' hz'
  have hsub := GlobalTheory.T.deRham_blockTriangular_diagonal_blocks l P AI T _ _ K r ρ' (blk₁ ρ' hz') (blk₂ ρ' hz') _ hR' hform hD'
  have hS1 : AdmSt P (blk₁ ρ' hz') :=
    IH _ (Fintype.card_subtype_lt (x := y) hy) _ (isRat_blk₁ ρ' hz' hR') hsub.1
  have hS2 : AdmSt P (blk₂ ρ' hz') :=
    IH _ (Fintype.card_subtype_lt (p := fun i => i ∉ s) (x := x) (not_not.2 hx)) _ (isRat_blk₂ ρ' hz' hR') hsub.2
  have hS' := GlobalTheory.T.deRhamExtension_potentiallySemistable l P AI T _ _ K r ρ' (blk₁ ρ' hz') (blk₂ ρ' hz') _ hR' hform hD' hS1 hS2
  exact semistable_of_conjugate_unramified_rational P Y X hYX hXY hY hX ρ' ρ h' hR.le hS'

end GlobalTheory.PMon.Red

end
