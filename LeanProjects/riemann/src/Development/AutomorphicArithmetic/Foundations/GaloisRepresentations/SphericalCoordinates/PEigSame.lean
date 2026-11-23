import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.SameEigenvalues

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ}

private theorem toV_mul (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem toV_inv_cancel (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec]

private theorem same_symm {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) : GlobalTheory.LKCx.Same G v β x t hx Kf K' b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, inv_mem hk1, inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · rw [h1, map_inv, map_inv, ← Prod.inv_mk]
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b d : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) (h' : GlobalTheory.LKCx.Same G v β x t hx Kf K' b d) :
    GlobalTheory.LKCx.Same G v β x t hx Kf K' a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, mul_mem hk1 hk1', mul_mem hk2 hk2', mul_ne_zero hc' hc, ?_, ?_⟩
  · rw [h1', h1, map_mul, map_mul]
    simp only [← Prod.mk_mul_mk, _root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, toV_mul, smul_smul]

private theorem minpoly_conj {F C : Type} [Field F] [Ring C] [Algebra F C] (u : Cˣ) (x : C) :
    minpoly F ((u : C) * x * ((u⁻¹ : Cˣ) : C)) = minpoly F x := by
  let e : C ≃ₐ[F] C :=
    { toFun := fun w => (u : C) * w * ((u⁻¹ : Cˣ) : C)
      invFun := fun w => ((u⁻¹ : Cˣ) : C) * w * (u : C)
      left_inv := fun w => by simp [_root_.mul_assoc]
      right_inv := fun w => by simp [_root_.mul_assoc]
      map_mul' := fun w w' => by simp [_root_.mul_assoc]
      map_add' := fun w w' => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : C) * algebraMap F C r * ((u⁻¹ : Cˣ) : C) = algebraMap F C r
        rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] }
  exact minpoly.algEquiv_eq e x

private theorem posV_ne (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

private theorem eigL_eq {y : GlobalTheory.LKCx.grp G β} {z : Fin G.n → ℂ} {e : ℂ} (hz : z ≠ 0)
    (h : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z) :
    GlobalTheory.RootSumWeights.eigL G v β y z = e := by
  have hf : GlobalTheory.LKCx.FixL G v β y z := ⟨e, h⟩
  unfold GlobalTheory.RootSumWeights.eigL
  rw [dif_pos hf]
  have hs := hf.choose_spec
  exact smul_left_injective ℂ hz (hs.symm.trans h)

private theorem conj_eig (y₀ y : GlobalTheory.LKCx.grp G β) (c e : ℂ) (hc : c ≠ 0) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β (y₀ * y * y₀⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
                 (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) =
      e • (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ↔
    (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z := by
  rw [Matrix.mulVec_smul, toV_mul, toV_mul, toV_inv_cancel, smul_comm e c,
    ← Matrix.mulVec_smul _ e z]
  constructor
  · intro h
    have h' := smul_right_injective (Fin G.n → ℂ) hc h
    have h'' := congrArg (fun w => (GlobalTheory.LKCx.toV G v β y₀⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h'
    simpa only [toV_inv_cancel] using h''
  · intro h
    rw [h]

end UpperTheory.Gal.W2.SameEigenvalues

open UpperTheory.Gal.W2.SameEigenvalues in
theorem UpperTheory.Gal.W2.eigSame_of :
    UpperTheory.Gal.W2.EigSame := by
  intro p _ G v c B K S hS a a' hq
  have hE := Quot.eqvGen_exact hq
  have hsame := (Equivalence.eqvGen_iff ⟨fun _ => GlobalTheory.LKCx.same_refl _ _ _ _ _ _ _ _ _,
    fun h => same_symm h, fun h h' => same_trans h h'⟩).mp hE
  obtain ⟨y₀, k, d, hk1, hk2, hd, h1, h2⟩ := hsame
  refine ⟨(MulAut.conj y₀).toEquiv, by simp, fun y => ?_⟩
  have hA : a'.1.1 = B.toAf y₀ * a.1.1 * k.1 := congrArg Prod.fst h1
  have hP : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2 := congrArg Prod.snd h1
  have hV : a'.2.1 =
      d • ((GlobalTheory.LKCx.toV G v B.β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := h2
  have hFix : GlobalTheory.LKCx.FixL G v B.β (y₀ * y * y₀⁻¹) a'.2.1 ↔ GlobalTheory.LKCx.FixL G v B.β y a.2.1 := by
    unfold GlobalTheory.LKCx.FixL
    rw [hV]
    exact exists_congr fun e => conj_eig y₀ y d e hd a.2.1
  have hAf : a'.1.1⁻¹ * B.toAf (y₀ * y * y₀⁻¹) * a'.1.1 ∈ S ↔ a.1.1⁻¹ * B.toAf y * a.1.1 ∈ S := by
    rw [hA, map_mul, map_mul, map_inv]
    have : (B.toAf y₀ * a.1.1 * k.1)⁻¹ * (B.toAf y₀ * B.toAf y * (B.toAf y₀)⁻¹) *
        (B.toAf y₀ * a.1.1 * k.1) = k.1⁻¹ * (a.1.1⁻¹ * B.toAf y * a.1.1) * k.1 := by group
    rw [this]
    exact hS k.1 hk1 _
  have hP1 : a'.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β (y₀ * y * y₀⁻¹) * a'.1.2 ∈ KHT p G.m G.n 1 G.Fw ↔
      a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
    rw [hP, map_mul, map_mul, map_inv]
    have : (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2)⁻¹ *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * GlobalTheory.LKCx.toP1 G B.β y * (GlobalTheory.LKCx.toP1 G B.β y₀)⁻¹) *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2) =
        k.2⁻¹ * (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2) * k.2 := by group
    rw [this]
    constructor
    · intro hm
      have h3 := mul_mem (mul_mem hk2 hm) (inv_mem hk2)
      simpa [_root_.mul_assoc] using h3
    · intro hm
      exact mul_mem (mul_mem (inv_mem hk2) hm) hk2
  have hSees : Sees B S a' (y₀ * y * y₀⁻¹) ↔ Sees B S a y := and_congr hFix (and_congr hAf hP1)
  refine ⟨hSees.symm, fun hs => ⟨?_, ?_⟩⟩
  · show minpoly G.F (((y₀ * y * y₀⁻¹ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ).1 : G.C) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul]
    exact minpoly_conj _ _
  · obtain ⟨e, he⟩ := hs.1
    rw [eigL_eq (posV_ne a.2) he]
    apply eigL_eq (posV_ne a'.2)
    rw [hV]
    exact (conj_eig y₀ y d e hd a.2.1).mpr he
