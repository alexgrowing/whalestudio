import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCentral

theorem exists_unitary {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x)
    (e a b : A) (he : e * e = e) (hc : e * σ e = 0) (hab : a * b = 1) :
    ∃ u : A, u * σ u = 1 ∧ (e + σ e) * (u - 1) = u - 1 ∧ e * u = e * a := by
  have he' : σ e * σ e = σ e := by rw [← map_mul, he]
  have hab' : σ a * σ b = 1 := by rw [← map_mul, hab, map_one]
  refine ⟨e * a + σ e * σ b + (1 - e - σ e), ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_sub, map_one, hσ]
    linear_combination (a * b - a - b + 1) * he + (σ a * σ b - σ a - σ b + 1) * he' +
      (a * σ a + b * σ b - a - b - σ a - σ b + 2) * hc + e * hab + σ e * hab'
  · linear_combination (a - 1) * he + (σ b - 1) * he' + (a + σ b - 2) * hc
  · linear_combination (a - 1) * he + (σ b - 1) * hc

theorem exists_scalar {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (u : A) (hu : u * σ u = 1) :
    ∃ z : Formalism.UG.UJ σ J, ((z : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = u • (1 : Matrix (Fin n) (Fin n) A) := by
  have hu' : σ u * u = 1 := by rw [mul_comm, hu]
  refine ⟨⟨⟨u • 1, σ u • 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · simp [smul_smul, hu, hu']
  · simp [smul_smul, hu, hu']
  · show Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) * J * (u • (1 : Matrix (Fin n) (Fin n) A)) = J
    have : Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) = σ u • (1 : Matrix (Fin n) (Fin n) A) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT]
      · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
    rw [this]
    simp [smul_smul, hu, hu']

theorem supp_scalar {A : Type} [CommRing A] {n : ℕ} (f u : A) (h : f * (u - 1) = u - 1) (i j : Fin n) :
    f * (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j = (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j := by
  by_cases hij : i = j
  · subst hij; simpa using h
  · simp [hij]

theorem scalar_comm {A : Type} [CommRing A] {n : ℕ} (u : A) (M : Matrix (Fin n) (Fin n) A) :
    (u • (1 : Matrix (Fin n) (Fin n) A)) * M = M * (u • (1 : Matrix (Fin n) (Fin n) A)) := by
  simp

theorem map_mul_scalar {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n : ℕ} (u : A)
    (M : Matrix (Fin n) (Fin n) A) :
    (M * (u • (1 : Matrix (Fin n) (Fin n) A))).map φ = φ u • M.map φ := by
  ext i j
  simp

theorem cA_cA (D : D7) (x : Formalism.L2.Theta.AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have : D.sp.cm.sig (D.sp.cm.sig b) = b := star_star b
    simp [cA, sigR, this]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mulVec_shift {R : Type} [CommRing R] {n : ℕ} (B M : Matrix (Fin n) (Fin n) R) (e u p : R)
    (h : e * u = e * p) (c c' z y : Fin n → R) (hc : ∀ i, c' i = p * c i)
    (hy : (fun a => e * M.mulVec y a) = fun a => e * B.mulVec (fun i => c i * z i) a) :
    (fun a => e * (u • M).mulVec y a) = fun a => e * B.mulVec (fun i => c' i * z i) a := by
  funext a
  have h1 := congrFun hy a
  have h2 : (fun i => c' i * z i) = p • (fun i => c i * z i) := by
    funext i; simp [hc, mul_assoc]
  rw [h2, Matrix.mulVec_smul, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
  linear_combination (M.mulVec y a) * h + p * h1

theorem hmul {D : D7} {V : HSp D} (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem hinj {D : D7} {V : HSp D} (g h : GA D V) (hh : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) :
    g = h := Subtype.ext (Units.ext hh)

theorem hfin {D : D7} {V : HSp D} (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (Formalism.L2.Theta.mt V g).map (finPart D) := rfl

theorem exists_mt {D : D7} (V : HSp D) (u : Formalism.L2.Theta.AE D) (hu : u * cA D u = 1) :
    ∃ ζ : GA D V, Formalism.L2.Theta.mt V ζ =
      u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  exists_scalar (cA D) (JR (AF D.host.F) V.gram) u hu

theorem shift_pow {D : D7} (ϖ : D.host.E) (hϖ : ϖ ≠ 0) (d : List ℤ) (i : ℕ) (hi : i < d.length) :
    finPart D (incA D (ϖ ^ ((d.map (· + 1)).getD i 0))) =
      finPart D (incA D ϖ) * finPart D (incA D (ϖ ^ (d.getD i 0))) := by
  have : (d.map (· + 1)).getD i 0 = d.getD i 0 + 1 := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [this, zpow_add_one₀ hϖ, map_mul, map_mul, mul_comm]

theorem finMat_scalar {D : D7} {V : HSp D} (α ζ : GA D V) (u : Formalism.L2.Theta.AE D)
    (hmt : Formalism.L2.Theta.mt V ζ = u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D))) :
    finMat D.sp.cm.sig V.gram (α * ζ : GA D V) = finPart D u • finMat D.sp.cm.sig V.gram α := by
  rw [hfin, hfin, hmul, hmt]
  exact map_mul_scalar _ _ _

theorem central : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E), IsSplitIdem D e → ϖ ≠ 0 → ∃ ζ : GA D V, SuppAt e V ζ ∧ (∀ g, Commute ζ g) ∧ ∀ (d : List ℤ) (α : GA D V), DivAt V e ϖ d α → DivAt V e ϖ (d.map (· + 1)) (α * ζ) := by
  intro D V e ϖ he hϖ
  obtain ⟨u, hu, hs, hue⟩ := exists_unitary (cA D) (cA_cA D) e (incA D ϖ) (incA D ϖ⁻¹) he.1 he.2.1
    (by rw [← map_mul, mul_inv_cancel₀ hϖ, map_one])
  obtain ⟨ζ, hmt⟩ : ∃ ζ : GA D V, Formalism.L2.Theta.mt V ζ =
      u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
    exists_mt V u hu
  refine ⟨ζ, ?_, ?_, ?_⟩
  · intro i j
    rw [hmt]
    exact supp_scalar _ _ hs i j
  · intro g
    refine hinj (ζ * g) (g * ζ) ?_
    rw [hmul, hmul, hmt]
    exact scalar_comm _ _
  · rintro d α ⟨hd, B, h1, h2, h3, h4⟩
    have hF := finMat_scalar α ζ u hmt
    have hup : finPart D e * finPart D u = finPart D e * finPart D (incA D ϖ) := by
      rw [← map_mul, hue, map_mul]
    have hc : ∀ i : Fin V.rank, finPart D (incA D (ϖ ^ ((d.map (· + 1)).getD i.1 0))) =
        finPart D (incA D ϖ) * finPart D (incA D (ϖ ^ (d.getD i.1 0))) :=
      fun i => shift_pow ϖ hϖ d i.1 (lt_of_lt_of_eq i.2 hd.symm)
    refine ⟨by simpa using hd, B, h1, h2, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hyz⟩ := h3 y hy
      refine ⟨z, hz, ?_⟩
      rw [hF]
      exact mulVec_shift B _ _ _ _ hup _ _ z y hc hyz
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := h4 z hz
      refine ⟨y, hy, ?_⟩
      rw [hF]
      exact mulVec_shift B _ _ _ _ hup _ _ z y hc hyz

end GlobalTheory.SplitCentral
