import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInvariantHermitianFormSymmEqSmulTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefEqMulTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionFormulaAndDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticFixingIWithDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelDensityInvariantAffineStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvHermSiegel

theorem sesq_polar {W : Type*} [AddCommGroup W] [Module ℂ W] (B : W → W → ℂ)
    (hl : ∀ (a : ℂ) v v' w, B (a • v + v') w = a * B v w + B v' w)
    (hh : ∀ v w, B w v = star (B v w)) (x y : W) :
    B x y = (B (x + y) (x + y) + Complex.I * B (x + Complex.I • y) (x + Complex.I • y)
      - (1 + Complex.I) * (B x x + B y y)) / 2 := by
  have a0 : ∀ w, B 0 w = 0 := fun w => by
    have := hl 1 0 0 w
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have a1 : ∀ v v' w, B (v + v') w = B v w + B v' w := fun v v' w => by
    simpa using hl 1 v v' w
  have a2 : ∀ (a : ℂ) v w, B (a • v) w = a * B v w := fun a v w => by
    simpa [a0] using hl a v 0 w
  have b1 : ∀ v v' w, B w (v + v') = B w v + B w v' := fun v v' w => by
    rw [hh, a1, star_add, ← hh, ← hh]
  have b2 : ∀ (a : ℂ) v w, B w (a • v) = star a * B w v := fun a v w => by
    rw [hh, a2, star_mul', ← hh]
  simp only [a1, b1, a2, b2]
  have hI : star Complex.I = -Complex.I := by simp [Complex.star_def]
  rw [hI]
  ring_nf
  simp only [show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring, Complex.I_sq]
  ring

theorem tauU_symPart {g : ℕ} {A : Matrix (Fin g) (Fin g) ℂ} (h : A.IsSymm) :
    tauU (symPart A) = A := by
  ext i j
  simp only [tauU, symPart, Matrix.of_apply]
  rw [h.apply i j]
  ring

theorem symPart_tauU {g : ℕ} (u : symMat g) : symPart (tauU u) = u := by
  apply Subtype.ext
  funext i j
  have hu : ∀ a b, u.1 a b = u.1 b a := u.2
  simp only [symPart, tauU, Matrix.of_apply]
  rw [hu j i]
  ring

theorem tauU_isSymm {g : ℕ} (u : symMat g) : (tauU u).IsSymm := by
  have hu : ∀ a b, u.1 a b = u.1 b a := u.2
  exact Matrix.IsSymm.ext fun i j => hu j i

theorem symPart_add_smul {g : ℕ} (a : ℂ) (Z Z' : Matrix (Fin g) (Fin g) ℂ) :
    symPart (a • Z + Z') = a • symPart Z + symPart Z' := by
  apply Subtype.ext
  funext i j
  simp only [symPart, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem isUnit_map {g : ℕ} {A : Matrix (Fin g) (Fin g) ℝ} (hA : IsUnit A) :
    IsUnit (A.map (fun t : ℝ => (t : ℂ))) :=
  hA.map (Complex.ofRealHom.mapMatrix (m := Fin g))

theorem map_mul_transpose {g : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) :
    (A * Aᵀ).map (fun t : ℝ => (t : ℂ)) = A.map (fun t : ℝ => (t : ℂ)) * (A.map (fun t : ℝ => (t : ℂ)))ᵀ := by
  rw [← Matrix.transpose_map]
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem tauU_i (g : ℕ) : tauU (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) = Complex.I • 1 :=
  tauU_symPart ((Matrix.isSymm_one).smul _)

theorem im_i (g : ℕ) : ((Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)).map fun t => (t.im : ℂ)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem i_mem (g : ℕ) : symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) ∈ siegel g := by
  show IsSiegel (tauU _)
  rw [tauU_i]
  refine ⟨(Matrix.isSymm_one).smul _, ?_⟩
  have : ((Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)).map Complex.im) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  rw [this]
  exact Matrix.PosDef.one

theorem sdens_i {g : ℕ} (Z : Matrix (Fin g) (Fin g) ℂ) (hZ : Z.IsSymm) :
    ((sdens (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) Z : ℝ) : ℂ) = (Z * Zᴴ).trace := by
  have hc : Zᴴ = Z.map star := by
    rw [Matrix.conjTranspose, hZ.eq]
  have hr : star ((Z * Zᴴ).trace) = (Z * Zᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  unfold sdens
  rw [im_i, inv_one, Matrix.one_mul, Matrix.mul_one, ← hc]
  exact Complex.conj_eq_iff_re.1 hr

theorem invHermFun_eq_const_and_smul_sdens : ∀ (g : ℕ) (F : symMat g → symMat g → Ext (1 + 1)), IsHermFun g F →
    (∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, IsInvFun F γ) → ∃ t l : ℝ, ∀ s ∈ siegel g, ∀ v : symMat g,
      F s v ∅ = t ∧ F s v Finset.univ = Complex.I * (l * sdens (tauU s) (tauU v) : ℝ) := by
  intro g F hF hinv
  set s₀ : symMat g := symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) with hs₀
  have hs₀m : s₀ ∈ siegel g := i_mem g
  obtain ⟨⟨t, ht⟩, B, hl, hh, hB⟩ := hF.2 s₀ hs₀m

  have hBinv : ∀ (k : Matrix.unitaryGroup (Fin g) ℂ) (x y : symMat g),
      B (symPart (k.1 * tauU x * k.1ᵀ)) (symPart (k.1 * tauU y * k.1ᵀ)) = B x y := by
    intro k x y
    obtain ⟨γ, hγ0, hD⟩ := GlobalTheory.T.exists_symplectic_fixing_i_with_derivative g k
    set D := fderiv ℂ (actB γ) s₀ with hDdef
    have hQ : ∀ z, B (D z) (D z) = B z z := by
      intro z
      have e := congrFun (hinv γ s₀ hs₀m z) Finset.univ
      rw [hγ0, hB, hB] at e
      exact mul_left_cancel₀ Complex.I_ne_zero e
    rw [← hD, ← hD, sesq_polar B hl hh (D x) (D y), sesq_polar B hl hh x y]
    have h1 : D x + D y = D (x + y) := (map_add D x y).symm
    have h2 : D x + Complex.I • D y = D (x + Complex.I • y) := by rw [map_add, map_smul]
    rw [h1, h2, hQ, hQ, hQ, hQ]
  obtain ⟨c, hc⟩ := GlobalTheory.unitary_invariant_hermitian_form_symm_eq_smul_trace g
    (fun Z W => B (symPart Z) (symPart W))
    (fun a Z Z' W => by simp only [symPart_add_smul]; exact hl _ _ _ _)
    (fun Z W => hh _ _)
    (fun k Z W hZ hW => by
      have := hBinv k (symPart Z) (symPart W)
      rwa [tauU_symPart hZ, tauU_symPart hW] at this)
  have hB2 : ∀ u : symMat g, B u u = ((c * sdens (tauU s₀) (tauU u) : ℝ) : ℂ) := by
    intro u
    have := hc (tauU u) (tauU u) (tauU_isSymm u) (tauU_isSymm u)
    simp only [symPart_tauU] at this
    rw [this, Complex.ofReal_mul, hs₀, tauU_i, sdens_i _ (tauU_isSymm u)]
  refine ⟨t, c, fun s hs v => ?_⟩
  obtain ⟨hsym, hpos⟩ := (hs : IsSiegel (tauU s))
  set Y := (tauU s).map Complex.im
  set X := (tauU s).map Complex.re
  have hX : X.IsSymm := by
    show ((tauU s).map Complex.re)ᵀ = _
    rw [← Matrix.transpose_map, hsym.eq]
  obtain ⟨A, hA, hAA⟩ := GlobalTheory.T.pos_def_eq_mul_transpose g Y hpos
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.siegel_action_formula_and_derivative g A X hA hX
  set A' := A.map (fun t : ℝ => (t : ℂ)) with hA'
  have hτ : A' * tauU s₀ * A'ᵀ + X.map (fun t : ℝ => (t : ℂ)) = tauU s := by
    rw [hs₀, tauU_i, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hA', ← map_mul_transpose, hAA]
    ext i j
    apply Complex.ext <;> simp [Y, X]
  have hγs : actB γ s₀ = s := by
    rw [(hγ s₀ 0).1, hτ, symPart_tauU]
  have hU : IsUnit A'.det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_map hA)
  set W := tauU v
  set P := A'⁻¹
  have hW : Wᵀ = W := (tauU_isSymm v).eq
  have hPW : (P * W * Pᵀ).IsSymm := by
    simp only [hW, Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, (tauU_isSymm v).eq,
      Matrix.mul_assoc]
  set u := symPart (P * W * Pᵀ)
  have hAu : A' * tauU u * A'ᵀ = W := by
    rw [tauU_symPart hPW]
    have e1 : A' * P = 1 := Matrix.mul_nonsing_inv _ hU
    have e2 : Pᵀ * A'ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]
  have hDu : fderiv ℂ (actB γ) s₀ u = v := by
    rw [(hγ s₀ u).2, hAu, symPart_tauU]
  have e := hinv γ s₀ hs₀m u
  rw [hγs, hDu] at e
  rw [e]
  refine ⟨ht u, ?_⟩
  have hsd : sdens (tauU s) W = sdens (tauU s₀) (tauU u) := by
    rw [← hτ, ← hAu]
    exact GlobalTheory.T.siegel_density_invariant_affine g A X _ _ hA
  rw [hB, hB2 u, hsd]

end GlobalTheory.InvHermSiegel
