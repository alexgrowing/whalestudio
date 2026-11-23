import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.NatDegreeDefectGelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapSingleAtEmb
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent

noncomputable section

open NumberField GlobalTheory.CuspRep Polynomial Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.Bridge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_add' (φ ψ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : chart (φ + ψ) g x = chart φ g x + chart ψ g x := by
  unfold chart; split_ifs <;> simp

theorem chart_smul' (c : ℂ) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : chart (c • φ) g x = c • chart φ g x := by
  unfold chart; split_ifs <;> simp

theorem chart_zero' (g : GA E a) (x : Lie E a) : chart (0 : GA E a → ℂ) g x = 0 := by
  unfold chart; split_ifs <;> simp

theorem along_add (w : InfinitePlace E) (g : GA E a) (φ ψ : GA E a → ℂ) :
    along w g (φ + ψ) = along w g φ + along w g ψ := funext fun x => chart_add' φ ψ g _

theorem along_smul (w : InfinitePlace E) (g : GA E a) (c : ℂ) (φ : GA E a → ℂ) :
    along w g (c • φ) = c • along w g φ := funext fun x => chart_smul' c φ g _

theorem along_zero (w : InfinitePlace E) (g : GA E a) : along w g (0 : GA E a → ℂ) = 0 :=
  funext fun x => chart_zero' g _

theorem along_sum {ι : Type} (S : Finset ι) (w : InfinitePlace E) (g : GA E a) (φ : ι → GA E a → ℂ) :
    along w g (∑ i ∈ S, φ i) = ∑ i ∈ S, along w g (φ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [along_zero]
  | insert b S hb ih => rw [sum_insert hb, sum_insert hb, along_add, ih]

theorem atW_one (w : InfinitePlace E) : atW w (1 : Matrix (Fin a) (Fin a) ℂ) = oneL E a := by
  funext i j v
  by_cases h : v = w
  · subst h; simp [atW, Matrix.one_apply]; split_ifs <;> rfl
  · simp [atW, h, Matrix.one_apply]; split_ifs <;> rfl

theorem along_one (w : InfinitePlace E) (g : GA E a) (φ : GA E a → ℂ) : along w g φ 1 = φ g := by
  have h := chart_val φ g 1
  simp only [Units.val_one, map_one, mul_one] at h
  rw [along, atW_one]
  exact h

theorem atW_mul (w : InfinitePlace E) (x y : Matrix (Fin a) (Fin a) ℂ) :
    Matrix.of (atW w x) * Matrix.of (atW w y) = Matrix.of (atW w (x * y)) := by
  ext i j v
  rw [Matrix.mul_apply, Finset.sum_apply]
  by_cases h : v = w
  · simp [atW, h, Matrix.mul_apply]
  · simp [atW, h, Matrix.one_apply]

theorem isUnit_atW (w : InfinitePlace E) {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    atW w x ∈ invSet E a := by
  have hx' : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have h1 : Matrix.of (atW w x) * Matrix.of (atW w x⁻¹) = 1 := by
    rw [atW_mul, Matrix.mul_nonsing_inv _ hx', atW_one]; rfl
  have h2 : Matrix.of (atW w x⁻¹) * Matrix.of (atW w x) = 1 := by
    rw [atW_mul, Matrix.nonsing_inv_mul _ hx', atW_one]; rfl
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem atEmb_add (τ : E →+* ℂ) (z z' : ℂ) : atEmb τ (z + z') = atEmb τ z + atEmb τ z' := by
  rw [atEmb_eq τ (z + z'), atEmb_eq τ z, atEmb_eq τ z']
  simp only [Complex.add_re, Complex.add_im, add_smul]
  abel

theorem atEmb_smul (τ : E →+* ℂ) (r : ℝ) (z : ℂ) : atEmb τ (r • z) = r • atEmb τ z := by
  rw [atEmb_eq τ (r • z), atEmb_eq τ z]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, smul_add, smul_smul]

def linW (w : InfinitePlace E) : Matrix (Fin a) (Fin a) ℂ →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (x.map (atEmb w.embedding))
      map_add' := fun x y => by
        funext i j
        change atEmb w.embedding (x i j + y i j) = atEmb w.embedding (x i j) + atEmb w.embedding (y i j)
        exact atEmb_add _ _ _
      map_smul' := fun r x => by
        funext i j
        change atEmb w.embedding (r • x i j) = r • atEmb w.embedding (x i j)
        exact atEmb_smul _ _ _ }

theorem atW_eq (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) ℂ) :
    atW w x = linW w x + atW w 0 := by
  funext i j v
  change atW w x i j v = atEmb w.embedding (x i j) v + atW w 0 i j v
  rw [GlobalTheory.BCT.MuProps.atEmb_emb]
  by_cases h : v = w
  · subst h; simp [atW]
  · simp [atW, h]

theorem rd_along (w : InfinitePlace E) (g : GA E a) (φ : Sm E a) (X : Matrix (Fin a) (Fin a) ℂ)
    {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    PositivityTheory.RgBcC.Rd X (along w g φ.1) x = along w g (lieD (toL (X.map (atEmb w.embedding))) φ.1) x := by
  have hz := isUnit_atW w hx
  have hA : HasFDerivAt (atW w) (linW w) x := by
    have e : (atW w : Matrix (Fin a) (Fin a) ℂ → Lie E a) = fun y => linW w y + atW w 0 :=
      funext fun y => atW_eq w y
    rw [e]
    exact (linW w).hasFDerivAt.add_const _
  have hc : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (atW w x)) (atW w x) :=
    ((contDiffAt_chart φ.2 g hz).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasFDerivAt (along w g φ.1) ((fderiv ℝ (chart φ.1 g) (atW w x)).comp (linW w)) x := hc.comp x hA
  rw [PositivityTheory.RgBcC.Rd, hcomp.fderiv, along, chart_lieD φ.2 _ g hz]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  congr 1
  funext i j v
  change atEmb w.embedding ((x * X) i j) v =
    (Matrix.of (atW w x) * Matrix.of (toL (X.map (atEmb w.embedding)))) i j v
  by_cases h : v = w
  · subst h
    simp [atW, GlobalTheory.BCT.MuProps.atEmb_emb, Matrix.mul_apply, Finset.sum_apply]
  · simp [atW, GlobalTheory.BCT.MuProps.atEmb_emb, Matrix.mul_apply, Finset.sum_apply, h]

theorem rd_along' (w : InfinitePlace E) (g : GA E a) (φ : Sm E a) (i j : Fin a) (z : ℂ)
    {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    PositivityTheory.RgBcC.Rd (Matrix.single i j z) (along w g φ.1) x = along w g (lieS E a i j (atEmb w.embedding z) φ).1 x := by
  rw [rd_along w g φ _ hx, GlobalTheory.OneRep.map_single_atEmb, lieS_apply]
  rfl

theorem eu_along (w : InfinitePlace E) (g : GA E a) (s : Bool) (φ : Sm E a) (i j : Fin a)
    {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    PositivityTheory.RgBcC.Eu s i j (along w g φ.1) x = along w g (eopW w s i j φ).1 x := by
  have h1 := rd_along' w g φ i j 1 hx
  have h2 := rd_along' w g φ i j Complex.I hx
  have e1 : atEmb w.embedding 1 = GlobalTheory.CompanionTheory.CasFamily.eW w := rfl
  have e2 : atEmb w.embedding Complex.I = GlobalTheory.CompanionTheory.CasFamily.fW w := rfl
  rw [e1] at h1
  rw [e2] at h2
  cases s
  · have hE := GlobalTheory.CompanionTheory.CasFamily.Eop_conjugate (a := a) w i j
    simp only [PositivityTheory.RgBcC.Eu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2, eopW, hE, Bool.false_eq_true,
      if_false, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, along_smul,
      along_add]
  · have hE := GlobalTheory.CompanionTheory.CasFamily.Eop_embedding (a := a) w i j
    simp only [PositivityTheory.RgBcC.Eu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2, eopW, hE, if_true,
      LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, along_smul,
      Pi.sub_apply]
    have hsub : ∀ f f' : GA E a → ℂ, along w g (f - f') = along w g f - along w g f' := fun f f' => by
      rw [sub_eq_add_neg, along_add, ← neg_one_smul ℂ f', along_smul]; simp [sub_eq_add_neg]
    rw [hsub, along_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem isOpen_GLs : IsOpen (PositivityTheory.RgBcC.GLs a) := by
  have e : PositivityTheory.RgBcC.GLs a = (fun x : Matrix (Fin a) (Fin a) ℂ => x.det) ⁻¹' ({0}ᶜ : Set ℂ) := by
    ext x; simp [PositivityTheory.RgBcC.GLs]
  rw [e]
  exact (continuous_id.matrix_det).isOpen_preimage _ isOpen_compl_singleton

theorem rd_congr (X : Matrix (Fin a) (Fin a) ℂ) {F G : Matrix (Fin a) (Fin a) ℂ → ℂ} {x : Matrix (Fin a) (Fin a) ℂ}
    (h : F =ᶠ[nhds x] G) : PositivityTheory.RgBcC.Rd X F x = PositivityTheory.RgBcC.Rd X G x := by
  simp only [PositivityTheory.RgBcC.Rd, h.fderiv_eq]

theorem eu_congr (s : Bool) (i j : Fin a) {F G : Matrix (Fin a) (Fin a) ℂ → ℂ} {x : Matrix (Fin a) (Fin a) ℂ}
    (h : F =ᶠ[nhds x] G) : PositivityTheory.RgBcC.Eu s i j F x = PositivityTheory.RgBcC.Eu s i j G x := by
  simp only [PositivityTheory.RgBcC.Eu, Pi.add_apply, Pi.smul_apply, rd_congr _ h]

theorem epow_along (w : InfinitePlace E) (g : GA E a) (s : Bool) (m : ℕ) (i j : Fin a) (φ : Sm E a)
    {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    PositivityTheory.RgBcC.Epow s m i j (along w g φ.1) x = along w g (Formalism.REAL.epow (eopW w s) m i j φ).1 x := by
  induction m generalizing i j x with
  | zero =>
    simp only [PositivityTheory.RgBcC.Epow, Formalism.REAL.epow]
    split_ifs with h
    · simp
    · simp [along_zero]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.Epow]
    rw [Finset.sum_apply, epow_succ']
    simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, along_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hev : PositivityTheory.RgBcC.Epow s m c j (along w g φ.1) =ᶠ[nhds x]
        along w g (Formalism.REAL.epow (eopW w s) m c j φ).1 :=
      Filter.eventually_of_mem (isOpen_GLs.mem_nhds hx) fun y hy => ih c j hy
    rw [eu_congr s i c hev, eu_along w g s _ i c hx]

theorem gel_along (w : InfinitePlace E) (g : GA E a) (s : Bool) (m : ℕ) (φ : Sm E a)
    {x : Matrix (Fin a) (Fin a) ℂ} (hx : x ∈ PositivityTheory.RgBcC.GLs a) :
    PositivityTheory.RgBcC.gel s m (along w g φ.1) x = along w g (Formalism.REAL.etr (eopW w s) m φ).1 x := by
  simp only [PositivityTheory.RgBcC.gel, Formalism.REAL.etr, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, along_sum]
  exact Finset.sum_congr rfl fun i _ => epow_along w g s m i i φ hx

end PositivityTheory.RgBcC.Bridge
