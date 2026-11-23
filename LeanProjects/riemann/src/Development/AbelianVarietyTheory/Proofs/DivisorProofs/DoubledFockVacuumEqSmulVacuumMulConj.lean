import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeOnSchwartzTensorConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsRealISmulSignConjOStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceFrameColBlocksEqStatement

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
namespace GlobalTheory.RealLift.VacBox

def eL {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))

def eR {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))

theorem dbl_cols {α β : Type} [Fintype β] {P Q R S : ℕ} (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ) :
    (A * c * (dblM C)ᵀ).toCols₁ = A * c.submatrix id eL * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ = A * c.submatrix id eR * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eL = Jm P Q * c.submatrix id eL * Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eR = -(Jm P Q * c.submatrix id eR * Jm R S) :=
  GlobalTheory.T.doubledSpaceFrame_colBlocks_eq α β P Q R S A C c

theorem heisOp_rot_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 :=
  GlobalTheory.T.fockHeisenbergOperatorOfCoords_real_I_smul_signConj_one P Q R S c t

theorem box_deriv {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) :=
  GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj F κ a₁ b₁ a₂ b₂ f g₁ g₂ f₀ h hg₁ hg₂ hh hf₀ x

def conjS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem sumPl_smul_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (L L' : ι → Module.End ℂ V) (v : V) (z : ℂ) (h : ∀ w, L' w v = z • L w v) :
    sumPl (V := fun _ : ι => V) L' (PiTensorProduct.tprod ℂ fun _ => v) =
      z • sumPl (V := fun _ : ι => V) L (PiTensorProduct.tprod ℂ fun _ => v) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ∀ M : Module.End ℂ V, (fun i => Function.update (fun i => (LinearMap.id : V →ₗ[ℂ] V)) w M i v) =
      Function.update (fun _ => v) w (M v) := by
    intro M; funext i
    by_cases hi : i = w
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e, e, h w]
  exact MultilinearMap.map_update_smul _ _ _ _ _

theorem sub_smul' {m n k : Type} (z : ℂ) (M : Matrix m n ℂ) (e : k → n) :
    (z • M).submatrix id e = z • M.submatrix id e := rfl

theorem toCols_at {F E α β₁ β₂ : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {u : Matrix α (β₁ ⊕ β₂) (AE F E)} (hu : At (evI F) u) : At (evI F) u.toCols₁ ∧ At (evI F) u.toCols₂ :=
  ⟨fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inl j),
   fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inr j)⟩

theorem vac_box : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  intro hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
  obtain ⟨D, hD1⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  set f₁ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hf₁
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (conjS f₁)
  have hf₀' : ∀ x, f₀ x = f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) := fun x => hf₀ x
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  have hder : ∀ u₁ : Matrix α β (AE F E), At (evI F) u₁ → ∀ c₁ : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u₁.map (piInf (τ w)) = A w * c₁ w * (C w)ᵀ) →
      D u₁ f₁ = Φ (sumPl (fun w => heisOp (c₁ w)) (PiTensorProduct.tprod ℂ fun _ => 1)) := fun u₁ hu₁ c₁ hc₁ =>
    GlobalTheory.SDUnique.sd_unique ((hD1 u₁ hu₁ f₁).1) (hΦ.2 u₁ hu₁ c₁ hc₁ _)
  have hbox : ∀ u : Matrix α (β ⊕ β) (AE F E), At (evI F) u → ∀ x, Dd u f₀ x =
      D u.toCols₁ f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) +
        f₁ (x ∘ Sum.inl) * star (D u.toCols₂ f₁ (x ∘ Sum.inr)) := by
    intro u hu x
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine box_deriv (d.e u.toCols₁).1 (d.e u.toCols₁).2 (d.e u.toCols₂).1 (d.e u.toCols₂).2 f₁ _ _ f₀ _
      ((hD1 _ hu₁ f₁).2) ((hD1 _ hu₂ f₁).2) (fun y => ?_) hf₀' x
    rw [(hDd u hu f₀).2 y, e]
  have key : ∀ u u' : Matrix α (β ⊕ β) (AE F E), At (evI F) u → At (evI F) u' →
      ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (dblM (C w))ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * (((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) •
        (Jm P Q * c w * Jm (R + S) (S + R))) * (dblM (C w))ᵀ) →
      ∀ f f' : SInf F (κ ⊕ κ), SD (fun t => dd.rho ψ (realAd F t • u)) f₀ f →
        SD (fun t => dd.rho ψ (realAd F t • u')) f₀ f' → f' = Complex.I • f := by
    intro u u' hu hu' c hc hc' f f' hf hf'
    rw [← GlobalTheory.SDUnique.sd_unique ((hDd u hu f₀).1) hf, ← GlobalTheory.SDUnique.sd_unique ((hDd u' hu' f₀).1) hf']
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    obtain ⟨hu₁', hu₂'⟩ := toCols_at hu'
    have hI : ∀ w, ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) = ((1 : ℝ) : ℂ) * Complex.I := fun w => by simp
    have h1 := hder _ hu₁ (fun w => (c w).submatrix id eL) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).1, ← hc w]; rfl)
    have h2 := hder _ hu₂ (fun w => (c w).submatrix id eR) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).2.1, ← hc w]; rfl)
    have h1' := hder _ hu₁' (fun w => (((1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eL * Jm R S))
      (fun w => by
        rw [← (dbl_cols (A w) (C w) (c w)).2.2.1, ← sub_smul', ← hI w,
          ← (dbl_cols (A w) (C w) _).1, ← hc' w]; rfl)
    have h2' := hder _ hu₂' (fun w => (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S))
      (fun w => by
        have e : (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S) =
            ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) • (-(Jm P Q * (c w).submatrix id eR * Jm R S)) := by
          rw [hI w, smul_neg, ← neg_smul]; congr 1; push_cast; ring
        rw [e, ← (dbl_cols (A w) (C w) (c w)).2.2.2, ← sub_smul', ← (dbl_cols (A w) (C w) _).2.1, ← hc' w]; rfl)
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ 1)] at h1'
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ (-1))] at h2'
    rw [map_smul] at h1' h2'
    ext x
    rw [SchwartzMap.smul_apply, hbox u' hu' x, hbox u hu x, h1', h2', h1, h2]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  obtain ⟨z', hz'⟩ := hV F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd hCM hψ hFrd hΦd f₀ 1 key
  have hne1 : f₁ ≠ 0 := fun h0 => GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (h0.trans (map_zero Φ).symm))
  obtain ⟨y, hy⟩ : ∃ y, f₁ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne1 (SchwartzMap.ext h)
  have hz0 : z' ≠ 0 := by
    rintro rfl
    have h := congrArg (fun g : SInf F (κ ⊕ κ) => g (Sum.elim y y)) hz'
    simp only [zero_smul, SchwartzMap.zero_apply, hf₀', Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    exact mul_ne_zero hy (star_ne_zero.2 hy) h
  refine ⟨z'⁻¹, inv_ne_zero hz0, fun x => ?_⟩
  have h := congrArg (fun g : SInf F (κ ⊕ κ) => g x) hz'
  simp only [SchwartzMap.smul_apply, smul_eq_mul, hf₀'] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

end GlobalTheory.RealLift.VacBox

end
