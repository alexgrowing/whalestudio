import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeAlternatingFormBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeFormComplexStructureBaseChStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulTraceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.UnitaryStd
open scoped TensorProduct

section Lemmas
variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

theorem finrank_int : Module.finrank ℤ (Lat ρ g) = r * (g + g) := by
  rw [Module.finrank_eq_card_basis (basis ρ g)]
  simp [Fintype.card_prod, Fintype.card_sum]

instance : Module.Finite (𝓞 E) (Lat ρ g) := Module.Finite.of_restrictScalars_finite ℤ _ _

theorem finrank_eq (s : ℕ) (hr : r = s * Module.finrank ℚ E) :
    Module.finrank (𝓞 E) (Lat ρ g) = s * g + s * g := by
  have h := GlobalTheory.ZM.finrank_int_eq_mul (𝓞 E) (Lat ρ g)
  rw [finrank_int, RingOfIntegers.rank] at h
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h2 : Module.finrank ℚ E * (s * g + s * g) = Module.finrank ℚ E * Module.finrank (𝓞 E) (Lat ρ g) := by
    rw [← h, hr]; ring
  exact (Nat.eq_of_mul_eq_mul_left hn h2).symm

theorem smul_ne_zero' {c : 𝓞 E} {x : Lat ρ g} (hc : c ≠ 0) (hx : x ≠ 0) : c • x ≠ 0 := by
  intro h
  obtain ⟨m, hm, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hc)
  have : m • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) m x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hx ((smul_eq_zero.1 this).resolve_left hm)

instance : Module.Projective (𝓞 E) (Lat ρ g) := by
  have : Module.Flat (𝓞 E) (Lat ρ g) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    exact smul_ne_zero' ρ g (nonZeroDivisors.coe_ne_zero c) hx hc
  have : Module.FinitePresentation (𝓞 E) (Lat ρ g) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem cx_cx (x : Lat ρ g) : cx ρ g (cx ρ g x) = -x := by
  ext i k <;> simp [cx_apply, neg_apply]

theorem form_cx_cx (S : Matrix (Fin r) (Fin r) ℤ) (x y : Lat ρ g) :
    form ρ g S (cx ρ g x) (cx ρ g y) = form ρ g S x y := by
  simp only [form_apply, cx_apply, dotProduct_neg, neg_dotProduct]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cx_smul (a : 𝓞 E) (x : Lat ρ g) : cx ρ g (a • x) = a • cx ρ g x := by
  ext i k <;> simp [cx_apply, smul_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

theorem form_self (S : Matrix (Fin r) (Fin r) ℤ) (hS : S.transpose = S) (x : Lat ρ g) : form ρ g S x x = 0 := by
  have hS' : ∀ i j, S j i = S i j := fun i j => by rw [← Matrix.transpose_apply S i j, hS]
  rw [form_apply]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hS' i j, dotProduct_comm]

theorem form_smul_left (S : Matrix (Fin r) (Fin r) ℤ) (b : 𝓞 E → 𝓞 E) (hb : ∀ a, (ρ a).transpose * S = S * ρ (b a))
    (a : 𝓞 E) (x y : Lat ρ g) : form ρ g S (a • x) y = form ρ g S x (b a • y) := by
  have hω : ∀ (c : Fin r → ℤ) (u : Lat ρ g) (v : (Fin g → ℤ) × (Fin g → ℤ)),
      (∑ k, c k • u k).1 ⬝ᵥ v.2 - (∑ k, c k • u k).2 ⬝ᵥ v.1 = ∑ k, c k * ((u k).1 ⬝ᵥ v.2 - (u k).2 ⬝ᵥ v.1) := by
    intro c u v
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct, smul_dotProduct,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hω' : ∀ (c : Fin r → ℤ) (u : (Fin g → ℤ) × (Fin g → ℤ)) (v : Lat ρ g),
      u.1 ⬝ᵥ (∑ k, c k • v k).2 - u.2 ⬝ᵥ (∑ k, c k • v k).1 = ∑ k, c k * (u.1 ⬝ᵥ (v k).2 - u.2 ⬝ᵥ (v k).1) := by
    intro c u v
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hL : form ρ g S (a • x) y =
      ∑ k, ∑ j, ((ρ a).transpose * S) k j * ((x k).1 ⬝ᵥ (y j).2 - (x k).2 ⬝ᵥ (y j).1) := by
    rw [form_apply]
    simp only [smul_apply, hω, Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hR : form ρ g S x (b a • y) =
      ∑ k, ∑ j, (S * ρ (b a)) k j * ((x k).1 ⬝ᵥ (y j).2 - (x k).2 ⬝ᵥ (y j).1) := by
    rw [form_apply]
    simp only [smul_apply, hω', Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hL, hR, hb]

theorem form_bijective (S : Matrix (Fin r) (Fin r) ℤ) (hS : IsUnit S.det) : Function.Bijective (form ρ g S) :=
  GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective ρ g S hS

theorem form_cx_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef) (x : ℝ ⊗[ℤ] Lat ρ g)
    (hx : x ≠ 0) : 0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x :=
  GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos ρ g S hS x hx

theorem trace_act (a : 𝓞 E) : LinearMap.trace ℤ (Lat ρ g) (act ρ g a) = 2 * g * (ρ a).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℤ (basis ρ g)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, basis_repr, act_apply, smul_apply]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, basis_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
    Pi.single_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem trace_cx_act (a : 𝓞 E) : LinearMap.trace ℤ (Lat ρ g) (cx ρ g ∘ₗ act ρ g a) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℤ (basis ρ g)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, basis_repr, LinearMap.comp_apply, act_apply,
    cx_apply, smul_apply]
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, basis_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
    Pi.single_apply]

theorem trace_rep (s : ℕ) (hr : r = s * Module.finrank ℚ E) (a : 𝓞 E) :
    (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a :=
  GlobalTheory.T.trace_ringHom_eq_mul_algebraTrace ρ s hr a

end Lemmas

section Datum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ)
  (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g s : ℕ)

theorem dom_exists (hpos : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (hr : r = s * Module.finrank ℚ E) :
    ∃ J : ℝ ⊗[ℤ] Lat ρ g →ₗ[ℝ] ℝ ⊗[ℤ] Lat ρ g, (∀ x, J (J x) = -x) ∧
    (∀ x y, (form ρ g S).baseChange ℝ (J x) (J y) = (form ρ g S).baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < (form ρ g S).baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] Lat ρ g →ₗ[ℝ] ℝ ⊗[ℤ] Lat ρ g) (t : ℂ), (∀ x : Lat ρ g, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        (((s * g : ℕ) : ℂ) * τ (a : E) + ((s * g : ℕ) : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  have hcc : cx ρ g ∘ₗ cx ρ g = -LinearMap.id := LinearMap.ext fun x => cx_cx ρ g x
  refine ⟨(cx ρ g).baseChange ℝ, fun x => ?_, fun x y => ?_, form_cx_pos ρ g S hpos, fun a A t hA ht => ?_⟩
  · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcc, LinearMap.baseChange_neg,
      LinearMap.baseChange_id]
    rfl
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul c m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul d n =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        rw [form_cx_cx]
  · have hAe : A = (act ρ g a).baseChange ℝ := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => simp only [map_add, hx, hx']
      | tmul c m =>
        have h1 : c ⊗ₜ[ℤ] m = c • ((1 : ℝ) ⊗ₜ[ℤ] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [h1, map_smul, map_smul, hA, LinearMap.baseChange_tmul, act_apply]
    have ht' : t = ((s * g : ℕ) : ℂ) * ((Algebra.trace ℤ (𝓞 E) a : ℤ) : ℂ) := by
      rw [ht, ← GlobalTheory.HostModel.sum_add_conj_eq_trace H a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => by ring
    have hcomm : cx ρ g ∘ₗ act ρ g a = act ρ g a ∘ₗ cx ρ g :=
      LinearMap.ext fun x => cx_smul ρ g a x
    refine ⟨?_, ?_, ?_⟩
    · rw [hAe, ← LinearMap.baseChange_comp, hcomm, LinearMap.baseChange_comp]
    · rw [hAe, LinearMap.trace_baseChange, trace_act, trace_rep ρ s hr, ht']
      simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re, Complex.natCast_im, Complex.intCast_im]
      push_cast
      norm_num
      ring
    · rw [hAe, ← LinearMap.baseChange_comp, LinearMap.trace_baseChange, trace_cx_act, ht']
      simp

def stdDatum (hSt : S.transpose = S) (hdet : IsUnit S.det) (hpos : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (hρ : ∀ a, (ρ a).transpose * S = S * ρ (H.bar a)) (hr : r = s * Module.finrank ℚ E) : Datum H where
  La := Lat ρ g
  fin := inferInstance
  proj := inferInstance
  EF := form ρ g S
  alt := form_self ρ g S hSt
  unimod := form_bijective ρ g S hdet
  adj a x y := form_smul_left ρ g S (fun a => H.bar a) hρ a x y
  p := s * g
  q := s * g
  rank := finrank_eq ρ g s hr
  dom := dom_exists H S ρ g s hpos hr

end Datum

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ g s : ℕ, r = s * Module.finrank ℚ E → ∃ (Dm : Datum H) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), Dm.p = s * g ∧ Dm.q = s * g ∧ (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) ∧ ∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1) := by
  intro E _ _ _ H r W hpos hdet ρ hρ _ g s hr
  have hSt : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  exact ⟨stdDatum H (W + W.transpose) ρ g s hSt hdet hpos hρ hr,
    { toFun := fun x => x, invFun := fun x => x, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }, rfl, rfl, fun a x i => rfl, fun x y => rfl⟩

end GlobalTheory.UnitaryStd
