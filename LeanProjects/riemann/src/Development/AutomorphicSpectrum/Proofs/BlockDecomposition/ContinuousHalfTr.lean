import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

section Gen

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [CommRing A] [Algebra F A]

theorem trace_one_tmul' (e : E) :
    Algebra.trace A (A ⊗[F] E) ((1 : A) ⊗ₜ[F] e) = algebraMap F A (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem ann_gen (P : A → Prop) (hP : ∀ x : A, (∀ t : F, P (algebraMap F A t * x)) → ∃ c : F, x = algebraMap F A c)
    (z : A ⊗[F] E) (h : ∀ e : E, P (Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z))) :
    ∃ w : E, z = (1 : A) ⊗ₜ[F] w := by
  classical
  let b := Module.finBasis F E
  have hnd := traceForm_nondegenerate F E
  let d := (Algebra.traceForm F E).dualBasis hnd b
  let B := Algebra.TensorProduct.basis A b
  have hB : ∀ k, B k = (1 : A) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hz : ∑ k, B.repr z k • ((1 : A) ⊗ₜ[F] b k) = z := by
    simpa only [hB] using B.sum_repr z
  have ht : ∀ e : E, Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z) =
      ∑ k, B.repr z k * algebraMap F A (Algebra.trace F E (e * b k)) := by
    intro e
    conv_lhs => rw [← hz]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_smul, trace_one_tmul', smul_eq_mul]
  have hak : ∀ k, ∃ c : F, B.repr z k = algebraMap F A c := fun k => by
    refine hP _ fun t => ?_
    have h1 := h (t • d k)
    rw [ht] at h1
    have h2 : ∀ l, Algebra.trace F E (t • d k * b l) = if l = k then t else 0 := fun l => by
      have h3 : Algebra.trace F E (d k * b l) = if l = k then 1 else 0 :=
        LinearMap.BilinForm.apply_dualBasis_left hnd b k l
      rw [smul_mul_assoc, map_smul, h3]
      split_ifs <;> simp
    simp only [h2] at h1
    have h4 : ∑ l, B.repr z l * algebraMap F A (if l = k then t else 0) =
        algebraMap F A t * B.repr z k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [if_neg hl, map_zero, mul_zero])
        (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, mul_comm]
    rwa [h4] at h1
  choose c hc using hak
  refine ⟨∑ k, c k • b k, ?_⟩
  rw [← hz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Gen

theorem halfTr_add' (a b : AE D) : halfTr (a + b) = halfTr a + halfTr b := by
  simp only [halfTr, trA, map_add, mul_add]

theorem halfTr_zero' : halfTr (0 : AE D) = 0 := by
  simp [halfTr]

theorem halfTr_neg' (a : AE D) : halfTr (-a) = -halfTr a := by
  simp only [halfTr, trA, map_neg, mul_neg]

theorem halfTr_add_cA (w : AE D) : halfTr (w + cA D w) = Algebra.trace (AF D.host.F) (AE D) w := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add, add_halves, map_one]
  simp only [halfTr, trA, map_add, Formalism.IndefR.Datum.Brg.trace_cA, mul_add]
  rw [← add_mul, h2, one_mul]

theorem halfTr_incA' (e : D.host.E) :
    halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
  rw [halfTr, trA, Formalism.IndefR.Fin.trace_incA, map_mul]

theorem continuous_halfTr' : Continuous (halfTr : AE D → AF D.host.F) :=
  continuous_const.mul Formalism.IndefR.Fin.cont_trace

def hE (i j : Fin r) (w : AE D) : Mx D r r :=
  Matrix.single j i w + Matrix.single i j (cA D w)

theorem adj_single' (a b : Fin r) (v : AE D) :
    adj (Matrix.single a b v : Mx D r r) = Matrix.single b a (cA D v) := by
  ext k l
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = l ∧ b = k
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (by tauto), map_zero]

theorem hE_mem (i j : Fin r) (w : AE D) : hE i j w ∈ hermA D r := by
  change adj (hE i j w) = hE i j w
  rw [hE, adj_add, adj_single', adj_single', cA_cA, add_comm]

theorem trace_hE_mul (i j : Fin r) (w : AE D) {z : Mx D r r} (hz : z ∈ hermA D r) :
    Matrix.trace (HMul.hMul (hE i j w) z : Mx D r r) = w * z i j + cA D (w * z i j) := by
  have h : adj z = z := hz
  have hji : z j i = cA D (z i j) := (congrFun (congrFun h j) i).symm
  rw [hE, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, hji, map_mul]
  rfl

theorem rat_single' (a b : Fin r) (e : D.host.E) :
    (rat (Matrix.single a b e) : Mx D r r) = Matrix.single a b (incA D e) := by
  ext k l
  simp only [rat, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = k ∧ b = l
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem hE_rat (i j : Fin r) (e : D.host.E) : hE i j (incA D e) ∈ ratMx D r r := by
  refine ⟨Matrix.single j i e + Matrix.single i j (star e), ?_⟩
  show rat _ = _
  rw [rat_add, rat_single', rat_single', hE, GlobalTheory.DualPairCheck.cA_incA]

theorem ann_E {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : AE D)
    (h : ∀ e : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * z)) = 1) :
    ∃ w : D.host.E, z = incA D w :=
  ann_gen (F := D.host.F) (E := D.host.E) (A := AF D.host.F) (fun x => ψ x = 1)
    (fun x hx => GlobalTheory.T.adelic_character_orthogonal_is_rational D.host.F D.sp.cm.totReal ψ hψ x hx) z h

def chi (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r)))

theorem chi_add_left (ψ : AddChar (AF D.host.F) ℂ) (m m' : Mx D r r) (b : hermA D r) :
    chi ψ (m + m') b = chi ψ m b * chi ψ m' b := by
  simp only [chi]
  rw [Matrix.add_mul, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_add_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b c : hermA D r) :
    chi ψ m (b + c) = chi ψ m b * chi ψ m c := by
  simp only [chi, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_zero_left (ψ : AddChar (AF D.host.F) ℂ) (b : hermA D r) : chi ψ (0 : Mx D r r) b = 1 := by
  simp only [chi]
  rw [Matrix.zero_mul, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_zero_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) : chi ψ m (0 : hermA D r) = 1 := by
  simp only [chi, AddSubgroup.coe_zero]
  rw [Matrix.mul_zero, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_neg_left (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) :
    chi ψ (-m) b = ψ (-halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r))) := by
  simp only [chi]
  rw [Matrix.neg_mul, Matrix.trace_neg, halfTr_neg']

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {m : Mx D r r}
    (hm : m ∈ ratMx D r r) (c : ratHerm D r) : chi ψ m c.1 = 1 := by
  obtain ⟨γ, rfl⟩ := hm
  obtain ⟨δ, hδ⟩ := AddSubgroup.mem_comap.1 c.2
  have hδ' : rat δ = c.1.1 := hδ
  have h1 : (HMul.hMul (rat γ) c.1.1 : Mx D r r) = rat (γ * δ) := by rw [← hδ', rat_mul]
  have h2 : Matrix.trace (rat (γ * δ) : Mx D r r) = incA D (Matrix.trace (γ * δ)) := by
    simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  show ψ (halfTr (Matrix.trace (HMul.hMul (rat γ) c.1.1 : Mx D r r))) = 1
  rw [h1, h2, halfTr_incA']
  exact hψ.2.2.1 _

theorem continuous_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (m : Mx D r r) :
    Continuous (chi ψ m : hermA D r → ℂ) := by
  refine hψ.1.comp (continuous_halfTr'.comp ?_)
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

theorem star_psi' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ψ a * star (ψ a) = 1 := by
    have := hψ.2.1 a
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  rw [AddChar.map_neg_eq_inv]
  exact eq_inv_of_mul_eq_one_right h1

theorem rat_of_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : hermA D r)
    (h : ∀ t : ratHerm D r, chi ψ t.1.1 z = 1) : z ∈ ratHerm D r := by
  have key : ∀ i j, ∃ w : D.host.E, z.1 i j = incA D w := fun i j => by
    refine ann_E hψ _ fun e => ?_
    have h1 := h ⟨⟨hE i j (incA D e), hE_mem _ _ _⟩, AddSubgroup.mem_comap.2 (hE_rat i j e)⟩
    have h2 : chi ψ (hE i j (incA D e)) z = ψ (halfTr (Matrix.trace (HMul.hMul (hE i j (incA D e)) z.1 : Mx D r r))) := rfl
    rw [show chi ψ (hE i j (incA D e)) z = 1 from h1] at h2
    rw [trace_hE_mul i j _ z.2, halfTr_add_cA] at h2
    exact h2.symm
  choose w hw using key
  refine AddSubgroup.mem_comap.2 ⟨Matrix.of w, ?_⟩
  ext i j
  exact (hw i j).symm

theorem exists_chi_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : ratHerm D r)
    (hu : u ≠ 0) : ∃ b : hermA D r, chi ψ u.1.1 b ≠ 1 := by
  obtain ⟨γ, hγ⟩ := AddSubgroup.mem_comap.1 u.2
  have hγ' : rat γ = u.1.1 := hγ
  obtain ⟨x₀, hx₀⟩ := hψ.2.2.2
  obtain ⟨i, j, hij⟩ : ∃ i j, γ i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    have : γ = 0 := Matrix.ext fun i j => hc i j
    rw [← hγ', this, rat_zero]
    rfl
  obtain ⟨e₀, he₀⟩ := Algebra.trace_surjective D.host.F D.host.E 1
  let w : AE D := incA D (γ i j)⁻¹ * (x₀ • incA D e₀)
  refine ⟨⟨hE i j w, hE_mem _ _ _⟩, ?_⟩
  have h1 : chi ψ u.1.1 ⟨hE i j w, hE_mem _ _ _⟩ =
      ψ (halfTr (Matrix.trace (HMul.hMul (hE i j w) u.1.1 : Mx D r r))) := by
    simp only [chi]
    rw [Matrix.trace_mul_comm]
  rw [h1, trace_hE_mul i j _ u.1.2, halfTr_add_cA]
  have h2 : w * u.1.1 i j = x₀ • incA D e₀ := by
    rw [← hγ']
    show incA D (γ i j)⁻¹ * (x₀ • incA D e₀) * incA D (γ i j) = _
    rw [mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, one_mul]
  rw [h2, map_smul, Formalism.IndefR.Fin.trace_incA, he₀, map_one, smul_eq_mul, mul_one]
  exact hx₀

end GlobalTheory.CompanionTheory.HermPoisson
