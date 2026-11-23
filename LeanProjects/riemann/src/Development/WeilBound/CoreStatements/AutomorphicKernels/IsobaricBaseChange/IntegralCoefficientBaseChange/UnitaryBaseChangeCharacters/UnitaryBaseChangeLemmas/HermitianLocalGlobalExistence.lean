import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.LatticeStep
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.NormStep
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UsideLeaf.hermitian_local_global_existence

theorem mem_intL_iff {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ intL (w.adicCompletion E) ↔ x ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valuation.mem_integer_iff _ _

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] (w : Pl E) {n : ℕ} (g : GL (Fin n) (w.adicCompletion E)) :
    g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, g.val i j ∈ intL (w.adicCompletion E)) ∧
      (∀ i j, (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j ∈ intL (w.adicCompletion E)) := by
  constructor
  · rintro ⟨g0, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [mem_intL_iff]
      exact (g0.val i j).2
    · rw [← map_inv, mem_intL_iff]
      exact ((g0⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let O := Ov E w
    have hO : ∀ x, x ∈ intL (w.adicCompletion E) → x ∈ O := fun x hx => (mem_intL_iff w x).1 hx
    let a : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, hO _ (h1 i j)⟩
    let b : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹ : GL (Fin n) _).val i j, hO _ (h2 i j)⟩
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) :=
      fun x y hxy => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hxy i) j)
    have ha : O.subtype.mapMatrix a = g.val := rfl
    have hb : O.subtype.mapMatrix b = (g⁻¹ : GL (Fin n) _).val := rfl
    have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; exact g.mul_inv)
    have hba : b * a = 1 := hinj (by rw [map_mul, ha, hb, map_one]; exact g.inv_mul)
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext i j
    rfl

section Util

variable {A : Type} [CommRing A]

theorem cT_cT (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_map {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) (τ : E →+* E) (σ : K →+* K)
    (h : ∀ x, σ (φ x) = φ (τ x)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) : cT σ (M.map φ) = (cT τ M).map φ := by
  ext i j; simp [cT, h]

theorem int_mul {K : Type} [Ring K] (S : Subring K) {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ S) (hN : ∀ i j, N i j ∈ S) : ∀ i j, (M * N) i j ∈ S := fun i j => by
  rw [Matrix.mul_apply]; exact S.sum_mem fun k _ => S.mul_mem (hM i k) (hN k j)

theorem int_cT {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ intL K) : ∀ i j, cT σ M i j ∈ intL K := fun i j => by
  have h := hM j i
  simp only [intL, Valuation.mem_integer_iff] at h ⊢
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ]
  exact h

end Util

theorem sep_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (hγ : ∀ i j, γ i j ∈ intL K) (A B : K[X]) (hA : ∀ i, A.coeff i ∈ intL K) (hB : ∀ i, B.coeff i ∈ intL K)
    (hAB : A * γ.charpoly + B * derivative γ.charpoly = 1) :
    ∃ Q₀ : (intL K)[X], γ.charpoly = Q₀.map (intL K).subtype ∧ Q₀.Separable := by
  let γO : Matrix (Fin n) (Fin n) (intL K) := fun i j => ⟨γ i j, hγ i j⟩
  have hγO : γO.map (intL K).subtype = γ := by ext i j; rfl
  have hlift : ∀ C : K[X], (∀ i, C.coeff i ∈ intL K) → ∃ CO : (intL K)[X], CO.map (intL K).subtype = C := by
    intro C hC
    have : C ∈ Polynomial.lifts (intL K).subtype :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hC i⟩, rfl⟩
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  obtain ⟨AO, hAO⟩ := hlift A hA
  obtain ⟨BO, hBO⟩ := hlift B hB
  refine ⟨γO.charpoly, by rw [← Matrix.charpoly_map, hγO], ?_⟩
  refine ⟨AO, BO, Polynomial.map_injective (intL K).subtype Subtype.val_injective ?_⟩
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hAO, hBO,
    ← Matrix.charpoly_map, hγO, hAB, Polynomial.map_one]

theorem local_good (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (γ₀ : GL (Fin n) E)
    (H₀ : Matrix (Fin n) (Fin n) E) (hH₀ : IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀)
    (hd : H₀.det ≠ 0)
    (hγH : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (A B : E[X]) (hAB : A * γ₀.val.charpoly + B * derivative γ₀.val.charpoly = 1)
    (w : Pl E) (hw : ¬ IsSplitAt w)
    (h1 : ∀ i j, algebraMap E (w.adicCompletion E) (γ₀.val i j) ∈ w.adicCompletionIntegers E)
    (h2 : ∀ i j, algebraMap E (w.adicCompletion E) ((γ₀⁻¹ : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E)
    (h3 : ∀ i j, algebraMap E (w.adicCompletion E) (H₀ i j) ∈ w.adicCompletionIntegers E)
    (h4 : ∀ i j, algebraMap E (w.adicCompletion E) (H₀⁻¹ i j) ∈ w.adicCompletionIntegers E)
    (h5 : ∀ i, algebraMap E (w.adicCompletion E) (A.coeff i) ∈ w.adicCompletionIntegers E)
    (h6 : ∀ i, algebraMap E (w.adicCompletion E) (B.coeff i) ∈ w.adicCompletionIntegers E)
    (Hw : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hHw : IsHerm (cj w) Hw ∧ Hw.det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * Hw *
      γ₀.val.map (algebraMap E (w.adicCompletion E)) = Hw)
    (k m : GL (Fin n) (w.adicCompletion E))
    (hk : k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n)
    (hm : m ∈ GlobalTheory.LFun.KGL w n) (hkm : m.val = cT (cj w) k.val * Hw * k.val) :
    ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) =
      γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧
      Hw = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val := by
  set φ : E →+* (w.adicCompletion E) := algebraMap E (w.adicCompletion E) with hφ
  set τ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hτ
  obtain ⟨-, hinv, hiso, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  have hext' : ∀ x, cj w (φ x) = φ (τ x) := hext
  have hcT : ∀ M : Matrix (Fin n) (Fin n) E, cT (cj w) (M.map φ) = (cT τ M).map φ := cT_map φ τ (cj w) hext'
  set γw := γ₀.val.map φ with hγw
  set γiw := (γ₀⁻¹ : GL (Fin n) E).val.map φ with hγiw
  set J := H₀.map φ with hJ
  set Ji := H₀⁻¹.map φ with hJi
  have hI : ∀ x : E, φ x ∈ w.adicCompletionIntegers E → φ x ∈ intL (w.adicCompletion E) := fun x hx => (mem_intL_iff w _).2 hx
  have iγ : ∀ i j, γw i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h1 i j)
  have iγi : ∀ i j, γiw i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h2 i j)
  have iJ : ∀ i j, J i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h3 i j)
  have iJi : ∀ i j, Ji i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h4 i j)
  have hmap1 : (1 : Matrix (Fin n) (Fin n) E).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have hγγ : γw * γiw = 1 := by rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hmap1]
  have hJJ : J * Ji = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), hmap1]
  have hJh : cT (cj w) J = J := by rw [hcT]; exact congrArg (fun M => M.map φ) hH₀
  have hγJ : cT (cj w) γw * J * γw = J := by
    rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hγH]

  have hABw : A.map φ * γw.charpoly + B.map φ * derivative γw.charpoly = 1 := by
    rw [hγw, Matrix.charpoly_map, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, hAB, Polynomial.map_one]
  obtain ⟨Q₀, hch, hsep⟩ := sep_int γw iγ (A.map φ) (B.map φ) (fun i => by rw [Polynomial.coeff_map]; exact hI _ (h5 i))
    (fun i => by rw [Polynomial.coeff_map]; exact hI _ (h6 i)) hABw

  obtain ⟨hk1, hk2⟩ := (mem_KGL_iff w _).1 hk
  have hkv : (k⁻¹ * GeneralLinearGroup.map φ γ₀ * k).val = (k⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw * k.val := rfl
  have hkiv : ((k⁻¹ * GeneralLinearGroup.map φ γ₀ * k)⁻¹ : GL (Fin n) (w.adicCompletion E)).val =
      (k⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γiw * k.val := by
    rw [show (k⁻¹ * GeneralLinearGroup.map φ γ₀ * k)⁻¹ = k⁻¹ * GeneralLinearGroup.map φ γ₀⁻¹ * k by
      rw [map_inv]; group]
    rfl
  obtain ⟨a, g, hac, rfl, ig, igi⟩ := GlobalTheory.UsideLeaf.UnitaryLocalCharpoly.lattice_step γw γiw Q₀ iγ iγi hγγ hch hsep k
    (fun i j => hkv ▸ hk1 i j) (fun i j => hkiv ▸ hk2 i j)
  obtain ⟨im, imi⟩ := (mem_KGL_iff w _).1 hm

  set σ := cj w
  set Hn := cT σ a.val * Hw * a.val with hHn
  have hcTg : cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val = 1 := by
    rw [← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
  have hHn' : Hn = cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * m.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
    rw [hkm, Units.val_mul, cT_mul]
    calc Hn = (cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val) * Hn * (g.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val) := by
          rw [hcTg, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [hHn, Matrix.mul_assoc]
  set Hi := g.val * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val with hHi
  have iH : ∀ i j, Hn i j ∈ intL (w.adicCompletion E) := by
    rw [hHn']; exact int_mul _ (int_mul _ (int_cT σ hiso igi) im) igi
  have iHi : ∀ i j, Hi i j ∈ intL (w.adicCompletion E) := int_mul _ (int_mul _ ig imi) (int_cT σ hiso ig)
  have hHH : Hn * Hi = 1 := by
    rw [hHn', hHi]
    calc cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * m.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (g.val * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val)
        = cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (m.val * (((g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * g.val) * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val)) *
          cT σ g.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
  have hHh : cT σ Hn = Hn := by
    rw [hHn, cT_mul, cT_mul, cT_cT σ hinv, hHw.1, Matrix.mul_assoc]
  have hγH' : cT σ γw * Hn * γw = Hn := by
    calc cT σ γw * Hn * γw = cT σ (a.val * γw) * Hw * (a.val * γw) := by
          rw [hHn, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (γw * a.val) * Hw * (γw * a.val) := by rw [hac]
      _ = cT σ a.val * (cT σ γw * Hw * γw) * a.val := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Hn := by rw [hHw.2.2]

  obtain ⟨b, hbc, hbJ⟩ := GlobalTheory.UsideLeaf.UnitaryLocalCharpoly.norm_step σ ϖ q hUI γw J Ji Hn Hi Q₀ iγ iJ iJi iH iHi hJJ hHH hJh
    hHh hγJ hγH' hch hsep
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · have hai : (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw = γw * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
      calc (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw = (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (γw * a.val) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (a.val * γw) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by rw [hac]
        _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [Units.val_mul, Matrix.mul_assoc, hai, ← Matrix.mul_assoc, hbc, Matrix.mul_assoc]
  · calc Hw = cT σ (a.val * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val) * Hw * (a.val * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * Hn * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
          rw [hHn, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (cT σ b.val * J * b.val) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by rw [hbJ]
      _ = _ := by rw [Units.val_mul, cT_mul]; simp only [Matrix.mul_assoc]

theorem eventually_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_int_coeff {E : Type} [Field E] [NumberField E] (A : E[X]) :
    ∀ᶠ w : Pl E in cofinite, ∀ i, algebraMap E (w.adicCompletion E) (A.coeff i) ∈ w.adicCompletionIntegers E := by
  have h := (Filter.eventually_all_finset A.support).2 fun i _ => eventually_int (A.coeff i)
  filter_upwards [h] with w hw i
  by_cases hi : i ∈ A.support
  · exact hw i hi
  · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
    exact zero_mem _

theorem eventually_int_mat {E : Type} [Field E] [NumberField E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_int (M i j)

end GlobalTheory.UsideLeaf.hermitian_local_global_existence

theorem GlobalTheory.UsideLeaf.hermitian_local_global_existence.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) := by
  intro E _ _ _ hU n γ₀ hEll H₀ hH₀ hd hγH H hH hlat
  obtain ⟨A, B, hAB⟩ := hEll.2.2.1
  filter_upwards [hlat, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat γ₀.val,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat (γ₀⁻¹ : GL (Fin n) E).val,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat H₀, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat H₀⁻¹,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_coeff A, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_coeff B]
    with w hw h1 h2 h3 h4 h5 h6 hns
  obtain ⟨k, m, hk, hm, hkm⟩ := hw hns
  exact GlobalTheory.UsideLeaf.hermitian_local_global_existence.local_good E hU n γ₀ H₀ hH₀ hd hγH A B hAB w hns h1 h2 h3 h4 h5 h6 (H w) (hH w hns)
    k m hk hm hkm
