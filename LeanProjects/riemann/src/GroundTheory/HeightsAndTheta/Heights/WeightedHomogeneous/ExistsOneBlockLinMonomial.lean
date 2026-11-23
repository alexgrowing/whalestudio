import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

theorem isMultiHomog_unit_iff {R : Type*} [CommRing R] {ι : Unit → Type*} [∀ k, Fintype (ι k)]
    (f : MvPolynomial (Σ k, ι k) R) (N : ℕ) :
    IsMultiHomog (R := R) (ι := ι) f (fun _ ↦ N) ↔ f.IsHomogeneous N := by
  have hdeg : ∀ m : (Σ k, ι k) →₀ ℕ, ∑ i, m ⟨(), i⟩ = Finsupp.weight 1 m := by
    intro m
    have h1 : m.degree = Finsupp.weight 1 m := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit ↦ ∑ y : ι u, m ⟨u, y⟩)).symm
  simp only [IsMultiHomog, IsHomogeneous, IsWeightedHomogeneous, mem_support_iff]
  constructor
  · intro h d hd
    rw [← hdeg]
    exact h d hd ()
  · intro h m hm k
    cases k
    rw [hdeg]
    exact h hm

theorem isArithVar_comap_rename {ι ι' : Unit → Type*} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (e : (Σ k, ι k) ≃ (Σ k, ι' k)) {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ e).toRingEquiv
  have hQ : P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι) = P.map E := by
    rw [← Ideal.comap_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    have ha' : a = fun _ ↦ a () := funext fun k ↦ by cases k; rfl
    rw [ha', isMultiHomog_unit_iff] at ha
    refine ⟨fun _ ↦ a (), ?_⟩
    rw [isMultiHomog_unit_iff]
    exact ha.rename_isHomogeneous
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    cases k
    obtain ⟨i, hi⟩ := hrel ()
    rcases hp : e ⟨(), i⟩ with ⟨⟨⟩, j⟩
    refine ⟨j, fun hj ↦ hi ?_⟩
    have hs : e.symm ⟨(), j⟩ = ⟨(), i⟩ := (Equiv.symm_apply_eq e).mpr hp.symm
    rw [Ideal.mem_comap, rename_X, hs] at hj
    exact hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι') (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) =
        Ideal.comap (C : ℤ →+* MRing ι) P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P _ E hQ)).symm

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

def oneBlockLin : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ →+* MvPolynomial (Fin (i + 1)) (𝓞 K) :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (om p.2.1) * X p.2.2

def affEval : MvPolynomial (Fin (i + 1)) (𝓞 K) →+* FractionRing (MvPolynomial (Fin i) K) :=
  eval₂Hom ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K)) (affGen K i)

theorem eval₂_oneBlockPt [NumberField K] (g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ) :
    eval₂ (Int.castRingHom _) (oneBlockPt om i) g = affEval i (oneBlockLin om i g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C, oneBlockLin, eval₂Hom_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p v hp =>
    simp only [eval₂_mul, map_mul, hp, eval₂_X]
    congr 1
    simp [oneBlockLin, affEval, oneBlockPt]

theorem oneBlockLin_isHomogeneous {g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ} {N : ℕ}
    (hg : g.IsHomogeneous N) : (oneBlockLin om i g).IsHomogeneous N := by
  have h : (eval₂ (Int.castRingHom (MvPolynomial (Fin (i + 1)) (𝓞 K))) (fun p ↦ C (om p.2.1) * X p.2.2)
      g).IsHomogeneous (1 * N) := hg.eval₂ _ _ (fun r ↦ ?_) (fun p ↦ ?_)
  · rw [one_mul] at h
    exact h
  · show ((r : MvPolynomial (Fin (i + 1)) (𝓞 K))).IsHomogeneous 0
    rw [← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) r]
    exact isHomogeneous_C _ _
  · simpa using (isHomogeneous_C (Fin (i + 1)) (om p.2.1)).mul (isHomogeneous_X (𝓞 K) p.2.2)

def linForm (c : 𝓞 K) (j : Fin (i + 1)) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  ∑ a, C (om.repr c a) * X ⟨(), (a, j)⟩

theorem linForm_isHomogeneous (c : 𝓞 K) (j : Fin (i + 1)) : (linForm om i c j).IsHomogeneous 1 := by
  refine IsHomogeneous.sum _ _ _ fun a _ ↦ ?_
  simpa using (isHomogeneous_C _ (om.repr c a)).mul (isHomogeneous_X ℤ (⟨(), (a, j)⟩ : Σ _ : Unit, Fin d × Fin (i + 1)))

theorem oneBlockLin_linForm (c : 𝓞 K) (j : Fin (i + 1)) :
    oneBlockLin om i (linForm om i c j) = C c * X j := by
  conv_rhs => rw [← om.sum_repr c]
  simp only [linForm, oneBlockLin, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [zsmul_eq_mul, map_mul, map_intCast, mul_assoc]

def powForm (β : Fin (i + 1) →₀ ℕ) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  β.prod fun j n ↦ linForm om i 1 j ^ n

theorem powForm_isHomogeneous (β : Fin (i + 1) →₀ ℕ) : (powForm om i β).IsHomogeneous β.degree := by
  have h := IsHomogeneous.prod β.support (fun j ↦ linForm om i 1 j ^ β j) (fun j ↦ 1 * β j)
    (fun j _ ↦ (linForm_isHomogeneous om i 1 j).pow (β j))
  simp only [one_mul] at h
  exact h

theorem oneBlockLin_powForm (β : Fin (i + 1) →₀ ℕ) : oneBlockLin om i (powForm om i β) = monomial β 1 := by
  rw [powForm, map_finsuppProd]
  simp only [map_pow, oneBlockLin_linForm, map_one, one_mul]
  exact prod_X_pow_eq_monomial

theorem exists_oneBlockLin_monomial (α : Fin (i + 1) →₀ ℕ) (hα : α ≠ 0) (c : 𝓞 K) :
    ∃ g, g.IsHomogeneous α.degree ∧ oneBlockLin om i g = monomial α c := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
    by_contra h
    push Not at h
    exact hα (Finsupp.ext h)
  have hle : Finsupp.single j 1 ≤ α := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)
  have hsplit : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := (add_tsub_cancel_of_le hle).symm
  refine ⟨linForm om i c j * powForm om i (α - Finsupp.single j 1), ?_, ?_⟩
  · have h := (linForm_isHomogeneous om i c j).mul (powForm_isHomogeneous om i (α - Finsupp.single j 1))
    convert h using 1
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  · rw [map_mul, oneBlockLin_linForm, oneBlockLin_powForm, C_mul_X_eq_monomial, monomial_mul, mul_one,
      ← hsplit]

theorem mem_secM_oneBlockPt_iff [NumberField K] (N : ℕ) (hN : 1 ≤ N) (s : FractionRing (MvPolynomial (Fin i) K)) :
    s ∈ secM (oneBlockPt om i) (fun _ ↦ N) ↔
      ∃ F : MvPolynomial (Fin (i + 1)) (𝓞 K), F.IsHomogeneous N ∧
        s = eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp
          (algebraMap (𝓞 K) K)) (affGen K i) F := by
  have hev : ∀ F : MvPolynomial (Fin (i + 1)) (𝓞 K),
      eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K))
        (affGen K i) F = affEval i F := fun _ ↦ rfl
  simp only [hev]
  rw [secM, Submodule.mem_toAddSubgroup]
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [isMultiHomog_unit_iff] at hg
      refine ⟨oneBlockLin om i g, oneBlockLin_isHomogeneous om i hg, ?_⟩
      exact eval₂_oneBlockPt om i g
    | zero => exact ⟨0, isHomogeneous_zero _ _ _, (map_zero (affEval i)).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF, rfl⟩ := hx
      obtain ⟨G, hG, rfl⟩ := hy
      exact ⟨F + G, hF.add hG, (map_add (affEval i) F G).symm⟩
    | smul n x _ hx =>
      obtain ⟨F, hF, rfl⟩ := hx
      refine ⟨n • F, ?_, (map_zsmul (affEval i) n F).symm⟩
      rw [zsmul_eq_mul, ← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) n]
      simpa using hF.C_mul (n : 𝓞 K)
  · rintro ⟨F, hF, rfl⟩
    rw [F.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα ↦ ?_
    have hdeg : α.degree = N := by
      have h := hF (mem_support_iff.mp hα)
      rw [← h, Finsupp.degree_eq_weight_one]
      rfl
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp at hdeg
      omega
    obtain ⟨g, hg, hgα⟩ := exists_oneBlockLin_monomial om i α hα0 (coeff α F)
    rw [hdeg] at hg
    refine Submodule.subset_span ⟨g, (isMultiHomog_unit_iff g N).mpr hg, ?_⟩
    rw [← hgα]
    exact eval₂_oneBlockPt om i g

end Values

def oneBlockReindexEquiv (e r : ℕ) :
    Coord (oneBlockSizes e r) ≃ (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) where
  toFun := oneBlockReindex e r
  invFun := oneBlockReindexInv e r
  left_inv v := by rcases v with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]
  right_inv p := by rcases p with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]

theorem OneBlockModel.imp (hA : Heights.OneBlockModel.Statement) : OneBlockModel.Statement := by
  intro K _ _ d om i
  refine ⟨?_, fun N hN s ↦ mem_secM_oneBlockPt_iff om i N hN s⟩
  cases d with
  | zero => exact ((om.index_nonempty).elim fun x ↦ x.elim0)
  | succ e =>
    obtain ⟨hstd, hideal, -⟩ := Heights.OneBlockStandard.proof K e i om
    have h := (hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1)) (oneBlockForms om) hstd).2.2.1
    rw [hideal] at h
    rw [mCoordIdeal_eq_comap om]
    exact isArithVar_comap_rename (oneBlockReindexEquiv e i) h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
