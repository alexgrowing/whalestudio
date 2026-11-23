import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemFlagUnipotentIffOrderedEichlerProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagUnipotentNormalFormRescaledStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSymplecticBasisLocalExtensionStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

private theorem hf_add_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (a b y : Fin N → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (c : E) (a y : Fin N → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hq_sub_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a b y : Fin N → E) :
    hq sig Hm (a - b) y = hq sig Hm a y - hq sig Hm b y := by
  simp only [hq, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hq_neg_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a y : Fin N → E) :
    hq sig Hm (-a) y = -hq sig Hm a y := by
  simp only [hq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem algebraMap_integer_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact (isIntegral_algebraMap (x := a)).algebraMap

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (hΛ : Submodule.IsLattice E Λ)
  (c : ∀ p, ((A.loc p).Fp)ˣ) (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
  (n : ∀ p, (G.S p).GLV) (hn : {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite)
  (gF : ∀ p, Fin (r+1) → (G.S p).V) (gsF : ∀ p, Fin r → (G.S p).V) (X Y : Fin r → G.V)
  (hsel : ∀ p, (gF p = (G.S p).f ∧ gsF p = (G.S p).es) ∨ (gF p = (G.S p).f' ∧ gsF p = (G.S p).es'))
  (hX : ∀ p (a : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • gF p a.castSucc = A.bc p (X a))
  (hY : ∀ p (a : Fin r), gsF p a = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (Y a))
  (hnN : ∀ p, n p ∈ (G.S p).Nof (gF p)) :
  ∃ g : G.GLV, (∀ p, ∃ g' ∈ (G.S p).Nof (gF p), A.Ext p g g') ∧ ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  classical
  have hinj : ∀ p, Function.Injective (A.loc p).ιE := fun p => by
    have := PlacesInt.nontrivial_Ep (A.loc p)
    exact (A.loc p).ιE.injective
  have hform : ∀ p (x y : Fin (k + 2 * r + 1) → E),
      (G.S p).h (A.bc p x) (A.bc p y) = (A.loc p).ιE (hq sig G.Hm x y) := by
    intro p x y
    have h := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm x y
    show hf (A.L p) (G.S p).Hm _ _ = _
    rw [G.Hm_eq p]
    exact h
  have hconj : ∀ p z, (A.L p).cj ((A.loc p).ιE z) = (A.loc p).ιE (sig z) := fun p z => by
    rw [A.L_cj p]
    exact (A.loc p).cj_ιE z
  obtain ⟨p0⟩ := exists_place F
  have hsig : ∀ z, sig (sig z) = z := fun z => by
    apply hinj p0
    rw [← hconj, ← hconj]
    exact (A.L p0).cj_cj _
  have hH : ∀ i j, sig (G.Hm j i) = G.Hm i j := fun i j => by
    have h2 := congrFun (congrFun (G.S p0).herm.1 i) j
    rw [G.Hm_eq p0] at h2
    simp only [cT, Matrix.map_apply] at h2
    apply hinj p0
    rw [← hconj]
    exact h2
  have hqsym : ∀ x y, hq sig G.Hm x y = sig (hq sig G.Hm y x) := by
    intro x y
    simp only [hq, map_sum, map_mul, hsig]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH j i]
    ring
  have hXa : ∀ p (i : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • gF p i.castSucc = A.bc p (X i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hX p i
  have hYa : ∀ p (i : Fin r), gsF p i = algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • A.bc p (Y i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hY p i
  have hR : ∀ p, (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (Y j)) = if i = j then 1 else 0) ∧
      (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (X j)) = 0) ∧
      (∀ i j, (G.S p).h (A.bc p (Y i)) (A.bc p (Y j)) = 0) ∧
      ∀ m : (G.S p).GLV, m ∈ (G.S p).Nof (gF p) ↔ ∃ (u : Fin r → (G.S p).V) (s : Fin r → (A.loc p).Ep)
        (e : Fin r → (G.S p).GLV), (∀ i, (∀ j, j ≤ i → (G.S p).h (u i) (A.bc p (X j)) = 0 ∧
          (G.S p).h (u i) (A.bc p (Y j)) = 0) ∧ s i + (A.L p).cj (s i) = (G.S p).h (u i) (u i) ∧
          ∀ v, e i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u i) (s i) v) ∧ m = (List.ofFn e).prod := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled (A.L p) r k (G.S p) (gF p) (gsF p) (hsel p) (fun i => G.c p ^ (r - (i : ℕ)))
      (fun i => A.bc p (X i)) (fun i => A.bc p (Y i)) (hXa p) (hYa p)
  choose up sp ep hup hn_eq using fun p => ((hR p).2.2.2 (n p)).1 (hnN p)
  have hXY : ∀ a b, hq sig G.Hm (X a) (Y b) = if a = b then 1 else 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).1 a b]
    split_ifs <;> simp
  have hXX : ∀ a b, hq sig G.Hm (X a) (X b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.1 a b, map_zero]
  have hYY : ∀ a b, hq sig G.Hm (Y a) (Y b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.2.1 a b, map_zero]
  set Bad : Set (HeightOneSpectrum (𝓞 F)) :=
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p} ∪
    {p | A.lat p Λ ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep))} ∪
    {p | n p • A.lat p Λ ≠ A.lat p Λ} ∪
    (⋃ i, ⋃ j, {p | (A.loc p).ιE (G.Hm i j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}) with hBad
  have hlatP := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hBadF : Bad.Finite := by
    have hi := (PlacesInt.integers_local A).2.1
    refine ((((hc.union hlatP.2.2).union hn).union ?_).union ?_).union ?_ <;>
      exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => hi _
  have hgood : ∀ p, p ∉ Bad →
      (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p) ∧
      A.lat p Λ = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep)) ∧
      n p • A.lat p Λ = A.lat p Λ ∧ (∀ i j, (A.loc p).ιE (G.Hm i j) ∈ (A.L p).O) ∧
      (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) := by
    intro p hp
    refine ⟨Classical.byContradiction fun h => hp ?_, Classical.byContradiction fun h => hp ?_,
      Classical.byContradiction fun h => hp ?_, fun i j => Classical.byContradiction fun h => hp ?_,
      fun a j => Classical.byContradiction fun h => hp ?_, fun a j => Classical.byContradiction fun h => hp ?_⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, h⟩⟩)))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩))
    · exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩)
  have hstd : ∀ p, p ∉ Bad → ∀ x : Fin (k + 2 * r + 1) → (A.loc p).Ep,
      ((∀ j, (List.ofFn (ep p)).prod x j ∈ (A.L p).O) ↔ ∀ j, x j ∈ (A.L p).O) := by
    intro p hp x
    obtain ⟨-, hl, hnl, -⟩ := hgood p hp
    rw [← mem_coord (A.L p) ((List.ofFn (ep p)).prod x), ← mem_coord (A.L p) x, ← hl, ← hn_eq p]
    constructor
    · intro h
      rw [← hnl] at h
      obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      rw [LinearEquiv.smul_def] at hyx
      rwa [← (n p).injective hyx]
    · intro h
      rw [← hnl]
      exact Submodule.smul_mem_pointwise_smul _ _ _ h
  have hint : ∀ p, p ∉ Bad → (∀ i j, up p i j ∈ (A.L p).O) ∧ ∀ i, sp p i ∈ (A.L p).O := by
    intro p hp
    obtain ⟨-, -, -, hHm, hXi, hYi⟩ := hgood p hp
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianEichlerProduct_params_integral (A.L p) _ r (G.S p).Hm (G.S p).herm.1
      (fun i j => by rw [G.Hm_eq p]; exact hHm i j) (fun i => A.bc p (X i)) (fun i => A.bc p (Y i))
      (up p) (sp p) (ep p) (fun i j => hXi i j) (fun i j => hYi i j) (hR p).1 (hR p).2.1
      (fun i j hj => (hup p i).1 j hj) (fun i => (hup p i).2.1) (fun i v => (hup p i).2.2 v) (hstd p hp)
  have hdex : ∀ p, ∃ d : ((A.loc p).Fp)ˣ, (p ∉ Bad → d = 1) ∧
      ∀ (u' : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep) (s' : Fin r → (A.loc p).Ep)
        (e' : Fin r → (G.S p).GLV),
        (∀ i v, e' i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u' i) (s' i) v) →
        (∀ i j, ∃ o ∈ (A.L p).O, u' i j - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        (∀ i, ∃ o ∈ (A.L p).O, s' i - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, ((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x =
          algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    by_cases hp : p ∈ Bad
    · obtain ⟨d, hd⟩ := GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice (A.L p) (k + 2 * r + 1) r (G.S p).Hm (fun i => A.bc p (X i))
        (up p) (sp p) (ep p) (fun i v => (hup p i).2.2 v) (A.lat p Λ) (hlatP.2.1 p) (c p)
      exact ⟨d, fun h => absurd hp h, hd⟩
    · refine ⟨1, fun _ => rfl, ?_⟩
      intro u' s' e' he' hu' hs' x hx
      obtain ⟨⟨cu, hcu⟩, hl, -, hHm, hXi, -⟩ := hgood p hp
      obtain ⟨hui, hsi⟩ := hint p hp
      have hu'i : ∀ i j, u' i j ∈ (A.L p).O := fun i j => by
        obtain ⟨o, ho, h⟩ := hu' i j
        have h' : u' i j - up p i j = o := by simpa using h
        rw [show u' i j = up p i j + o by rw [← h']; ring]
        exact add_mem (hui i j) ho
      have hs'i : ∀ i, s' i ∈ (A.L p).O := fun i => by
        obtain ⟨o, ho, h⟩ := hs' i
        have h' : s' i - sp p i = o := by simpa using h
        rw [show s' i = sp p i + o by rw [← h']; ring]
        exact add_mem (hsi i) ho
      have hHm' : ∀ i j, (G.S p).Hm i j ∈ (A.L p).O := fun i j => by rw [G.Hm_eq p]; exact hHm i j
      have hx' : ∀ j, x j ∈ (A.L p).O := (mem_coord (A.L p) x).1 (hl ▸ hx)
      have hz := int_prod (A.L p) hHm' r (fun i => A.bc p (X i)) u' s' e' (fun i j => hXi i j) hu'i hs'i
        he' x hx'
      have hw := (hstd p hp (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x))).1
        (by rw [LinearEquiv.apply_symm_apply]; exact hz)
      have hci : algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) ∈ (A.L p).O := by
        have : (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = ((cu⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) := by
          rw [Units.val_inv_eq_inv_val, ← hcu, eq_comm]
          apply eq_inv_of_mul_eq_one_left
          exact_mod_cast Units.inv_mul cu
        rw [this]
        exact algebraMap_integer_mem_O (A.L p) _
      refine ⟨algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) •
        (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x), ?_, ?_⟩
      · rw [hl]
        refine (mem_coord (A.L p) _).2 fun j => ?_
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        exact mul_mem hci (sub_mem (hw j) (hx' j))
      · rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  choose d hd1 hd2 using hdex
  have hQex : ∀ i : Fin r, ∃ (u : Fin (k + 2 * r + 1) → E) (s : E),
      (∀ a ∈ (Finset.univ.filter fun j : Fin r => j ≤ i),
        hq sig G.Hm u (X a) = 0 ∧ hq sig G.Hm u (Y a) = 0) ∧ s + sig s = hq sig G.Hm u u ∧
      ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o) ∧
        ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro i
    refine GlobalTheory.T.hermitian_symplectic_basis_local_extension A (k + 2 * r + 1) r G.Hm hH X Y (Finset.univ.filter fun j : Fin r => j ≤ i)
      hXY hXX hYY (fun p => up p i) (fun p => sp p i) (fun p a ha => ?_) (fun p => ?_) ?_ d ?_
    · have h := (hup p i).1 a (Finset.mem_filter.1 ha).2
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · have h := (hup p i).2.1
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨fun j => (hint p hpb).1 i j, (hint p hpb).2 i⟩
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨1, by rw [hd1 p hpb]; simp⟩
  choose uQ sQ hQ using hQex
  have hinjQ : ∀ i, Function.Injective (eQ sig G.Hm (X i) (uQ i) (sQ i)) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : v + hq sig G.Hm v (uQ i) • X i - hq sig G.Hm v (X i) • (uQ i + sQ i • X i) = 0 := hv
    have hii : i ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp
    have hux : hq sig G.Hm (uQ i) (X i) = 0 := ((hQ i).1 i hii).1
    have hxu : hq sig G.Hm (X i) (uQ i) = 0 := by rw [hqsym, hux, map_zero]
    have hb : hq sig G.Hm v (X i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (X i)) hv'
      have hz0 : hq sig G.Hm 0 (X i) = 0 := by simp [hq]
      simp only [hq_sub_left, hq_add_l, hq_smul_l, hux, hXX i i, hz0] at h
      simpa using h
    rw [hb, zero_smul, sub_zero] at hv'
    have hv2 : v = -(hq sig G.Hm v (uQ i) • X i) := eq_neg_of_add_eq_zero_left hv'
    have ha : hq sig G.Hm v (uQ i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (uQ i)) hv2
      simp only [hq_neg_left, hq_smul_l, hxu, mul_zero, neg_zero] at h
      exact h
    rw [hv2, ha, zero_smul, neg_zero]
  let eR : Fin r → G.GLV := fun i => LinearEquiv.ofInjectiveEndo (eQ sig G.Hm (X i) (uQ i) (sQ i)) (hinjQ i)
  have heR : ∀ i v, eR i v = eQ sig G.Hm (X i) (uQ i) (sQ i) v := fun i v => by
    simp only [eR, LinearEquiv.coe_ofInjectiveEndo]
  have hext : ∀ p i, ∃ e' : (G.S p).GLV, A.Ext p (eR i) e' ∧ ∀ v, e' v =
      eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) v := by
    intro p i
    obtain ⟨e', he', -⟩ := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 (eR i)
    refine ⟨e', he', fun v => ?_⟩
    let M : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep) :=
      { toFun := fun w => eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) w
        map_add' := fun a b => by
          simp only [eich, hf_add_left_flag_measures']
          module
        map_smul' := fun t a => by
          simp only [eich, hf_smul_left_flag_measures', RingHom.id_apply]
          module }
    have hlin := RatExt.lin_ext (A.loc p).ιE (e' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] _) M
      (fun x => by
        show e' (A.bc p x) = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) (A.bc p x)
        rw [he' x, heR, bc_eQ, G.Hm_eq p])
    exact LinearMap.congr_fun hlin v
  choose eL heL heL' using hext
  have hmem : ∀ p, (List.ofFn (eL p)).prod ∈ (G.S p).Nof (gF p) := by
    intro p
    refine ((hR p).2.2.2 _).2 ⟨fun i => A.bc p (uQ i), fun i => (A.loc p).ιE (sQ i), eL p,
      fun i => ⟨fun j hj => ?_, ?_, heL' p i⟩, rfl⟩
    · have hj' : j ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp [hj]
      rw [hform, hform, ((hQ i).1 j hj').1, ((hQ i).1 j hj').2, map_zero]
      exact ⟨rfl, rfl⟩
    · rw [hform, ← (hQ i).2.1, map_add, hconj]
  refine ⟨(List.ofFn eR).prod, fun p => ⟨_, hmem p, ext_prod A p r eR (eL p) (heL p)⟩, ?_⟩
  intro p g' hg' x hx
  have hg'eq : g' = (List.ofFn (eL p)).prod :=
    ((RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 ((List.ofFn eR).prod)).unique hg'
      (ext_prod A p r eR (eL p) (heL p))
  rw [hg'eq, hn_eq p]
  exact hd2 p (fun i => A.bc p (uQ i)) (fun i => (A.loc p).ιE (sQ i)) (eL p) (heL' p)
    (fun i j => ((hQ i).2.2 p).1 j) (fun i => ((hQ i).2.2 p).2) x hx

theorem strong_approximation_unipotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c hc n hn
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f) (fun p => (G.S p).es)
      (fun a => G.f a.castSucc) G.es (fun _ => Or.inl ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es_eq p a) hN
    exact ⟨g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f') (fun p => (G.S p).es')
      (fun a => G.f' a.castSucc) G.es' (fun _ => Or.inr ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f'_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es'_eq p a) hN
    exact ⟨g, hg1, hg2⟩

end GlobalTheory.HL.SAN
