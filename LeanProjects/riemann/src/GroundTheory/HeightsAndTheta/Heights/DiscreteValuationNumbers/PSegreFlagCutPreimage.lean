import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutPreimage
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSectionTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor SegreFlagCutChartSection

noncomputable section

set_option linter.unusedSectionVars false

namespace SegreFlagCutPreimage

section General

theorem alg_eq_of_support {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (α β : MvPolynomial σ R →ₐ[R] A) (G : MvPolynomial σ R)
    (h : ∀ m ∈ G.support, ∀ p ∈ m.support, α (X p) = β (X p)) : α G = β G := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_eq, Finsupp.prod, map_mul, map_mul, map_prod, map_prod]
  congr 1
  · show α (algebraMap R _ (coeff m G)) = β (algebraMap R _ (coeff m G))
    rw [α.commutes, β.commutes]
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_pow, map_pow, h m hm p hp]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type} [CommRing R]

theorem le_of_mem_support {G : MRing ι R} {b : K → ℕ} (hG : IsMultiHomog G b) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ G.support) (p : Σ k, ι k) : m p ≤ b p.1 := by
  have hw : Finsupp.weight (blockWeight ι) m = b := hG (mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hp : p ∈ m.support
  · refine le_trans ?_ (Finset.single_le_sum (f := fun v => (m v • blockWeight ι v) p.1)
      (fun _ _ => Nat.zero_le _) hp)
    simp [blockWeight]
  · have : m p = 0 := by simpa using hp
    rw [this]
    exact Nat.zero_le _

theorem sub_mem_of_homog {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {z : (Σ k, ι k) → Φ}
    {f g : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b)
    (hv : aeval z f = aeval z g) : f - g ∈ pointIdeal O z := by
  refine mem_of_homog (b := b) ?_ (by rw [map_sub, hv, sub_self])
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg))

end General

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem aeval_vdeg_indep (y : (Σ k, ι k) → Ω) (e e' : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t t' : Fin N → Φ)
    {U : MRing (bundleIdx (bundleIdx ι M) M') O} {α : K → ℕ} (hU : IsMultiHomog U (vdeg α)) :
    aeval (pairProjCoord y e φ φ' t) U = aeval (pairProjCoord y e' φ φ' t') U := by
  refine alg_eq_of_support _ _ U fun m hm p hp => ?_
  have hle := le_of_mem_support hU hm p
  have hp0 : m p ≠ 0 := Finsupp.mem_support_iff.mp hp
  rcases p with ⟨_ | _ | k, j⟩
  · simp [vdeg] at hle
    omega
  · simp [vdeg] at hle
    omega
  · rw [aeval_X, aeval_X]
    rfl

theorem express_family (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (ϖ : O) {J L : ℕ} (ψ : Fin L → Module.Dual Ω E) (χ : Fin J → Module.Dual Ω E)
    (a a' : K → ℤ) (n : ℕ) (r : Fin J → Fin L → Ω) (hr : ∀ i l, r i l ∈ chartRing O (segreVec y) c)
    (h : ∀ i, algebraMap O Ω ϖ ^ n • χ i = ∑ l, (r i l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • ψ l) :
    ∃ (bG bH : K → ℕ) (G : Fin J → Fin L → MRing (bundleIdx (bundleIdx ι M) M') O),
      (∀ i l, IsMultiHomog (G i l) (vdeg bG)) ∧ (∀ k, (bG k : ℤ) - bH k = a' k - a k) ∧
      ∀ (s : Fin N → Φ) (i : Fin J),
        aeval (pairProjCoord y w φ φ' s) (C (ϖ ^ n) * chartMonoZ O M M' c bH) * genVal w s (χ i) =
          ∑ l, aeval (pairProjCoord y w φ φ' s) (G i l) * genVal w s (ψ l) := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  obtain ⟨n₀, U, hU⟩ := chart_forms_uniform (O := O) (M := M) (M' := M') y w φ φ' (0 : Fin N → Φ) c hc
    (fun p : Fin (J * L) => r (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) (fun p => hr _ _)
  have hUs : ∀ (s : Fin N → Φ) i l, aeval (pairProjCoord y w φ φ' s) (U (finProdFinEquiv (i, l))) =
      algebraMap Ω Φ (r i l * segreVec y c ^ n₀) := by
    intro s i l
    rw [aeval_vdeg_indep y w w φ φ' s 0 (hU _).1, (hU _).2]
    simp
  let A : K → ℕ := fun k => (a' k - a k).toNat
  let B : K → ℕ := fun k => (a k - a' k).toNat
  have hAB : ∀ k, ((n₀ + B k : ℕ) : ℤ) + (a' k - a k) = (n₀ : ℤ) + (A k : ℤ) := by
    intro k
    simp only [A, B]
    omega
  refine ⟨fun k => n₀ + A k, fun k => n₀ + B k,
    fun i l => U (finProdFinEquiv (i, l)) * chartMonoZ O M M' c A, fun i l => ?_, fun k => ?_, ?_⟩
  · have hv : vdeg (K := K) (fun k => n₀ + A k) = vdeg (fun _ => n₀) + vdeg A := vdeg_add _ _
    rw [hv]
    exact IsWeightedHomogeneous.mul (hU _).1 (chartMonoZ_homog c A)
  · have := hAB k
    push_cast at this ⊢
    linarith
  · intro s i
    have hk : ∀ k, y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k) =
        y ⟨k, c k⟩ ^ n₀ * y ⟨k, c k⟩ ^ A k := by
      intro k
      rw [← zpow_natCast (y _) (n₀ + B k), ← zpow_add₀ (hy k), hAB k, zpow_add₀ (hy k), zpow_natCast,
        zpow_natCast]
    have key : (algebraMap O Ω ϖ ^ n * ∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) • χ i =
        ∑ l, (r i l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k) • ψ l := by
      rw [mul_comm, ← smul_smul, h i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul]
      congr 1
      calc (∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) * (r i l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k))
          = r i l * ∏ k, (y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k)) := by
            rw [Finset.prod_mul_distrib]
            ring
        _ = r i l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k := by
            simp_rw [hk]
            rw [Finset.prod_mul_distrib, Finset.prod_pow, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl]
            ring
    have hval := congrArg (genVal w s) key
    rw [genVal_smul, genVal_sum_smul] at hval
    rw [map_mul, aeval_C, aeval_chartMonoZ, map_pow, IsScalarTower.algebraMap_apply O Ω Φ, ← map_pow,
      ← map_mul, hval]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul (aeval (pairProjCoord y w φ φ' s)) (U (finProdFinEquiv (i, l))), hUs s i l, aeval_chartMonoZ,
      map_mul (algebraMap Ω Φ) (r i l * segreVec y c ^ n₀)]

end Forms

section Subst

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {O : Type} [CommRing O]
  {M M' : ℕ}

def substPhi (L : Fin M → MRing (bundleIdx (bundleIdx ι M) M') O) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → MRing (bundleIdx (bundleIdx ι M) M') O
  | ⟨some none, i⟩ => L i
  | p => X p

def dropPhi (O : Type) [CommRing O] :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) →
      MvPolynomial (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O
  | ⟨none, l⟩ => X ⟨none, l⟩
  | ⟨some none, _⟩ => 0
  | ⟨some (some k), j⟩ => X ⟨some k, j⟩

theorem rename_dropPhi (p : Σ o, bundleIdx (bundleIdx ι M) M' o) (hp : p.1 ≠ some none) :
    rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M'))
      (aeval (dropPhi (ι := ι) (M := M) (M' := M') O) (X p : MRing (bundleIdx (bundleIdx ι M) M') O)) =
        (X p : MRing (bundleIdx (bundleIdx ι M) M') O) := by
  rcases p with ⟨_ | _ | k, j⟩
  · rw [aeval_X]
    simp only [dropPhi, rename_X]
    rfl
  · exact absurd rfl hp
  · rw [aeval_X]
    simp only [dropPhi, rename_X]
    rfl

theorem core {Φ : Type} [Field Φ] [Algebra O Φ] (P Q : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ)
    (L : Fin M → MRing (bundleIdx (bundleIdx ι M) M') O) (H : MRing (bundleIdx (bundleIdx ι M) M') O)
    (δ : Option (Option K) → ℕ) (hδ : δ (some none) = 0) (hL : ∀ i, IsMultiHomog (L i) δ)
    (hQ : ∀ i, aeval Q (L i) = aeval Q H * Q ⟨some none, i⟩) (i₀ : Fin M)
    (hrel : ∀ i, L i₀ * X ⟨some none, i⟩ - X ⟨some none, i₀⟩ * L i ∈ pointIdeal O P) :
    ∀ q ∈ pointIdeal O Q, ∃ n : ℕ, L i₀ ^ n * q ∈ pointIdeal O P ⊔
      (pointIdeal O (fun p => Q (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M') p))).map
        (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M'))) := by
  classical
  set f := FieldNumbers.blockIncl (secondFactorBlocks (K := K)) (bundleIdx (bundleIdx ι M) M') with hf
  set A := pointIdeal O P ⊔ (pointIdeal O (fun p => Q (f p))).map (rename f) with hA

  have hfree : ∀ i, rename f (aeval (dropPhi O) (L i)) = L i := by
    intro i
    have := alg_eq_of_support ((rename f).comp (aeval (dropPhi O))) (AlgHom.id O _) (L i)
      (fun m hm p hp => by
        have hle := le_of_mem_support (hL i) hm p
        have hp0 : m p ≠ 0 := Finsupp.mem_support_iff.mp hp
        have hne : p.1 ≠ some none := fun h => by
          rw [h, hδ] at hle
          omega
        rw [AlgHom.comp_apply, AlgHom.id_apply]
        exact rename_dropPhi p hne)
    simpa using this

  let Λ₁ : Option (Option K) → Option (Option K) → ℕ := fun o => if o = some none then δ else Pi.single o 1
  let Λ : (Option (Option K) → ℕ) →+ (Option (Option K) → ℕ) :=
    { toFun := fun d => ∑ o, d o • Λ₁ o
      map_zero' := by simp
      map_add' := fun d d' => by simp [add_smul, Finset.sum_add_distrib] }
  have hΛ : ∀ v : Σ o, bundleIdx (bundleIdx ι M) M' o, Λ (blockWeight _ v) = Λ₁ v.1 := by
    intro v
    simp only [Λ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, blockWeight]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hgh : ∀ v, IsWeightedHomogeneous (blockWeight _) (substPhi L v) (Λ (blockWeight _ v)) := by
    intro v
    rw [hΛ]
    rcases v with ⟨_ | _ | k, j⟩
    · simp only [Λ₁, substPhi, if_neg (show (none : Option (Option K)) ≠ some none by simp)]
      exact isWeightedHomogeneous_X O _ _
    · simp only [Λ₁, substPhi, if_pos rfl]
      exact hL j
    · simp only [Λ₁, substPhi, if_neg (show some (some k) ≠ some none by simp)]
      exact isWeightedHomogeneous_X O _ _

  have hform : ∀ (b : Option (Option K) → ℕ) (q : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsMultiHomog q b → q ∈ pointIdeal O Q → L i₀ ^ b (some none) * q ∈ A := by
    intro b q hqb hqQ
    have hσ : bind₁ (substPhi L) q ∈ pointIdeal O Q := by
      refine mem_of_homog (bind₁_isMultiHomog_of Λ _ hgh hqb) ?_
      rw [aeval_bind₁]
      have hfun : (fun p => aeval Q (substPhi L p)) =
          fun p => aeval Q (H ^ blockWeight (bundleIdx (bundleIdx ι M) M') p (some none) * X p) := by
        funext p
        rcases p with ⟨_ | _ | k, j⟩
        · simp [substPhi, blockWeight]
        · simp only [substPhi, blockWeight, Pi.single_eq_same, pow_one, map_mul, aeval_X]
          exact hQ j
        · simp [substPhi, blockWeight]
      rw [hfun, ← aeval_bind₁, bind₁_scale_of (some none) H X hqb, bind₁_X_left, AlgHom.id_apply, map_mul,
        aeval_eq_zero_of_mem hqQ, mul_zero]
    have e1 := bind₁_scale_of (some none) (L i₀) X hqb
    rw [bind₁_X_left, AlgHom.id_apply] at e1
    have e2 := bind₁_scale_of (some none) (X ⟨some none, i₀⟩) (substPhi L) hqb
    have h1 : L i₀ ^ b (some none) * q - X ⟨some none, i₀⟩ ^ b (some none) * bind₁ (substPhi L) q ∈
        pointIdeal O P := by
      rw [← e1, ← e2]
      refine bind₁_sub_mem_of _ _ _ (fun v => ?_) q
      rcases v with ⟨_ | _ | k, j⟩
      · simp [substPhi, blockWeight]
      · simpa [substPhi, blockWeight] using hrel j
      · simp [substPhi, blockWeight]
    have heq : rename f (aeval (dropPhi O) (bind₁ (substPhi L) q)) = bind₁ (substPhi L) q := by
      have hh : ((rename f).comp ((aeval (dropPhi O)).comp (bind₁ (substPhi L)))) = bind₁ (substPhi L) := by
        apply MvPolynomial.algHom_ext
        intro p
        rw [AlgHom.comp_apply, AlgHom.comp_apply, bind₁_X_right]
        rcases p with ⟨_ | _ | k, j⟩
        · exact rename_dropPhi _ (by simp)
        · exact hfree j
        · exact rename_dropPhi _ (by simp)
      exact congrArg (fun φ => φ q) hh
    have h2 : bind₁ (substPhi L) q ∈ (pointIdeal O (fun p => Q (f p))).map (rename f) := by
      rw [← heq]
      refine Ideal.mem_map_of_mem _ ?_
      rw [← comap_pointIdeal_blockIncl, Ideal.mem_comap, heq]
      exact hσ
    have h3 := A.add_mem (Ideal.mem_sup_left h1)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ (X ⟨some none, i₀⟩ ^ b (some none)) h2))
    rwa [sub_add_cancel] at h3
  intro q hq
  have hsat : ∀ b, ∃ n : ℕ, L i₀ ^ n *
      weightedHomogeneousComponent (blockWeight (bundleIdx (bundleIdx ι M) M')) b q ∈ A := fun b =>
    ⟨_, hform b _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (isMultiHomogIdeal_pointIdeal Q q hq b)⟩
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (Option (Option K) → ℕ),
      q = ∑ b ∈ S, weightedHomogeneousComponent (blockWeight (bundleIdx (bundleIdx ι M) M')) b q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (bundleIdx (bundleIdx ι M) M')) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (bundleIdx (bundleIdx ι M) M')) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ b ∈ S, nn b, ?_⟩
  rw [hS, Finset.mul_sum]
  refine Ideal.sum_mem _ fun b hb => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hb), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn b)

end Subst

end SegreFlagCutPreimage

open SegreFlagCutPreimage in

theorem SegreFlagCutPreimage.proof : SegreFlagCutPreimage.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f₀ g₀ hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk W hW hWr hPW hϖW
  classical
  have hexp := TwistedDualGensExpress.proof

  obtain ⟨c, hc⟩ : ∃ c : ∀ j, ι j,
      ∀ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W :=
    ⟨fun j => (hWr (some (some j))).choose, fun j => (hWr (some (some j))).choose_spec⟩
  obtain ⟨l₀, hl₀⟩ := hWr none
  have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
    intro j h0
    refine hc j (hPW (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
    rw [aeval_X]
    show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
    rw [h0, map_zero]
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => nz j
  have hmono : ∀ (n : ℕ) (α : K → ℕ), (C (ϖ ^ n) * chartMonoZ O M M' c α) ∉ W := by
    intro n α hm
    rcases hW.mem_or_mem hm with h | h
    · rw [map_pow] at h
      exact hϖW (hW.mem_of_pow_mem n h)
    · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hc j (hW.mem_of_pow_mem _ hj)

  choose nI rI hrI hxI using fun i : Fin M => hexp O ϖ Ω K ι y N E B' B
    (fun c hc => ⟨(hB c hc).2, (hB c hc).1⟩) a₀' a₀ M' M φ' φ hφ' hφ c hyc i
  set n := ∑ i, nI i with hn
  have hle : ∀ i, nI i ≤ n := fun i =>
    Finset.single_le_sum (f := nI) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hxU : ∀ i, algebraMap O Ω ϖ ^ n • φ i =
      ∑ l, ((algebraMap O Ω ϖ ^ (n - nI i) * rI i l) * ∏ j, y ⟨j, c j⟩ ^ (a₀ j - a₀' j)) • φ' l := by
    intro i
    have h := congrArg (fun v => algebraMap O Ω ϖ ^ (n - nI i) • v) (hxI i)
    simp only [smul_smul, ← pow_add, Nat.sub_add_cancel (hle i), Finset.smul_sum] at h
    rw [h]
    exact Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
  have hr' : ∀ i l, algebraMap O Ω ϖ ^ (n - nI i) * rI i l ∈ chartRing O (segreVec y) c := fun i l =>
    mul_mem (pow_mem (Subalgebra.algebraMap_mem _ ϖ) _) (hrI i l)
  obtain ⟨bG, bH, G, hG, hdeg, hval⟩ := express_family (O := O) (M := M) (M' := M') (Φ := Φ) y w φ φ' c hyc ϖ
    φ' φ a₀' a₀ n _ hr' hxU

  obtain ⟨n', r'', hr'', hx''⟩ := hexp O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc l₀
  obtain ⟨bG', bH', G', hG', hdeg', hval'⟩ := express_forms (M := M) (M' := M') y w φ φ'
    (flagCoord w e t (k + 1)) c hyc ϖ φ (φ' l₀) a₀ a₀' n' r'' hr'' hx''
  obtain ⟨L, hLdef⟩ : ∃ L : Fin M → MRing (bundleIdx (bundleIdx ι M) M') O,
      ∀ i, L i = ∑ l, X (⟨none, l⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) * G i l := ⟨_, fun _ => rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : Option (Option K) → ℕ, δ = Pi.single none 1 + vdeg bG := ⟨_, rfl⟩
  have hL : ∀ i, IsMultiHomog (L i) δ := fun i => by
    rw [hLdef, hδdef]
    exact IsWeightedHomogeneous.sum _ _ _ fun l _ => (isWeightedHomogeneous_X O
      (blockWeight (bundleIdx (bundleIdx ι M) M')) (⟨none, l⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)).mul (hG i l)
  have hLval : ∀ (s : Fin N → Φ) i, aeval (pairProjCoord y w φ φ' s) (L i) =
      aeval (pairProjCoord y w φ φ' s) (C (ϖ ^ n) * chartMonoZ O M M' c bH) * genVal w s (φ i) := by
    intro s i
    rw [hval s i, hLdef, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, aeval_X, mul_comm]
    rfl

  have hsum : ∑ i, L i * G' i - X ⟨none, l₀⟩ * (C (ϖ ^ n') * chartMonoZ O M M' c bH') *
      (C (ϖ ^ n) * chartMonoZ O M M' c bH) ∈
      pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
    refine sub_mem_of_homog (b := δ + vdeg bG')
      (IsWeightedHomogeneous.sum _ _ _ fun i _ => (hL i).mul (hG' i)) ?_ ?_
    · have h1 := ((isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M'))
        (⟨none, l₀⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)).mul ((isWeightedHomogeneous_C _ (ϖ ^ n')).mul
          (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH'))).mul
        ((isWeightedHomogeneous_C _ (ϖ ^ n)).mul (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))
      have hd : δ + vdeg bG' = blockWeight (bundleIdx (bundleIdx ι M) M')
          (⟨none, l₀⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) + (0 + vdeg bH') + (0 + vdeg bH) := by
        rw [hδdef]
        funext o
        rcases o with _ | _ | j
        · simp [vdeg, blockWeight]
        · simp [vdeg, blockWeight]
        · simp [vdeg, blockWeight]
          have := hdeg j
          have := hdeg' j
          omega
      rw [IsMultiHomog, hd]
      exact h1
    · show aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) _ =
        aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) _
      have hterm : ∀ i, aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (L i * G' i) =
          aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (C (ϖ ^ n) * chartMonoZ O M M' c bH) *
            (aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (G' i) *
              genVal w (flagCoord w e t (k + 1)) (φ i)) := by
        intro i
        rw [map_mul, hLval]
        ring
      rw [map_sum, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, ← hval']
      simp only [map_mul, aeval_X]
      change _ = genVal w (flagCoord w e t (k + 1)) (φ' l₀) * (_ * _) * (_ * _)
      ring
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, L i₀ ∉ W := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h1 : ∑ i, L i * G' i ∈ W := W.sum_mem fun i _ => W.mul_mem_right _ (hall i)
    have h2 := W.sub_mem h1 (hPW hsum)
    rw [sub_sub_cancel] at h2
    rcases hW.mem_or_mem h2 with h3 | h3
    · rcases hW.mem_or_mem h3 with h4 | h4
      · exact hl₀ h4
      · exact hmono n' bH' h4
    · exact hmono n bH h3
  refine ⟨L i₀, hi₀, ?_⟩
  refine core (flagClosurePt y w e φ φ' t (k + 1)) (flagClosurePt y w e φ φ' t k) L
    (C (ϖ ^ n) * chartMonoZ O M M' c bH) δ ?_ hL ?_ i₀ ?_
  · simp [hδdef, vdeg]
  · intro i
    exact hLval (flagCoord w e t k) i
  · intro i
    refine sub_mem_of_homog (b := δ + Pi.single (some none) 1) ((hL i₀).mul (isWeightedHomogeneous_X O _ _)) ?_ ?_
    · rw [add_comm]
      exact (isWeightedHomogeneous_X O _ _).mul (hL i)
    · show aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) _ =
        aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) _
      rw [map_mul, map_mul, hLval, hLval, aeval_X, aeval_X]
      change _ * genVal w _ (φ i) = genVal w _ (φ i₀) * _
      ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
