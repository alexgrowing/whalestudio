import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExists

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Twist GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.QCoh

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

def coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ a ∈ g.support, monomial a (l (coeff a g))

theorem coeff_coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) (a : σ →₀ ℕ) :
    coeff a (coeffMap l g) = l (coeff a g) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem isHomogeneous_coeffMap (l : K →ₗ[k] k) {g : MvPolynomial σ K} {d : ℕ} (hg : g.IsHomogeneous d) :
    (coeffMap l g).IsHomogeneous d := fun a ha =>
  hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])

theorem mem_map_of_coeffMap {I : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ K}
    (h : ∀ l : K →ₗ[k] k, coeffMap l g ∈ I) :
    g ∈ I.map (MvPolynomial.map (algebraMap k K) : MvPolynomial σ k →+* MvPolynomial σ K) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let s := g.support.biUnion fun a => (b.repr (coeff a g)).support
  have e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g) := by
    ext a
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]
    have hs : (b.repr (coeff a g)).support ⊆ s := by
      by_cases ha : a ∈ g.support
      · exact Finset.subset_biUnion_of_mem (fun a => (b.repr (coeff a g)).support) ha
      · simp [notMem_support_iff.1 ha]
    conv_lhs => rw [← b.linearCombination_repr (coeff a g),
      Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

theorem le_of_ringKrullDim_coneIdeal {N D e : ℕ} (y : Fin N → K) (hD : Algebra.trdeg k K = D)
    (he : ringKrullDim (MvPolynomial (Fin N) k ⧸ coneIdeal k y) = (e + 1 : ℕ)) : e ≤ D := by
  have := isPrime_coneIdeal (K := k) y
  obtain ⟨d, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)
  obtain rfl : d = e + 1 := by exact_mod_cast h1.symm.trans he
  have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)
  rw [← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD] at h3
  have h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0}) := by
    rw [← h2, Nat.cast_add, Nat.cast_one]; exact h3
  have : e + 1 ≤ D + 1 := by exact_mod_cast h4
  omega

end Algebra

variable {k : Type} [Field k] (S : LinSys k)

theorem chartEval_eq_zero {g : MvPolynomial (Fin S.N) k} {d : ℕ} (hg : g.IsHomogeneous d) (h : g ∈ S.imageIdeal)
    (i : S.L.ι) {W : S.Y.Opens} (hle : W ≤ S.L.U i) : chartEval k S.b i hle g = 0 := by
  have e : resG _ hle (zfun (S.form hg) i) = 0 := by
    rw [(S.mem_imageIdeal_iff hg).1 h]
    exact (congrArg _ (zfun_zero i)).trans (map_zero _)
  rwa [LinSys.form, zfun_formSec, resG_chartEval] at e

theorem coeffMap_mem_imageIdeal (E : Type) [Field E] [Algebra k E] {g : MvPolynomial (Fin S.N) E} {d : ℕ}
    (hg : g.IsHomogeneous d) (h : g ∈ (S.baseChange E).imageIdeal) (l : E →ₗ[k] k) :
    coeffMap l g ∈ S.imageIdeal := by
  refine (S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)
  rw [zfun_zero, LinSys.form, zfun_formSec]
  refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
    (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
  obtain ⟨⟨W, hW⟩, hle⟩ := W
  have H := S.isPullback_baseChange E
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
    (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
      (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Λ, hΛ⟩ := IndepBaseChange.exists_contract po' l
  have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => hle hy
  have e := (eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')
  have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
      ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
    have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
      (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
    have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
    exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
  have e₂ := congrArg Λ e
  rw [map_zero, map_sum] at e₂
  refine (resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))
  rw [coeffMap, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartEval, eval₂Hom_monomial]
  refine Eq.trans (hΛ (coeff a g) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)
  refine congrArg₂ (· * ·) rfl ?_
  refine (map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans
    (Finset.prod_congr rfl fun j _ => ?_)
  exact (map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)

theorem del_eq_zero (hp : IsProjOver S.str) (s : Fin S.D → S.L.Sec) (hs : ∀ y, ∃ i, y ∈ nonzeroLocus (s i)) :
    S.del = 0 := by
  have := isNoetherian_of_isProjOver hp
  have key := CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s)
    (structureModule S.Y) (fun x _ hx => by
      obtain ⟨i, hi⟩ := hs x
      exact (hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)
  have e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length := by rw [List.length_ofFn]
  rw [LinSys.del, e, topSelf_def]
  exact key

variable {S}

theorem isIntegral (h : S.IsVariety) : IsIntegral S.Y := by
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  have := geometricallyIntegral_of_smooth S.str
  exact GeometricallyIntegral.isIntegral_of_subsingleton S.str

theorem exists_generic (h : S.IsVariety) : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra k Ω) (x : S.Pt Ω),
    IsGenericPoint (ptOf x.1) Set.univ ∧ Algebra.trdeg k Ω = S.D := by
  have := isIntegral h
  have hg := genericPoint_spec S.Y
  refine ⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra,
    ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩
  exact (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _
    fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2

theorem map_imageIdeal (h : S.IsVariety) (E : Type) [Field E] [Algebra k E] :
    S.imageIdeal.map (MvPolynomial.map (algebraMap k E) : MvPolynomial (Fin S.N) k →+* MvPolynomial (Fin S.N) E) =
      (S.baseChange E).imageIdeal := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · have := isIntegral (h.baseChange E)
    obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic (h.baseChange E)
    let : Algebra k Ω := ((algebraMap E Ω).comp (algebraMap k E)).toAlgebra
    have : IsScalarTower k E Ω := .of_algebraMap_eq' rfl
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E x.1
    rw [imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro g ⟨d, hg, h0⟩
    refine (mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_
    have h1 := S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)
    rw [LinSys.baseHom_ptOver] at h1
    exact (aeval_map_algebraMap E _ g).trans h1
  · rintro g ⟨d, hg, h0⟩
    exact mem_map_of_coeffMap
      (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))

theorem isPrime_imageIdeal (h : S.IsVariety) : S.imageIdeal.IsPrime := by
  have := isIntegral h
  obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic h
  rw [imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]
  exact isPrime_coneIdeal _

theorem del_eq_zero_of_lt [Infinite k] (hp : IsProjOver S.str) (hb : S.BasePointFree) {e δ : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin S.N) k} (hf : IsChowFormInt S.imageIdeal e δ f) (he : e < S.D) :
    S.del = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])
  refine del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_
  by_contra hc
  push Not at hc
  let Ω := AlgebraicClosure (S.Y.residueField y)
  let x : Sp Ω ⟶ S.Y := spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y
  have hx : ptOf x = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  let : Algebra k Ω := (S.baseHom x).toAlgebra
  have h1 := (hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2
    ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by
      have h2 := hc ⟨i, by omega⟩
      rw [dif_pos i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb] at h2
      exact h2⟩
  exact hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))

theorem ringKrullDim_imageIdeal [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  have := isIntegral h
  have hp := isPrime_imageIdeal h
  obtain ⟨Ω, _, _, x, hx, hD⟩ := exists_generic h
  have hI := imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j)
    fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  obtain ⟨f, hf⟩ := ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he
  obtain rfl : e = S.D := le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he))
    (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))
  exact he

theorem exists_isChowForm [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ∃ f, IsChowForm S.imageIdeal S.D (hilbertDegree S.imageIdeal) f :=
  ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal
    (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)

theorem exists_isHeight : ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F),
    T.IsAlgebraicData → 0 < T.del → ∃ h, T.IsHeight h := fun _ _ _ T h hd =>
  have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne'
  ⟨_, T.isHeight_of_isChowForm hf⟩

end GlobalTheory.Adelic.HeightExists
