import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

theorem gfp_li_tri {K : Type} [Field K] {m n : ℕ} (M : Fin m → Fin m → K) (hdiag : ∀ i, M i i = 1)
    (hlow : ∀ i j, j < i → M i j = 0) (e : Fin m → Fin n → K) (he : LinearIndependent K e) :
    LinearIndependent K (fun i => ∑ j, M i j • e j) := by
  classical
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  have hM : (Matrix.of M).det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j h; exact hlow i j h)]
    simp [hdiag]
  have hv : Matrix.vecMul g (Matrix.of M) = 0 := by
    have h0 : ∑ j, (Matrix.vecMul g (Matrix.of M) j) • e j = 0 := by
      rw [← hg]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    funext j
    exact he _ h0 j
  intro i
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero (by rw [hM]; exact one_ne_zero) hv) i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gfpSmooth {L : Type} [Field L] (x : Sp L ⟶ Xo.X) : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
  have := Xo.univ.t.semi.smooth
  show Smooth (pullback.snd Xo.univ.t.G.hom x)
  infer_instance

theorem gfp_xGen_over (Z : Comp Xo c) : xGen Z ≫ Xo.s = sOf c (kap Z) := by
  rw [xGen, Category.assoc, pullback.condition, sOf, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← Category.assoc]
  congr 1
  show genSp Z ≫ strK = Spec.map (CommRingCat.ofHom (algebraMap c.F (kap Z)))
  rw [← Spec.map_preimage (genSp Z ≫ strK)]
  rfl

theorem gfp_tower (Z : Comp Xo c) (r : c.F) :
    algebraMap c.F (Om Z) r = algebraMap (kap Z) (Om Z) (algebraMap c.F (kap Z) r) := by rfl

section Gen

variable {L L' : Type} [Field L] [Field L'] [Algebra c.F L] [Algebra c.F L'] [Algebra L L']

theorem gfp_over_bc (htow : ∀ r : c.F, algebraMap c.F L' r = algebraMap L L' (algebraMap c.F L r))
    {x : Sp L ⟶ Xo.X} (hx0 : x ≫ Xo.s = sOf c L) : (spMap (algebraMap L L') ≫ x) ≫ Xo.s = sOf c L' := by
  have h2 : (algebraMap L L').comp (algebraMap c.F L) = algebraMap c.F L' :=
    RingHom.ext fun r => (htow r).symm
  rw [Category.assoc, hx0, sOf, sOf, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← RingHom.comp_assoc, h2]

private theorem li_bc_lemma {K K' : Type} [Field K] [Field K'] [Algebra K K'] {m n : ℕ}
    (d : Fin m → Fin n → K) (hd : LinearIndependent K d) :
    LinearIndependent K' (fun i => algebraMap K K' ∘ d i) := by
  classical
  let A : Matrix (Fin m) (Fin n) K := Matrix.of d
  have hinj : Function.Injective fun v => Matrix.vecMul v A := Matrix.vecMul_injective_iff.2 hd
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear A)
    (LinearMap.ker_eq_bot.2 hinj)
  have key : ∀ v, Matrix.vecMul v (A * (LinearMap.toMatrix' g).transpose) = v := by
    intro v
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hg v
  have hAB : A * (LinearMap.toMatrix' g).transpose = 1 := by
    ext i j
    have := congrFun (key (Pi.single i 1)) j
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using this
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hAB' : A.map (algebraMap K K') * ((LinearMap.toMatrix' g).transpose).map (algebraMap K K') = 1 := by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : Matrix.vecMul w (A.map (algebraMap K K')) = 0 := by
    funext j
    have := congrFun hw j
    simpa [Matrix.vecMul, dotProduct, A, Finset.sum_apply] using this
  have hw' : w = Matrix.vecMul (Matrix.vecMul w (A.map (algebraMap K K')))
      (((LinearMap.toMatrix' g).transpose).map (algebraMap K K')) := by
    rw [Matrix.vecMul_vecMul, hAB', Matrix.vecMul_one]
  intro i
  rw [hw', hv, Matrix.zero_vecMul]
  rfl

theorem gfp_frPt_gen (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (htow : ∀ r : c.F, algebraMap c.F L' r = algebraMap L L' (algebraMap c.F L r))
    (x : Sp L ⟶ Xo.X) (hx0 : x ≫ Xo.s = sOf c L) (M : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → L')
    (hdiag : ∀ τ i, M τ i i = 1) (hlow : ∀ τ i j, j < i → M τ i j = 0) :
    ∃ (y₀ : FrPt Xo c L) (y : FrPt Xo c L'), y₀.x = x ∧ y.x = spMap (algebraMap L L') ≫ x ∧
      ∀ τ i, IsCombAt y.x (fun j => spMap (dualMap (algebraMap L L')) ≫ y₀.u τ j) (M τ i) (y.u τ i) := by
  classical
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨xc', hx', hvec, htmap⟩ := gfp_bc (L' := L') hx
  let bas : ∀ τ : E →+* ℂ, Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ) :=
    fun τ => Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)
  let d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L := fun τ i => (bas τ i : Fin n → L)
  have hd : ∀ τ, LinearIndependent L (d τ) := fun τ =>
    (bas τ).linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i => (bas τ i).2
  let d' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L' := fun τ i => algebraMap L L' ∘ d τ i
  have hd' : ∀ τ, LinearIndependent L' (d' τ) := fun τ => li_bc_lemma (d τ) (hd τ)
  have hdW' : ∀ τ i, d' τ i ∈ gfpEig (c := c) hx' τ := by
    intro τ i
    have h := hdW τ i
    simp only [gfpEig, ReciprocityTheory.ChartRestriction.G.Chart.eigLat, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
    intro a
    simp only [d']
    rw [htmap, h a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_mul, htow]
  let e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n → L' := fun τ i => ∑ j, M τ i j • d' τ j
  have heW : ∀ τ i, e τ i ∈ gfpEig (c := c) hx' τ := fun τ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hdW' τ j)
  have he : ∀ τ, LinearIndependent L' (e τ) := fun τ => gfp_li_tri (M τ) (hdiag τ) (hlow τ) (d' τ) (hd' τ)
  have hx0' := gfp_over_bc htow hx0
  refine ⟨⟨x, hx0, fun τ i => gfpVec x xc (d τ i), fun τ i => gfp_tan hx _,
      fun τ i => (gfp_eig_iff hx τ _).2 (hdW τ i),
      fun τ w hw hE => gfp_basis hx0 hx τ (d τ) (hd τ) (hdW τ) w hw hE,
      (gfp_gen hT x).choose, (gfp_gen hT x).choose_spec⟩,
    ⟨spMap (algebraMap L L') ≫ x, hx0', fun τ i => gfpVec _ xc' (e τ i), fun τ i => gfp_tan hx' _,
      fun τ i => (gfp_eig_iff hx' τ _).2 (heW τ i),
      fun τ w hw hE => gfp_basis hx0' hx' τ (e τ) (he τ) (heW τ) w hw hE,
      (gfp_gen hT _).choose, (gfp_gen hT _).choose_spec⟩, rfl, rfl, fun τ i => ?_⟩
  have hfun : (fun j => spMap (dualMap (algebraMap L L')) ≫ gfpVec x xc (d τ j)) =
      fun j => gfpVec (spMap (algebraMap L L') ≫ x) xc' (d' τ j) := funext fun j => (hvec _).symm
  have key := (gfp_comb_iff hx' (d' τ) (M τ i) (e τ i)).2 rfl
  rw [← hfun] at key
  exact key

end Gen

theorem genFrEx_of (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) : GenFrEx Xo c := by
  intro Z
  obtain ⟨y₀, y, h0, h1, h2⟩ := gfp_frPt_gen (L := kap Z) (L' := Om Z) hT (gfp_tower Z) (xGen Z)
    (gfp_xGen_over Z) (fun τ => genCoef Z τ) (fun τ i => by simp [genCoef])
    (fun τ i j hji => by simp [genCoef, not_lt.2 hji.le, hji.ne'])
  exact ⟨y, h1, y₀, h0, h2⟩

end Formalism.L2.Pj
