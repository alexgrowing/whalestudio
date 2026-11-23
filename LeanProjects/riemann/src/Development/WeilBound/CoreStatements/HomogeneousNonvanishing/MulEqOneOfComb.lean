import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelNef

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.CompHt

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem mul_eq_one_of_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K)
    (h : ∀ j, b j = ∑ k, c k j • ∑ i, g i k • b i) : g * c = 1 := by
  ext i j
  have e := congrArg (fun v => b.repr v i) (h j)
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [mul_comm (g i _), ← e, eq_comm]

theorem sum_eq {K : Type} [Field K] (σ : K →+* ℂ) {N n : ℕ} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} (h : g * c = 1) (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (a : Fin N) :
    ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j = ∑ m, A m a * x m := by
  have e : ∀ j m, ∑ k, σ (g j k) * σ (c k m) = if j = m then 1 else 0 := fun j m => by
    have := congrArg σ (congrFun (congrFun h j) m)
    rw [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite σ, map_one, map_zero] at this
    simpa only [map_mul] using this
  calc ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j
      = ∑ j, ∑ m, (∑ k, σ (g j k) * σ (c k m)) * (A m a * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by simp [e]

theorem isometric_fs {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (L : HermLB M.s)
    (ev : V →ₗ[K] Ω) {W : Submodule (𝓞 K) V} (s : W → L.B.Sec) {e : L.B.ι → Ω}
    (hv : ∀ w : W, M.HasVal e (s w) (ev w)) (hW : Submodule.span K (W : Set V) = ⊤) {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (hgw : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hcb : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hφ : ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts M.s (σ.comp (algebraMap (𝓞 K) K))),
      (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2))
    (hs : ⨆ k, nonzeroLocus (s (gw k)) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hdet hcc)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    (t : ℝ) :
    ((HermLB.fs M.s L.isLB (fun k => s (gw k)) hs Mt hdet hcc).shift (fun _ => t) (fun _ => rfl)).Isometric
      (L.shift (fun _ => t) (fun _ => rfl)) := by
  have hgc := mul_eq_one_of_comb b g c fun j => by simpa only [hgw] using hcb j
  refine HermLB.isometric_of_eqOn fun σ' l y hl => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' := ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
  replace hl : y ∈ ptsIn M.s _ (L.B.U l) := hl
  have hz := mem_ptsIn.1 hl
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hW fun v hvW => by
    rw [← hv ⟨v, hvW⟩ l ⟨_, hz⟩]
    exact valF_mem_O hz _
  have hr : Set.range y.1 ⊆ L.B.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
  have hsk : ∀ k, valR y.1 (L.B.U l) ((s (gw k)).f l) = ∑ j, σ (g j k) * x j := fun k => by
    refine ((val_eq hr (hv (gw k) l ⟨_, hz⟩)).symm.trans (hx _)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgw, b.repr_sum_self]
  refine congrArg (· + 2 * t) ((hφ σ l y).trans (Eq.trans ?_
    (Weight.fsBasis_φ L.isLB (fun k => s (gw k)) hs _ (hdet _) l y).symm))
  simp only [hsk, hMt, sum_eq σ hgc]
  rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)]

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
