import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.Analytic
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchPolar
import GroundTheory.AutomorphicForms.L2LocalComponents.CuspSmooth
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

open MeasureTheory Filter Topology Polynomial
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm Reduction UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem mem_of_mem_topologicalClosure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S Y : Submodule ℂ E} (hY : IsClosed (Y : Set E)) (T : E →L[ℂ] E) (hT : ∀ v ∈ S, T v ∈ Y)
    {v : E} (hv : v ∈ S.topologicalClosure) : T v ∈ Y := by
  have hle : S ≤ Y.comap (T : E →ₗ[ℂ] E) := fun w hw => hT w hw
  exact Submodule.topologicalClosure_minimal S hle (hY.preimage T.continuous) hv

theorem exists_eq_archimedean_mul_finite (g : normOneGL K n) :
    ∃ (a : archGroup K n) (f : AdelicGLn.FiniteAdelicGL K n),
      g = archP K n a * retractOne (finEmb K n f) := by
  refine ⟨archEquiv K n (AdelicGLn.prodEquiv K n g).1, (AdelicGLn.prodEquiv K n g).2, ?_⟩
  calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
    _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
          finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
    _ = _ := by rw [retractOne_mul, retract_infEmb]

theorem derivOp_mem {V : Submodule ℂ (CuspL2 μ)} (hVc : IsClosed (V : Set (CuspL2 μ)))
    (hV : (cuspRepT μ).IsInvariant V) {v : CuspL2 μ} (hv : v ∈ V)
    (hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v) (X : archLie K n) :
    (isExpLieAlgebra K n).derivOp (archRepT μ) X v ∈ V := by
  have hd := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) hs X
  have ht := hasDerivAt_iff_tendsto_slope.1 hd
  refine hVc.mem_of_tendsto ht (Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  refine V.smul_mem _ (V.sub_mem ?_ ?_)
  · rw [archRepT_apply]
    exact hV _ _ hv
  · rw [archRepT_apply]
    exact hV _ _ hv

theorem derivOp_cuspVecL {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) (X : archLie K n) :
    (isExpLieAlgebra K n).derivOp (archRepT μ) X (cuspVecL μ φ) =
      cuspVecL μ ((gkModuleCusp K n).ρ ((isExpLieAlgebra K n).toLie X) φ) := by
  rw [gkModuleCusp_ρ_apply, ← uAction_cuspToL2 μ hφ, IsExpLieAlgebra.uAction_ι,
    IsExpLieAlgebra.coe_derivEnd, IsExpLieAlgebra.ofLie_toLie]

theorem aeval_uAction_cuspVecL {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) (u : UEnv K n)
    (P : ℂ[X]) :
    ((aeval ((isExpLieAlgebra K n).uAction (archRepT μ) u) P
        ⟨cuspVecL μ φ, isSmoothVector_cuspToL2 μ hφ⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) :
      CuspL2 μ) = cuspVecL μ (aeval (uActionCusp K n u) P φ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp, hq, map_add]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_pow, ← map_pow,
      Submodule.coe_smul, uAction_cuspToL2 μ hφ, map_smul]

set_option maxHeartbeats 1000000 in

theorem isInvariant_topologicalClosure_map {W : Submodule ℂ (cuspForms K n)}
    (hW : W ≤ centralCuspForms K n)
    (hWρ : ∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W)
    (hWσ : ∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W)
    (hWτ : ∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W) :
    (cuspRepT μ).IsInvariant (W.map (cuspVecL μ)).topologicalClosure := by
  set S := W.map (cuspVecL μ) with hSdef
  set Y := S.topologicalClosure with hYdef
  have hYc : IsClosed (Y : Set (CuspL2 μ)) := S.isClosed_topologicalClosure
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  have hS : ∀ v ∈ S, (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact isSmoothVector_cuspToL2 μ (hW hφ)
  have hSd : ∀ X : archLie K n, ∀ v ∈ S, (isExpLieAlgebra K n).derivOp (archRepT μ) X v ∈ S := by
    rintro X _ ⟨φ, hφ, rfl⟩
    rw [derivOp_cuspVecL μ (hW hφ)]
    exact ⟨_, hWρ _ φ hφ, rfl⟩
  have hSP : ∀ v (hv : v ∈ S), ∃ P : ℂ[X], P.Monic ∧
      aeval ((isExpLieAlgebra K n).uAction (archRepT μ) ((isExpLieAlgebra K n).laplacianElt b)) P
        ⟨v, hS v hv⟩ = 0 := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨P, hP, -, hPφ⟩ := exists_aeval_uActionCusp_laplacianU_eq_zero φ b ε B hε horth hsymm hinv hK
    refine ⟨P, hP, Subtype.ext ?_⟩
    have := aeval_uAction_cuspVecL μ (hW hφ) (laplacianU K n b) P
    rw [hPφ, map_zero] at this
    exact this

  have hexp : ∀ v ∈ S, ∀ Z : archLie K n,
      archRepT μ ((isExpLieAlgebra K n).expG Z) v ∈ Y := by
    intro v hv Z
    rw [hYdef, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have h0 := (isExpLieAlgebra K n).inner_map_expG_eq_zero (archRepT μ) b S hS hSd hSP (w := w)
      (fun u hu => by rw [← inner_conj_symm, hw u hu, map_zero]) hv Z
    exact h0

  have hKS : ∀ k : archCompact K n, ∀ v ∈ S, archRepT μ (k : archGroup K n) v ∈ S := by
    rintro k _ ⟨φ, hφ, rfl⟩
    rw [← cuspToL2_sigma μ k (hW hφ)]
    exact ⟨_, hWσ k φ hφ, rfl⟩
  have hKY : ∀ k : archCompact K n, ∀ v ∈ Y, archRepT μ (k : archGroup K n) v ∈ Y := fun k v hv =>
    mem_of_mem_topologicalClosure hYc ((archRepT μ) (k : archGroup K n))
      (fun u hu => S.le_topologicalClosure (hKS k u hu)) hv

  have harchS : ∀ a : archGroup K n, ∀ v ∈ S, archRepT μ a v ∈ Y := by
    intro a v hv
    obtain ⟨k, hk, Z, rfl⟩ := exists_mem_archCompact_mul_expG a
    rw [BanachRep.map_mul_apply]
    exact hKY ⟨k, hk⟩ _ (hexp v hv Z)
  have harchY : ∀ a : archGroup K n, ∀ v ∈ Y, archRepT μ a v ∈ Y := fun a v hv =>
    mem_of_mem_topologicalClosure hYc ((archRepT μ) a) (harchS a) hv

  have hfinS : ∀ f, ∀ v ∈ S, cuspRepT μ (retractOne (finEmb K n f)) v ∈ S := by
    rintro f _ ⟨φ, hφ, rfl⟩
    rw [← cuspToL2_finRepCusp μ f (hW hφ)]
    exact ⟨_, hWτ f φ hφ, rfl⟩
  have hfinY : ∀ f, ∀ v ∈ Y, cuspRepT μ (retractOne (finEmb K n f)) v ∈ Y := fun f v hv =>
    mem_of_mem_topologicalClosure hYc (cuspRepT μ (retractOne (finEmb K n f)))
      (fun u hu => S.le_topologicalClosure (hfinS f u hu)) hv
  intro g v hv
  obtain ⟨a, f, rfl⟩ := exists_eq_archimedean_mul_finite g
  rw [UnitaryRep.map_mul_apply]
  have := harchY a _ (hfinY f v hv)
  rw [archRepT_apply] at this
  exact this

set_option maxHeartbeats 1000000 in

theorem sup_orthRel_of_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : cuspForms K n →ₗ[ℂ] H)
    (hinj : ∀ a ∈ centralCuspForms K n, ι a = 0 → a = 0)
    (hτ : ∀ g, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι (finRepCusp K n g a)) (ι (finRepCusp K n g c)) = inner ℂ (ι a) (ι c))
    (hρ : ∀ X, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι ((gkModuleCusp K n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp K n).ρ X c)) = 0)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (hΔ : ∀ φ : cuspForms K n, ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧
      aeval (uActionCusp K n (laplacianU K n b)) P φ = 0)
    (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hUρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U)
    (hUτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) :
    U ⊔ orthRel ι (centralCuspForms K n) U = centralCuspForms K n := by
  classical
  let Δ := uActionCusp K n (laplacianU K n b)
  have hΔsum : ∀ φ : cuspForms K n,
      Δ φ = ∑ i, (gkModuleCusp K n).ρ (b i) ((gkModuleCusp K n).ρ (b i) φ) := by
    intro φ
    simp only [Δ, laplacianU, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply]
    rfl
  have hΔV : ∀ φ ∈ centralCuspForms K n, Δ φ ∈ centralCuspForms K n :=
    fun φ hφ => uActionCusp_mem_centralCuspForms _ hφ
  have hXX : ∀ X, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι ((gkModuleCusp K n).ρ X ((gkModuleCusp K n).ρ X a))) (ι c) =
      inner ℂ (ι a) (ι ((gkModuleCusp K n).ρ X ((gkModuleCusp K n).ρ X c))) := by
    intro X a ha c hc
    have h1 := hρ X _ (ρ_mem_centralCuspForms X ha) c hc
    have h2 := hρ X a ha _ (ρ_mem_centralCuspForms X hc)
    linear_combination h1 - h2
  have hT : ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (ι (Δ x)) (ι y) = inner ℂ (ι x) (ι (Δ y)) := by
    intro x hx y hy
    rw [hΔsum, hΔsum, map_sum, map_sum, sum_inner, inner_sum]
    exact Finset.sum_congr rfl fun i _ => hXX (b i) x hx y hy
  have hUΔ : ∀ φ ∈ U, Δ φ ∈ U := fun φ hφ => by
    rw [hΔsum]
    exact U.sum_mem fun i _ => hUρ _ _ (hUρ _ _ hφ)
  have hHC : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      (U₀ : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n →
      ∀ P : ℂ[X], P.Monic → 0 < P.natDegree → ∀ S : Submodule ℂ (cuspForms K n),
        (∀ φ ∈ S, aeval (uActionCusp K n (laplacianU K n b)) P φ = 0 ∧
          (gkModuleCusp K n).ρ (centralZ K n) φ = 0 ∧ ∀ u ∈ U₀, finRepCusp K n u φ = φ) →
        FiniteDimensional ℂ S :=
    fun U₀ _ P hP hPd S hS => finiteDimensional_of_eigen b P hP hPd 0
      ((U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)).comap (AdelicGLn.integralFiniteGL K n).subtype)
      (U₀.isOpen.preimage continuous_subtype_val) S fun φ hφ =>
        ⟨(hS φ hφ).1, by rw [zero_smul]; exact (hS φ hφ).2.1, fun u hu => (hS φ hφ).2.2 _ hu⟩
  refine sup_orthRel_eq_of_symmetric (ι := ι) hU hinj hΔV hT hUΔ (fun v hv => ?_)
  obtain ⟨U₀, hU₀sub, hU₀⟩ := exists_openSubgroup_rightInvariant v.2.1.isSmooth v.2.1.isKFinite
  let V₀ : Submodule ℂ (cuspForms K n) :=
    { carrier := {x | x ∈ centralCuspForms K n ∧ ∀ h ∈ U₀, finRepCusp K n h x = x}
      zero_mem' := ⟨Submodule.zero_mem _, fun h _ => map_zero _⟩
      add_mem' := fun {x y} hx hy => ⟨Submodule.add_mem _ hx.1 hy.1, fun h hh => by
        rw [map_add, hx.2 h hh, hy.2 h hh]⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun h hh => by
        rw [map_smul, hx.2 h hh]⟩ }
  refine ⟨V₀, fun x hx => hx.1, ⟨hv, fun h hh => Subtype.ext (funext fun g => hU₀ g h hh)⟩,
    fun z hz => ⟨hΔV z hz.1, fun h hh => ?_⟩, fun x hx => ?_, fun u hu => ?_⟩
  · show finRepCusp K n h (uActionCusp K n (laplacianU K n b) z) = uActionCusp K n (laplacianU K n b) z
    rw [← uActionCusp_finRepCusp, hz.2 h hh]
  · obtain ⟨P, hPm, hPd, hP⟩ := hΔ x
    obtain ⟨p, hp⟩ := exists_map_eq_mul_map_conj P
    have hQm : (p.map (algebraMap ℝ ℂ)).Monic := hp ▸ hPm.mul (hPm.map _)
    have hQd : 0 < (p.map (algebraMap ℝ ℂ)).natDegree := by
      rw [hp, hPm.natDegree_mul (hPm.map _)]
      omega
    refine ⟨p, ?_, hHC U₀ hU₀sub _ hQm hQd _ fun φ hφ =>
      ⟨hφ.2, ρ_centralZ_eq_zero hφ.1.1, hφ.1.2⟩⟩
    show aeval Δ (p.map (algebraMap ℝ ℂ)) x = 0
    rw [hp, mul_comm, map_mul, Module.End.mul_apply, hP, map_zero]
  · obtain ⟨e, heU, hefix, he⟩ := exists_average ι hτ U hU hUτ U₀ hU₀sub hu
    exact ⟨e, ⟨heU, hU heU, hefix⟩, fun w hw => he w hw.1 hw.2⟩

theorem sup_orthRel_centralCuspForms (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hUρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U)
    (hUτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) :
    U ⊔ orthRel (cuspToL2 μ) (centralCuspForms K n) U = centralCuspForms K n := by
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  exact sup_orthRel_of_finite (cuspToL2 μ)
    (fun a ha h0 => injOn_cuspToL2 μ (ha : _) (fun _ _ => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm))
    (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc)
    (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc) b
    (fun φ => exists_aeval_uActionCusp_laplacianU_eq_zero φ b ε B hε horth hsymm hinv hK) U hU hUρ hUτ

variable {μ}

def summandCuspForms (V : Submodule ℂ (CuspL2 μ)) : Submodule ℂ (cuspForms K n) :=
  centralCuspForms K n ⊓ V.comap (cuspVecL μ)

theorem mem_summandCuspForms {V : Submodule ℂ (CuspL2 μ)} {φ : cuspForms K n} :
    φ ∈ summandCuspForms V ↔ φ ∈ centralCuspForms K n ∧ cuspVecL μ φ ∈ V :=
  Iff.rfl

theorem summandCuspForms_le_central (V : Submodule ℂ (CuspL2 μ)) :
    summandCuspForms V ≤ centralCuspForms K n :=
  inf_le_left

section Summand

variable {V : Submodule ℂ (CuspL2 μ)} (hVc : IsClosed (V : Set (CuspL2 μ)))
  (hV : (cuspRepT μ).IsInvariant V)

include hVc hV in

theorem summandCuspForms_stable_ρ :
    ∀ X, ∀ φ ∈ summandCuspForms V, (gkModuleCusp K n).ρ X φ ∈ summandCuspForms V := by
  intro X φ hφ
  refine ⟨ρ_mem_centralCuspForms X hφ.1, ?_⟩
  show cuspVecL μ ((gkModuleCusp K n).ρ X φ) ∈ V
  have e := derivOp_cuspVecL μ hφ.1 ((isExpLieAlgebra K n).ofLie X)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [← e]
  exact derivOp_mem μ hVc hV hφ.2 (isSmoothVector_cuspToL2 μ hφ.1) _

include hV in

theorem summandCuspForms_stable_σ :
    ∀ k, ∀ φ ∈ summandCuspForms V, (gkModuleCusp K n).σ k φ ∈ summandCuspForms V := by
  intro k φ hφ
  refine ⟨σ_mem_centralCuspForms k hφ.1, ?_⟩
  show cuspVecL μ ((gkModuleCusp K n).σ k φ) ∈ V
  rw [cuspToL2_sigma μ k hφ.1, archRepT_apply]
  exact hV _ _ hφ.2

include hV in

theorem summandCuspForms_stable_τ :
    ∀ g, ∀ φ ∈ summandCuspForms V, finRepCusp K n g φ ∈ summandCuspForms V := by
  intro g φ hφ
  refine ⟨finRepCusp_mem_centralCuspForms g hφ.1, ?_⟩
  show cuspVecL μ (finRepCusp K n g φ) ∈ V
  rw [cuspToL2_finRepCusp μ g hφ.1]
  exact hV _ _ hφ.2

theorem eq_zero_of_cuspVecL_eq_zero {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (h0 : cuspVecL μ φ = 0) : φ = 0 :=
  injOn_cuspToL2 μ (hφ : _) (fun _ _ => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm)

include hV in

theorem le_topologicalClosure_map [CompleteSpace V] (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    {W : Submodule ℂ (cuspForms K n)} (hWU : W ≤ summandCuspForms V)
    (hWρ : ∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W)
    (hWσ : ∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W)
    (hWτ : ∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W) (hW0 : W ≠ ⊥) :
    V ≤ (W.map (cuspVecL μ)).topologicalClosure := by
  set Y := (W.map (cuspVecL μ)).topologicalClosure with hYdef
  have hYinv := isInvariant_topologicalClosure_map μ (hWU.trans inf_le_left) hWρ hWσ hWτ
  set Y' : Submodule ℂ V := Y.comap V.subtype with hY'def
  have hY'c : IsClosed (Y' : Set V) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hY'inv : ((cuspRepT μ).restrict V hV).IsInvariant Y' := by
    intro g v hv
    show (((cuspRepT μ).restrict V hV g v : V) : CuspL2 μ) ∈ Y
    rw [UnitaryRep.coe_restrict_apply]
    exact hYinv g v hv
  rcases hirr.2 Y' hY'c hY'inv with h | h
  · exfalso
    obtain ⟨φ, hφW, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem : (⟨cuspVecL μ φ, (hWU hφW).2⟩ : V) ∈ Y' :=
      Submodule.le_topologicalClosure _ ⟨φ, hφW, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hφ0 (eq_zero_of_cuspVecL_eq_zero (hWU hφW).1 (congrArg Subtype.val hmem))
  · intro v hv
    have : (⟨v, hv⟩ : V) ∈ Y' := h ▸ Submodule.mem_top
    exact this

include hVc hV in

theorem eq_summandCuspForms [CompleteSpace V] (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    {W : Submodule ℂ (cuspForms K n)} (hWU : W ≤ summandCuspForms V)
    (hWρ : ∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W)
    (hWσ : ∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W)
    (hWτ : ∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W) (hW0 : W ≠ ⊥) :
    W = summandCuspForms V := by
  have hVY := le_topologicalClosure_map hV hirr hWU hWρ hWσ hWτ hW0
  set O := orthRel (cuspToL2 μ) (centralCuspForms K n) W with hOdef
  have hsup : W ⊔ O = centralCuspForms K n :=
    sup_orthRel_centralCuspForms μ W (hWU.trans inf_le_left) hWρ hWτ
  have hO : O ⊓ summandCuspForms V = ⊥ := by
    rw [eq_bot_iff]
    rintro ψ ⟨hψO, hψU⟩
    rw [Submodule.mem_bot]
    set Kψ : Submodule ℂ (CuspL2 μ) := ℂ ∙ cuspVecL μ ψ
    have hle : W.map (cuspVecL μ) ≤ Kψᗮ := by
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 : inner ℂ (cuspToL2 μ u) (cuspToL2 μ ψ) = 0 := hψO.2 u hu
      exact inner_eq_zero_symm.1 h1
    have hcl : (W.map (cuspVecL μ)).topologicalClosure ≤ Kψᗮ :=
      Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
    have h2 := hcl (hVY hψU.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at h2
    exact eq_zero_of_cuspVecL_eq_zero hψU.1 h2
  apply le_antisymm hWU
  calc summandCuspForms V = (W ⊔ O) ⊓ summandCuspForms V := by
        rw [hsup]; exact (inf_eq_right.2 inf_le_left).symm
    _ = W ⊔ O ⊓ summandCuspForms V := sup_inf_assoc_of_le O hWU
    _ ≤ W := by rw [hO, sup_bot_eq]

include hVc hV in

theorem topologicalClosure_map_summandCuspForms [CompleteSpace V]
    (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) (hne : summandCuspForms V ≠ ⊥) :
    ((summandCuspForms V).map (cuspVecL μ)).topologicalClosure = V := by
  refine le_antisymm ?_ (le_topologicalClosure_map hV hirr le_rfl
    (summandCuspForms_stable_ρ hVc hV) (summandCuspForms_stable_σ hV) (summandCuspForms_stable_τ hV) hne)
  refine Submodule.topologicalClosure_minimal _ ?_ hVc
  rintro _ ⟨φ, hφ, rfl⟩
  exact hφ.2

end Summand

end CuspidalSpectrum

namespace AutomorphicForm

open CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace CuspidalAutomorphicRepresentation

variable {μ : Measure (Reduction.normOneGL K n)} [μ.IsHaarMeasure]

def ofSummand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V] (hV : (cuspRepT μ).IsInvariant V)
    (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible) (hne : summandCuspForms V ≠ ⊥) :
    CuspidalAutomorphicRepresentation K n :=
  have hVc : IsClosed (V : Set (CuspL2 μ)) := (completeSpace_coe_iff_isComplete.1 ‹CompleteSpace V›).isClosed
  ofIrreducible (summandCuspForms V) (summandCuspForms_le_central V)
    (summandCuspForms_stable_ρ hVc hV) (summandCuspForms_stable_σ hV) (summandCuspForms_stable_τ hV)
    (isIrreducible_cuspSubmodule_of _ _ _ _ hne fun W hW hWρ hWσ hWτ => by
      by_cases hW0 : W = ⊥
      · exact Or.inl hW0
      · exact Or.inr (eq_summandCuspForms hVc hV hirr hW hWρ hWσ hWτ hW0))

@[simp] theorem carrier_ofSummand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    (hne : summandCuspForms V ≠ ⊥) : (ofSummand V hV hirr hne).carrier = summandCuspForms V := rfl

theorem topologicalClosure_map_ofSummand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    (hne : summandCuspForms V ≠ ⊥) :
    ((ofSummand V hV hirr hne).carrier.map (cuspVecL μ)).topologicalClosure = V :=
  topologicalClosure_map_summandCuspForms ((completeSpace_coe_iff_isComplete.1 ‹CompleteSpace V›).isClosed) hV hirr hne

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end

end GroundTheory.Automorphic
