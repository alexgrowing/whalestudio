import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualCotangentKer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalLinearPrimeBound

open StackedExceptionalFirstGeometric

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def linS (m : T → ℤ) : MRing (stackedBlocks T) := ∑ t, C (m t) * graphSecond t

theorem linD_add (m n : T → ℤ) : linD (m + n) = linD m + linD n := by
  simp [linD, add_mul, Finset.sum_add_distrib]

theorem linD_sub (m n : T → ℤ) : linD (m - n) = linD m - linD n := by
  simp [linD, sub_mul, Finset.sum_sub_distrib]

theorem linD_zero : linD (0 : T → ℤ) = 0 := by
  simp [linD]

theorem linD_single (c : T) : linD (Pi.single c 1 : T → ℤ) = X ⟨(), c⟩ := by
  simp [linD, Pi.single_apply]

theorem linS_add (m n : T → ℤ) : linS (m + n) = linS m + linS n := by
  simp [linS, add_mul, Finset.sum_add_distrib]

theorem linS_single (c : T) : linS (Pi.single c 1 : T → ℤ) = graphSecond c := by
  simp [linS, Pi.single_apply]

theorem graphMap_linS {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (m : T → ℤ) :
    graphMap (dualIdeal b') (linForm (stackedDiag a)) (linS m) =
      C (Ideal.Quotient.mk (dualIdeal b') (linD fun s => m s * a s)) * X () := by
  rw [linS, linD, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, graphSecond, graphMap, eval₂Hom_C, eval₂Hom_X']
  simp [linForm, stackedDiag, mul_assoc]

theorem linD_mem_base {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (n : T → ℤ)
    (hn : ∑ s, n s • (b' s : Fin i → K) ∈ dualLattice F) : fstEmb (linD n) ∈ stackedBase b' a := by
  obtain ⟨m, hm⟩ := exists_coeff_stacked hab hn
  have hlin : IsLinAt b' (linD n - linD fun s => m s * a s) 0 := by
    have := (isLinAt_linD b' n).sub (isLinAt_linD b' fun s => m s * a s)
    rwa [hm, sub_self] at this
  have hle : stackedGraph b' a ≤ stackedBase b' a := le_sup_left
  have hsp : Ideal.span (Set.range fun t => C (a t) * graphFirst t) ≤ stackedBase b' a := le_sup_right
  have h1 := hle (fstEmb_mem a (mem_dualIdeal_of_isLinAt_zero hlin))
  have h2 : fstEmb (linD fun s => m s * a s) ∈ stackedBase b' a := by
    rw [fstEmb_linD]
    refine Ideal.sum_mem _ fun s _ => ?_
    rw [C_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hsp (Ideal.subset_span ⟨s, rfl⟩))
  have := Ideal.add_mem _ h1 h2
  rwa [map_sub, sub_add_cancel] at this

theorem quad_mem_graph {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')} (a : T → ℤ)
    (n₁ n₂ n₃ n₄ : T → ℤ)
    (hq : formCoord (∑ s, n₁ s • (b' s : Fin i → K)) * formCoord (∑ s, n₂ s • (b' s : Fin i → K)) =
      formCoord (∑ s, n₃ s • (b' s : Fin i → K)) * formCoord (∑ s, n₄ s • (b' s : Fin i → K))) :
    fstEmb (linD n₁) * fstEmb (linD n₂) - fstEmb (linD n₃) * fstEmb (linD n₄) ∈ stackedGraph b' a := by
  have := fstEmb_mem a (mem_dualIdeal_of_isLinAt_quad (isLinAt_linD b' n₁) (isLinAt_linD b' n₂)
    (isLinAt_linD b' n₃) (isLinAt_linD b' n₄) hq)
  rwa [map_sub, map_mul, map_mul] at this

theorem mixed_mem_graph {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')} (a : T → ℤ)
    (m n m' n' : T → ℤ)
    (hq : formCoord (∑ s, (m s * a s) • (b' s : Fin i → K)) * formCoord (∑ s, n s • (b' s : Fin i → K)) =
      formCoord (∑ s, (m' s * a s) • (b' s : Fin i → K)) * formCoord (∑ s, n' s • (b' s : Fin i → K))) :
    linS m * fstEmb (linD n) - linS m' * fstEmb (linD n') ∈ stackedGraph b' a := by
  have h := Ideal.Quotient.eq.mpr (mem_dualIdeal_of_isLinAt_quad (isLinAt_linD b' fun s => m s * a s)
    (isLinAt_linD b' n) (isLinAt_linD b' fun s => m' s * a s) (isLinAt_linD b' n') hq)
  rw [map_mul, map_mul] at h
  have hC := congrArg (C : MRing (dualBlocks T) ⧸ dualIdeal b' →+* MvPolynomial Unit _) h
  rw [C_mul, C_mul] at hC
  show _ ∈ RingHom.ker _
  rw [RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_linS, graphMap_linS, graphMap_fstEmb, graphMap_fstEmb]
  linear_combination (X () : MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b')) * hC

section Prime

variable {F F' : HermLattice K i} (P : Ideal (MRing (stackedBlocks T))) [P.IsPrime]

abbrev FracP := FractionRing (MRing (stackedBlocks T) ⧸ P)

def toFrac : MRing (stackedBlocks T) →+* FracP P :=
  (algebraMap (MRing (stackedBlocks T) ⧸ P) (FracP P)).comp (Ideal.Quotient.mk P)

theorem toFrac_eq_zero {f : MRing (stackedBlocks T)} : toFrac P f = 0 ↔ f ∈ P := by
  rw [toFrac, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem toFrac_eq_of_sub_mem {f g : MRing (stackedBlocks T)} (h : f - g ∈ P) : toFrac P f = toFrac P g := by
  rw [← sub_eq_zero, ← map_sub, toFrac_eq_zero]
  exact h

def coef (b' : Module.Basis T ℤ (dualLattice F')) (c : T) (μ : 𝓞 K) : T → ℤ :=
  (exists_coeff b' (smul_mem_dual F' μ (b' c).2)).choose

theorem coef_spec (b' : Module.Basis T ℤ (dualLattice F')) (c : T) (μ : 𝓞 K) :
    ∑ s, coef b' c μ s • (b' s : Fin i → K) = algebraMap (𝓞 K) K μ • (b' c : Fin i → K) :=
  (exists_coeff b' (smul_mem_dual F' μ (b' c).2)).choose_spec

theorem sum_single_smul (b' : Module.Basis T ℤ (dualLattice F')) (c : T) :
    ∑ s, (Pi.single c 1 : T → ℤ) s • (b' s : Fin i → K) = b' c := by
  simp [Pi.single_apply]

def theta (b' : Module.Basis T ℤ (dualLattice F')) (c : T) (μ : 𝓞 K) : FracP P :=
  toFrac P (fstEmb (linD (coef b' c μ))) / toFrac P (graphFirst c)

variable {P}

theorem toFrac_graphFirst_ne {c : T} (hc : graphFirst c ∉ P) : toFrac P (graphFirst c) ≠ 0 :=
  fun h => hc ((toFrac_eq_zero P).mp h)

theorem theta_mul {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (hc : graphFirst c ∉ P) (μ : 𝓞 K) (n : T → ℤ)
    (hn : ∑ s, n s • (b' s : Fin i → K) = algebraMap (𝓞 K) K μ • (b' c : Fin i → K)) :
    theta P b' c μ * toFrac P (graphFirst c) = toFrac P (fstEmb (linD n)) := by
  rw [theta, div_mul_cancel₀ _ (toFrac_graphFirst_ne hc)]
  apply toFrac_eq_of_sub_mem
  rw [← map_sub, ← linD_sub]
  apply hP
  apply linD_mem_base hab
  have : ∑ s, (coef b' c μ - n) s • (b' s : Fin i → K) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, coef_spec, hn, sub_self]
  rw [this]
  exact zero_mem _

def thetaHom {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (hc : graphFirst c ∉ P) : 𝓞 K →+* FracP P where
  toFun := theta P b' c
  map_one' := by
    apply mul_right_cancel₀ (toFrac_graphFirst_ne hc)
    rw [theta_mul hab hP hc 1 (Pi.single c 1) (by rw [sum_single_smul, map_one, one_smul]), one_mul,
      linD_single, fstEmb_X]
  map_mul' μ ν := by
    apply mul_right_cancel₀ (mul_ne_zero (toFrac_graphFirst_ne hc) (toFrac_graphFirst_ne hc))
    have e1 := theta_mul hab hP hc (μ * ν) _ (coef_spec b' c (μ * ν))
    have e2 := theta_mul hab hP hc μ _ (coef_spec b' c μ)
    have e3 := theta_mul hab hP hc ν _ (coef_spec b' c ν)
    have hform : formCoord (∑ s, coef b' c (μ * ν) s • (b' s : Fin i → K)) *
        formCoord (∑ s, (Pi.single c 1 : T → ℤ) s • (b' s : Fin i → K)) =
        formCoord (∑ s, coef b' c μ s • (b' s : Fin i → K)) *
          formCoord (∑ s, coef b' c ν s • (b' s : Fin i → K)) := by
      rw [coef_spec, coef_spec, coef_spec, sum_single_smul, formCoord_smul, formCoord_smul, formCoord_smul,
        map_mul, C_mul, map_mul]
      ring
    have hq := toFrac_eq_of_sub_mem P (hP ((le_sup_left : stackedGraph b' a ≤ stackedBase b' a)
      (quad_mem_graph a _ _ _ _ hform)))
    rw [map_mul, map_mul, linD_single, fstEmb_X, ← e1, ← e2, ← e3] at hq
    linear_combination hq
  map_zero' := by
    have h := theta_mul hab hP hc 0 0 (by simp)
    rw [linD_zero, map_zero, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (toFrac_graphFirst_ne hc)
  map_add' μ ν := by
    apply mul_right_cancel₀ (toFrac_graphFirst_ne hc)
    rw [theta_mul hab hP hc (μ + ν) (coef b' c μ + coef b' c ν)
        (by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, coef_spec, map_add]),
      add_mul, theta_mul hab hP hc μ _ (coef_spec b' c μ), theta_mul hab hP hc ν _ (coef_spec b' c ν),
      linD_add, map_add, map_add]

theorem thetaHom_apply {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (hc : graphFirst c ∉ P) (μ : 𝓞 K) : thetaHom hab hP hc μ = theta P b' c μ := rfl

theorem theta_eq_zero {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (μ : 𝓞 K) (h : algebraMap (𝓞 K) K μ • (b' c : Fin i → K) ∈ dualLattice F) : theta P b' c μ = 0 := by
  rw [theta, (toFrac_eq_zero P).mpr (hP (linD_mem_base hab _ (by rw [coef_spec]; exact h))), zero_div]

end Prime

section Second

variable {F F' : HermLattice K i} {P : Ideal (MRing (stackedBlocks T))} [P.IsPrime]

variable (P) in

def secVal (b : Module.Basis T ℤ (dualLattice F)) : dualLattice F →+ FracP P :=
  AddMonoidHom.mk' (fun ψ => toFrac P (linS fun t => b.repr ψ t)) (by
    intro ψ χ
    show toFrac P (linS _) = toFrac P (linS _) + toFrac P (linS _)
    rw [← map_add, ← linS_add]
    congr 2
    funext t
    simp)

theorem secVal_apply (b : Module.Basis T ℤ (dualLattice F)) (ψ : dualLattice F) :
    secVal P b ψ = toFrac P (linS fun t => b.repr ψ t) := rfl

theorem secVal_basis (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    secVal P b (b t) = toFrac P (graphSecond t) := by
  have h : (fun s => b.repr (b t) s) = (Pi.single t 1 : T → ℤ) := by
    funext s
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [secVal_apply, h, linS_single]

theorem sum_repr_stacked {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (ψ : dualLattice F) :
    ∑ s, (b.repr ψ s * a s) • (b' s : Fin i → K) = ψ := by
  have h := congrArg (fun x : dualLattice F => (x : Fin i → K)) (b.sum_repr ψ)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hab, mul_smul]

theorem secVal_smul {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (hc : graphFirst c ∉ P) (μ : 𝓞 K) (φ ψ : dualLattice F)
    (h : (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)) :
    secVal P b ψ = thetaHom hab hP hc μ * secVal P b φ := by
  apply mul_right_cancel₀ (toFrac_graphFirst_ne hc)
  have hform : formCoord (∑ s, (b.repr ψ s * a s) • (b' s : Fin i → K)) *
      formCoord (∑ s, (Pi.single c 1 : T → ℤ) s • (b' s : Fin i → K)) =
      formCoord (∑ s, (b.repr φ s * a s) • (b' s : Fin i → K)) *
        formCoord (∑ s, coef b' c μ s • (b' s : Fin i → K)) := by
    rw [sum_repr_stacked hab, sum_repr_stacked hab, sum_single_smul, coef_spec, h, formCoord_smul,
      formCoord_smul]
    ring
  have hq := toFrac_eq_of_sub_mem P (hP ((le_sup_left : stackedGraph b' a ≤ stackedBase b' a)
    (mixed_mem_graph a _ _ _ _ hform)))
  rw [map_mul, map_mul, linD_single, fstEmb_X, ← theta_mul hab hP hc μ _ (coef_spec b' c μ)] at hq
  rw [secVal_apply, secVal_apply, thetaHom_apply, hq]
  ring

theorem secVal_eq_zero_of_mem_span {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (hP : stackedBase b' a ≤ P) {c : T}
    (hc : graphFirst c ∉ P) {k : Type} [Field k] (ρ : 𝓞 K →+* k)
    (hz : ∀ μ : 𝓞 K, ρ μ = 0 → algebraMap (𝓞 K) K μ • (b' c : Fin i → K) ∈ dualLattice F) {v : dualLattice F}
    (hv : v ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}) : secVal P b v = 0 := by
  have hle : Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
      (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)} ≤ LinearMap.ker (secVal P b).toIntLinearMap := by
    refine Submodule.span_le.mpr fun v hv => ?_
    obtain ⟨μ, φ, hμ, hv⟩ := hv
    show secVal P b v = 0
    rw [secVal_smul hab hP hc μ φ v hv, thetaHom_apply, theta_eq_zero hab hP μ (hz μ hμ), zero_mul]
  exact hle hv

end Second

end StackedExceptionalLinearPrimeBound

open StackedExceptionalLinearPrimeBound StackedExceptionalFirstGeometric in

theorem DualStackedExcLinPrimeLe.proof (hK : DualCotangentKer.Statement) : DualStackedExcLinPrimeLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov hab k _ α M hdata P hPp hP hrel
  haveI := hPp
  obtain ⟨ρ, ρ', σ, hρ, -, hσ, hker, hsl', hsl, hα, hM⟩ := hdata
  obtain ⟨c, hc⟩ : ∃ c : T, graphFirst c ∉ P := hrel (Sum.inl ())

  have hnd : (b' c : Fin i → K) ∉ dualLattice F := by
    intro h
    apply hc
    have := hP (linD_mem_base hab (Pi.single c 1) (by rwa [sum_single_smul]))
    rwa [linD_single, fstEmb_X] at this
  have hz : ∀ μ : 𝓞 K, ρ μ = 0 → algebraMap (𝓞 K) K μ • (b' c : Fin i → K) ∈ dualLattice F := by
    intro μ hμ
    have := hsl' μ (b' c) ⟨_, smul_mem_dual F' μ (b' c).2⟩ rfl
    rw [hμ, zero_mul] at this
    exact (hker _).mp this

  let ι : k →+* FracP P := ρ.liftOfSurjective hρ ⟨thetaHom hab hP hc, fun μ hμ => by
    rw [RingHom.mem_ker] at hμ ⊢
    exact theta_eq_zero hab hP μ (hz μ hμ)⟩
  have hι : ∀ μ, ι (ρ μ) = theta P b' c μ := fun μ => RingHom.liftOfSurjective_comp_apply ρ hρ _ μ
  have hxc := toFrac_graphFirst_ne hc
  have hαc : ι (α c) ≠ 0 := by
    refine (map_ne_zero ι).mpr ?_
    rw [hα]
    intro h
    exact hnd ((hker _).mp h)

  have hA : ∀ t, ι (α t) * toFrac P (graphFirst c) = ι (α c) * toFrac P (graphFirst t) := by
    intro t
    obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (b' c).2 hnd (b' t).2
    have hαt : α t = ρ l * α c := by
      rw [hα, hα]
      have h1 : ρ' (b' t - ⟨_, smul_mem_dual F' l (b' c).2⟩) = 0 := (hker _).mpr hl
      rw [map_sub, sub_eq_zero] at h1
      rw [h1, hsl' l (b' c) _ rfl]
    have hxt : toFrac P (graphFirst t) = theta P b' c l * toFrac P (graphFirst c) := by
      rw [theta_mul hab hP hc l _ (coef_spec b' c l)]
      apply toFrac_eq_of_sub_mem
      have hmem := hP (linD_mem_base hab (Pi.single t 1 - coef b' c l) (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, coef_spec, sum_single_smul]
        exact hl))
      rwa [linD_sub, map_sub, linD_single, fstEmb_X] at hmem
    rw [hαt, map_mul, hι, hxt]
    ring

  choose χ hχ using fun j : Fin i => hσ (Pi.single j 1)
  choose μ hμ using fun (t : T) (j : Fin i) => hρ (M t j)
  have hB : ∀ t, toFrac P (graphSecond t) = ∑ j, ι (M t j) * secVal P b (χ j) := by
    intro t
    let ψ : dualLattice F := ∑ j, ⟨algebraMap (𝓞 K) K (μ t j) • (χ j : Fin i → K), smul_mem_dual F _ (χ j).2⟩
    have hσψ : σ ψ = σ (b t) := by
      have hs : ∀ j, σ ⟨algebraMap (𝓞 K) K (μ t j) • (χ j : Fin i → K), smul_mem_dual F _ (χ j).2⟩ =
          M t j • (Pi.single j 1 : Fin i → k) := fun j => by
        rw [hsl (μ t j) (χ j) _ rfl, hμ, hχ]
      rw [map_sum, Finset.sum_congr rfl fun j _ => hs j, ← hM t]
      funext j'
      simp [Pi.single_apply]
    have h0 := secVal_eq_zero_of_mem_span (P := P) (b := b) hab hP hc ρ hz
      (hK K i F T b k ρ σ hρ hσ hsl (b t - ψ) (by rw [map_sub, hσψ, sub_self]))
    rw [map_sub, sub_eq_zero, secVal_basis] at h0
    rw [h0, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [secVal_smul hab hP hc (μ t j) (χ j) _ rfl, ← hμ t j, hι, thetaHom_apply]

  have hg : (eval₂Hom ι fun o => Option.elim o (toFrac P (graphFirst c) / ι (α c))
      fun j => secVal P b (χ j)).comp (linPointMap α M) = toFrac P := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((eval₂Hom ι fun o => Option.elim o
        (toFrac P (graphFirst c) / ι (α c)) fun j => secVal P b (χ j)).comp (linPointMap α M)).comp C)
        ((toFrac P).comp C)) r
    · rintro ⟨(⟨⟩ | ⟨⟩), (t : T)⟩
      · show eval₂Hom _ _ (linPointMap α M (graphFirst t)) = toFrac P (graphFirst t)
        rw [LinPrimeExample.linPointMap_first, map_mul, eval₂Hom_C, eval₂Hom_X']
        simp only [Option.elim]
        rw [← mul_div_assoc, hA t, mul_div_cancel_left₀ _ hαc]
      · show eval₂Hom _ _ (linPointMap α M (graphSecond t)) = toFrac P (graphSecond t)
        rw [LinPrimeExample.linPointMap_second, map_sum, hB t]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, eval₂Hom_C, eval₂Hom_X']
        rfl
  intro f hf
  rw [linPrime, RingHom.mem_ker] at hf
  rw [← toFrac_eq_zero P, ← hg, RingHom.comp_apply, hf, map_zero]

end

end GroundTheory.Heights₂.Heights
