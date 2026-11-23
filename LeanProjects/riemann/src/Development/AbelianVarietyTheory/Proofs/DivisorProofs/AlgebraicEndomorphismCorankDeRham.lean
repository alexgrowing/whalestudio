import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescRank

open TensorProduct

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
include hbc

theorem ext_of_bc {φ₁ φ₂ : Module.Dual L P'} (h : ∀ c, φ₁ (mp c) = φ₂ (mp c)) : φ₁ = φ₂ := by
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := hbc.2 y
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def extForm (v : Module.Dual K P) : Module.Dual L P' :=
  liftSemi ({ toFun := fun c ↦ algebraMap K L (v c), map_add' := by simp, map_smul' := by simp } :
      P →ₛₗ[algebraMap K L] L) ∘ₗ (LinearEquiv.ofBijective _ hbc).symm.toLinearMap

theorem extForm_apply (v : Module.Dual K P) (c : P) : extForm mp hbc v (mp c) = algebraMap K L (v c) := by
  have : mp c = LinearEquiv.ofBijective _ hbc (1 ⊗ₜ c) := (one_smul L (mp c)).symm
  rw [extForm, this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem extForm_zero : extForm mp hbc 0 = 0 :=
  ext_of_bc mp hbc fun c ↦ by rw [extForm_apply]; simp

theorem extForm_injective : Function.Injective (extForm mp hbc) := by
  intro v w h
  refine LinearMap.ext fun c ↦ (algebraMap K L).injective ?_
  rw [← extForm_apply mp hbc, ← extForm_apply mp hbc, h]

variable (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hg

theorem extForm_dualMap (w : Module.Dual K P) :
    extForm mp hbc (g₀.dualMap w) = g.dualMap (extForm mp hbc w) :=
  ext_of_bc mp hbc fun c ↦ by
    rw [extForm_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, hg, extForm_apply]

theorem disjoint_desc (h : Disjoint (LinearMap.ker g.dualMap) (LinearMap.range g.dualMap)) :
    Disjoint (LinearMap.ker g₀.dualMap) (LinearMap.range g₀.dualMap) := by
  rw [Submodule.disjoint_def] at h ⊢
  rintro v hv ⟨w, rfl⟩
  have e := h (extForm mp hbc (g₀.dualMap w))
    (by rw [LinearMap.mem_ker, ← extForm_dualMap mp hbc g₀ g hg, LinearMap.mem_ker.1 hv, extForm_zero])
    ⟨extForm mp hbc w, (extForm_dualMap mp hbc g₀ g hg w).symm⟩
  exact extForm_injective mp hbc (e.trans (extForm_zero mp hbc).symm)

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

open TensorProduct

theorem rank_quot_range_dualMap {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) : Module.rank k (Module.Dual k V ⧸ LinearMap.range f.dualMap) = Module.finrank k (LinearMap.ker f) := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, (Subspace.quotAnnihilatorEquiv _).rank_eq, ← Module.finrank_eq_rank,
    Subspace.dual_finrank_eq]

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
  (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hbc hg

theorem rank_coker_desc [FiniteDimensional K P]
    (h : Module.rank L (Module.Dual L P' ⧸ LinearMap.range g.dualMap) ≤ 2) :
    Module.rank K (Module.Dual K P ⧸ LinearMap.range g₀.dualMap) ≤ 2 := by
  haveI : FiniteDimensional L P' := Module.Finite.equiv (LinearEquiv.ofBijective _ hbc)
  rw [rank_quot_range_dualMap] at h ⊢
  let j₀ : L ⊗[K] LinearMap.ker g₀ →ₗ[L] P' := liftSemi mp ∘ₗ (LinearMap.ker g₀).subtype.baseChange L
  have hj₀ : Function.Injective j₀ := by
    refine hbc.1.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hmem : ∀ z, j₀ z ∈ LinearMap.ker g := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul x c =>
      simp only [j₀, LinearMap.comp_apply, LinearMap.baseChange_tmul, Submodule.coe_subtype, liftSemi_tmul,
        LinearMap.mem_ker, map_smul, hg, LinearMap.mem_ker.1 c.2, map_zero, smul_zero]
  let j : L ⊗[K] LinearMap.ker g₀ →ₗ[L] LinearMap.ker g := LinearMap.codRestrict _ j₀ hmem
  have hj : Function.Injective j := fun x y e ↦ hj₀ (congrArg Subtype.val e)
  have hle := LinearMap.finrank_le_finrank_of_injective hj
  rw [Module.finrank_baseChange] at hle
  have h' : Module.finrank L (LinearMap.ker g) ≤ 2 := by exact_mod_cast h
  exact_mod_cast hle.trans h'

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

theorem desc_of_baseChange : GlobalTheory.Published.AbelianDeRham →
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
      (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (b : 𝓞 F) (β : Qb),
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) ≤ 2 →
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) →
      Module.rank Qb (HdR X₀.A ⧸ LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1))
        (LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) := by
  intro hD F _ _ 𝔠 X₀ X p hp b β hrank hdisj
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hBC : m.IsBC := (hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1
  haveI : FiniteDimensional Qb (prim (dp0 Qb) (𝟙 _) X₀.A) := (GlobalTheory.Published.AbelianDeRham.Free.prim hD.1 X₀.ab X₀.dim).1
  haveI := X₀.rm.hom
  haveI := X.rm.hom
  let g₀ := primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) - β • LinearMap.id
  let g := primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) - algebraMap Qb ℂ β • LinearMap.id
  have e₀ : act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1 = g₀.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g₀, act_apply, push_apply, smul_eq_mul]
  have e : act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1 = g.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g, act_apply, push_apply, smul_eq_mul]
  have hg : ∀ c, g (m.pull c) = m.pull (g₀ c) := by
    intro c
    have k := (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)).comp m
    have e1 : primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) (m.pull c) = k.pull c :=
      GrpMor.pull_pull m (homMor (dp0 ℂ) (𝟙 _) (X.rm.act b)) k (fun _ ↦ rfl) (hp.act b) c
    have e2 : m.pull (primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) c) = k.pull c :=
      GrpMor.pull_pull (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)) m k (fun _ ↦ rfl) rfl c
    simp only [g, g₀, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smulₛₗ, e1, e2]
  rw [e₀]
  rw [e] at hrank hdisj
  exact ⟨rank_coker_desc m.pull hBC g₀ g hg hrank, disjoint_desc m.pull hBC g₀ g hg hdisj⟩

end GlobalTheory.DescRank
