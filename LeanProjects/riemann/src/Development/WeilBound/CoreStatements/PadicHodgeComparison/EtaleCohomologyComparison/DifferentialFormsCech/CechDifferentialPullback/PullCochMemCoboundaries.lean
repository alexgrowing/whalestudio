import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh

section Ref

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
  {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
  {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
  (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))

include hτ in

theorem inter_le_map {n : ℕ} (t : Fin n → ι) : inter U t ≤ (Opens.map f).obj (inter V (τ ∘ t)) := by
  intro x hx
  rw [mem_inter_iff] at hx
  change f x ∈ inter V (τ ∘ t)
  rw [mem_inter_iff]
  exact fun a => hτ (t a) (hx a)

def pullCoch (n : ℕ) : Cochain P V n →+ Cochain Q U n where
  toFun σ t := res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (σ (τ ∘ t)))
  map_zero' := by funext t; simp
  map_add' σ σ' := by funext t; simp

omit hτ in
theorem app_res_map {A B : Opens Y} (h : A ≤ B) (x : P.obj (op B)) :
    φ.app (op A) (res P h x) = res Q ((Opens.map f).monotone h) (φ.app (op B) x) := by
  simp only [res, ← ConcreteCategory.comp_apply, φ.naturality]
  rfl

theorem pullCoch_d (n : ℕ) (σ : Cochain P V n) :
    pullCoch f φ V U τ hτ (n + 1) (d P V n σ) = d Q U n (pullCoch f φ V U τ hτ n σ) := by
  funext t
  simp only [pullCoch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [app_res_map, res_res, res_res]
  rfl

theorem pullCoch_mem_cocycles {n : ℕ} {σ : Cochain P V n} (hσ : σ ∈ cocycles P V n) :
    pullCoch f φ V U τ hτ n σ ∈ cocycles Q U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← pullCoch_d, hσ, map_zero]

theorem pullCoch_mem_coboundaries {n : ℕ} {σ : Cochain P V n} (hσ : σ ∈ coboundaries P V n) :
    pullCoch f φ V U τ hτ n σ ∈ coboundaries Q U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨ρ, rfl⟩ := hσ
    exact ⟨pullCoch f φ V U τ hτ n ρ, (pullCoch_d f φ V U τ hτ n ρ).symm⟩

def cechPullH (n : ℕ) : cechH P V n →+ cechH Q U n :=
  QuotientAddGroup.map _ _ (AddMonoidHom.codRestrict ((pullCoch f φ V U τ hτ n).comp (cocycles P V n).subtype)
    (cocycles Q U n) fun σ => pullCoch_mem_cocycles f φ V U τ hτ σ.2) fun σ hσ => by
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      exact pullCoch_mem_coboundaries f φ V U τ hτ (AddSubgroup.mem_addSubgroupOf.1 hσ)

theorem cechPullH_cls {n : ℕ} (σ : Cochain P V n) (hσ : d P V n σ = 0) :
    cechPullH f φ V U τ hτ n (cls σ hσ) =
      cls (pullCoch f φ V U τ hτ n σ) (by rw [← pullCoch_d, hσ, map_zero]) := rfl

end Ref

section Pull

open GlobalTheory.SheafPull

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}

def hPull (φ : G ⟶ (push f).obj G') (n : ℕ) : Sheaf.H.{0} G n →+ Sheaf.H.{0} G' n :=
  (GlobalTheory.SiteCoh.terminalEquiv G' n isTerminalTop).toAddMonoidHom.comp
    ((pull.{0, 0} f φ n (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)).comp
      (GlobalTheory.SiteCoh.terminalEquiv G n isTerminalTop).symm.toAddMonoidHom)

end Pull

section Forms

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def CO (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) : Type :=
  cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j

instance (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) :
    AddCommGroup (CO q U a j) :=
  inferInstanceAs (AddCommGroup (cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j))

instance (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) :
    Module K (CO q U a j) :=
  letI := GlobalTheory.HodgeCoh.algΓ q
  inferInstanceAs (Module K (cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j))

def cechPull {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i)) (a j : ℕ) :
    CO p V a j →+ CO q U a j :=
  cechPullH u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ j

def cechOmAdd (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ) :
    CO q U a j ≃+ HodgeC q a j :=
  (cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j).trans (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm

end Forms

end CrystallineSemistableComparison.Om.Cech
