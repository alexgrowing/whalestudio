import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TwistCube

open Twist

variable {X : Scheme.{0}} (F : X.Modules) {L : LB X}

theorem mulSecOfEq_zpowSec_comp (σ : LB.Sec (lbZPow L 1)) {n d e : ℤ} (a b : ℕ)
    (h₁ : n + a * 1 = d) (h₂ : d + b * 1 = e) (h₃ : n + ((a + b : ℕ) : ℤ) * 1 = e) :
    mulSecOfEq F (zpowSec σ a) h₁ ≫ mulSecOfEq F (zpowSec σ b) h₂ =
      mulSecOfEq F (zpowSec σ (a + b)) h₃ := by
  ext V s : 3
  exact mulSecOfEq_zpowSec_app σ rfl h₁ h₂ h₃ s

def powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) : F ⟶ twistZ F L c :=
  (twistZZeroIso F hL).hom ≫ mulSecOfEq F (zpowSec σ c) (by omega)

theorem powMap_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ) (h : c + j = d)
    (h' : (c : ℤ) + (j : ℤ) * 1 = d) :
    powMap F hL σ c ≫ mulSecOfEq F (zpowSec σ j) h' = powMap F hL σ d := by
  subst h
  rw [powMap, powMap, Category.assoc, mulSecOfEq_zpowSec_comp F σ c j _ _ (by push_cast; ring)]

theorem bijective_powMap_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {W : X.Opens}
    (hW : W ≤ nonzeroLocus σ) : Function.Bijective ((powMap F hL σ c).app W) := by
  rw [powMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.coe_comp]
  exact (bijective_mulSecOfEq_app hL _ (by omega) (hW.trans (nonzeroLocus_le_zpowSec hL σ c))).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app W))

variable {ι : Type} (U : ι → X.Opens)

theorem isIso_cechCubeMap_powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : IsIso (cechCubeMap ℤ V U (powMap F hL σ c)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun s => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_powMap_app F hL σ c ((cechOpen_le V U s).trans hV)

theorem cechCubeRes_naturality {G : X.Modules} (φ : F ⟶ G) {V : X.Opens} :
    cechCubeMap ℤ ⊤ U φ ≫ cechCubeRes ℤ G (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) =
      cechCubeRes ℤ F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫ cechCubeMap ℤ V U φ :=
  presheafCubeRes_naturality (sectionsPresheafMap ℤ φ) _

def cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F V U :=
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫
    inv (cechCubeMap ℤ V U (powMap F hL σ c))

theorem cubeDiv_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cubeDiv F U hL σ c hV ≫ cechCubeMap ℤ V U (powMap F hL σ c) =
      cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  simp [cubeDiv]

theorem cubeDiv_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) (s : Finset ι) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s) :
    (cechCubeMap ℤ V U (powMap F hL σ c)).app s ((cubeDiv F U hL σ c hV).app s a) =
      (cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)).app s a := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cubeDiv_comp]

theorem cechCubeMap_mul_comp_cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ)
    (h : c + j = d) (h' : (c : ℤ) + (j : ℤ) * 1 = d) {V : X.Opens} (hV : V ≤ nonzeroLocus σ) :
    cechCubeMap ℤ ⊤ U (mulSecOfEq F (zpowSec σ j) h') ≫ cubeDiv F U hL σ d hV =
      cubeDiv F U hL σ c hV := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  haveI := isIso_cechCubeMap_powMap F U hL σ d hV
  unfold cubeDiv
  rw [← Category.assoc, cechCubeRes_naturality, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
  exact congrArg (cechCubeMap ℤ V U) (powMap_comp F hL σ j c d h h')

end TwistCube

end GlobalTheory

theorem GlobalTheory.cechCube_nonzeroLocus_colimit : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  intro X F _ L hL σ₀ ι _ _ U hU
  have hVσ : nonzeroLocus σ₀ ≤ nonzeroLocus (Twist.zofSec σ₀) := (Twist.nonzeroLocus_zofSec hL σ₀).ge
  refine ⟨fun j c d h => cechCubeMap ℤ ⊤ U
      (Twist.mulSecOfEq F (Twist.zpowSec (Twist.zofSec σ₀) j) (by omega)),
    fun c => TwistCube.cubeDiv F U hL (Twist.zofSec σ₀) c hVσ, ?_, ?_, ?_, ?_⟩
  · intro j c d h
    exact TwistCube.cechCubeMap_mul_comp_cubeDiv F U hL _ j c d h _ hVσ
  · intro j j' c d e h h' h''
    exact congrArg (cechCubeMap ℤ ⊤ U) (TwistCube.mulSecOfEq_zpowSec_comp F _ j j' (by omega) _ _)
  · intro s hs b
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    obtain ⟨k, hk⟩ := (Twist.eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (Twist.zofSec σ₀)
      hA.isCompact hA.isQuasiSeparated hle hV ((Twist.twistZZeroIso F hL).hom.app _ b)).exists
    obtain ⟨a, ha⟩ := hk k (by omega)
    exact ⟨k, a, (TwistCube.bijective_powMap_app F hL _ k ((cechOpen_le _ U s).trans hVσ)).1
      ((TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) k hVσ s a).trans ha)⟩
  · intro s hs c a ha
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    have h0 : Twist.resM _ hle a = 0 := by
      have e := TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) c hVσ s a
      rw [ha, map_zero] at e
      exact e.symm
    obtain ⟨k, hk⟩ := (Twist.eventually_mulSecOfEq_zpowSec_eq_zero hL (Twist.zofSec σ₀)
      hA.isCompact hle hV.ge a h0).exists
    exact ⟨k, hk _ (by push_cast; ring)⟩
