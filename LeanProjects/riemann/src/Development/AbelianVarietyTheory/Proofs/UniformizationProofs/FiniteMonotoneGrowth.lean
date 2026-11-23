import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSectionStatement
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmpleGrowth

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

theorem top_add {M : LB X} (a b : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (a + b)).f k = (SecOnR.topEquiv f M a).f k + (SecOnR.topEquiv f M b).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_add, map_add]

theorem top_smul {M : LB X} (c : K) (a : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (c • a)).f k = cst f (M.U k) c * (SecOnR.topEquiv f M a).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]

theorem top_ext {M : LB X} {a b : SecOnR f M ⊤}
    (h : ∀ k, (SecOnR.topEquiv f M a).f k = (SecOnR.topEquiv f M b).f k) : a = b :=
  (SecOnR.topEquiv f M).injective (by
    generalize SecOnR.topEquiv f M a = x at h ⊢
    generalize SecOnR.topEquiv f M b = y at h ⊢
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : x = y := funext h
    rfl)

theorem top_zero {M : LB X} (k : M.ι) : (SecOnR.topEquiv f M 0).f k = 0 := by
  rw [SecOnR.topEquiv_f, SecOnR.coord_zero, map_zero]

def linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M)
    (hadd : ∀ a b k, (φ (a + b)).f k = (φ a).f k + (φ b).f k)
    (hsmul : ∀ (c : K) a k, (φ (c • a)).f k = cst f (M.U k) c * (φ a).f k) :
    V →ₗ[K] SecOnR f M ⊤ where
  toFun a := (SecOnR.topEquiv f M).symm (φ a)
  map_add' a b := top_ext f fun k => by
    simp only [top_add, LinearEquiv.apply_symm_apply, hadd]
  map_smul' c a := top_ext f fun k => by
    simp only [top_smul, LinearEquiv.apply_symm_apply, hsmul, RingHom.id_apply]

theorem top_linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M) (hadd hsmul)
    (a : V) : SecOnR.topEquiv f M (linTop f φ hadd hsmul a) = φ a :=
  (SecOnR.topEquiv f M).apply_symm_apply _

def mulPw {H : LB X} (s : LB.Sec H) (t : ℕ) (σ : LB.Sec (pw H t)) : LB.Sec (pw H (t + 1 : ℕ)) where
  f := fun k => s.f k * (show Γ(X, H.U k) from σ.f k)
  compat := fun k l => by
    have h₁ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k) =
      (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l) := s.compat k l
    have h₂ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (σ.f k) =
      (H.g k l ^ (t : ℤ)).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (σ.f l) := σ.compat k l
    change rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k * (show Γ(X, H.U k) from σ.f k)) =
      (H.g k l ^ ((t + 1 : ℕ) : ℤ)).val *
        rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l * (show Γ(X, H.U l) from σ.f l))
    rw [map_mul, map_mul, h₁, h₂, zpow_natCast, zpow_natCast, pow_succ, Units.val_mul]
    ring

def mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) :
    SecOnR f (pw H t) ⊤ →ₗ[K] SecOnR f (pw H (t + 1 : ℕ)) ⊤ :=
  linTop f (fun a => mulPw s t (SecOnR.topEquiv f _ a))
    (fun a b k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_add f a b k)).trans
      (mul_add (s.f k) (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) a).f k)
        (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) b).f k)))
    (fun c a k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_smul f c a k)).trans
      (mul_left_comm _ _ _))

theorem top_mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) (a : SecOnR f (pw H t) ⊤) :
    SecOnR.topEquiv f (pw H (t + 1 : ℕ)) (mulLin f s t a) = mulPw s t (SecOnR.topEquiv f (pw H t) a) :=
  top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral X] {H : LB X} (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) (t : ℕ) :
    Function.Injective (mulLin f s t) := by
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let W : X.Opens := X.basicOpen (s.f k₀)
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  have hu : IsUnit (rs X hWU (s.f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : s.f k₀ * (show Γ(X, H.U k₀) from (SecOnR.topEquiv f (pw H t) a).f k₀) = 0 := by
    have e := top_mulLin f s t a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (pw H (t + 1 : ℕ)) => σ.f k₀) e).symm.trans
      (top_zero f (M := pw H (t + 1 : ℕ)) k₀)
  have h' := congrArg (rs X hWU) h
  rw [map_mul, map_zero, hu.mul_right_eq_zero] at h'
  exact top_ext f fun k =>
    (SecGrowth.sec_eq_zero (M := pw H t) (SecOnR.topEquiv f _ a) (k₀ := k₀) hWU h' k).trans
      (top_zero f k).symm

theorem finite_of_polynomial {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (t : ℕ)
    (h : ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) :
    Module.Finite K (SecOnR f (pw H t) ⊤) := by
  haveI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t) :=
    Submodule.finiteDimensional_of_le (S₂ := MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t)
      fun F hF => (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (MvPolynomial.IsHomogeneous.totalDegree_le hF)
  refine Module.Finite.of_surjective
    (linTop f (V := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t)
      (fun F => SecGrowth.polySec f s F.2)
      (fun a b k => map_add (MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k)) a.1 b.1)
      (fun c a k => ?_)) fun a => ?_
  · change MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) (c • a.1) =
      cst f (H.U k) c * MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) a.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  · obtain ⟨F, hF, hFa⟩ := h (SecOnR.topEquiv f _ a)
    refine ⟨⟨F, hF⟩, top_ext f fun k => ?_⟩
    exact (congrArg (fun σ : LB.Sec (pw H t) => σ.f k) (top_linTop f _ _ _ _)).trans (hFa k).symm

theorem finite_monotone_growth : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) ∧ (∀ t t' : ℕ, t ≤ t' → Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (f) (pw H t') ⊤)) ∧ ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K (SecOnR (f) (pw H t) ⊤) ∧ Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ C * t ^ g := by
  intro K _ X _ f g hf H n s hH hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection K X f H n s hH hs
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hinj := mulLin_injective f (s i) hi
  have hfin : ∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤) := fun t => by
    have h : ∀ d t : ℕ, t₀ ≤ t + d → Module.Finite K (SecOnR f (pw H t) ⊤) := by
      intro d
      induction d with
      | zero => exact fun t ht => finite_of_polynomial f s t (ht₀ t ht)
      | succ d ih =>
        intro t ht
        haveI := ih (t + 1) (by omega)
        exact Module.Finite.of_injective _ (hinj t)
    exact h t₀ t (Nat.le_add_left _ _)
  refine ⟨hfin, fun t t' h => ?_, ?_⟩
  · exact monotone_nat_of_le_succ (f := fun t : ℕ => Module.finrank K (SecOnR f (pw H t) ⊤))
      (fun t => LinearMap.finrank_le_finrank_of_injective (hinj t)) h
  · exact SecGrowth.growth_of_veryAmpleBy f s hs g t₀ ht₀
      (fun B _ _ _ r => finrank_totalDegree_image_growth K B _ _ r)
      (trdeg_eq_of_smoothOfRelativeDimension K X f g hf)
      (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR.topEquiv f _)
      (fun t a b k => top_add f a b k) (fun t c a k => top_smul f c a k)
      (fun t a ha => top_ext f fun k => (ha k).trans (top_zero f k).symm)
      (fun t σ => ⟨(SecOnR.topEquiv f _).symm σ, fun k => by rw [LinearEquiv.apply_symm_apply]⟩)

end GlobalTheory.VeryAmpleGrowth
