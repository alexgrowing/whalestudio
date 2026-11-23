import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem exists_gl_preimage {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) (hφ : Function.Injective φ) {n : ℕ}
    (u : GL (Fin n) C) (h : ∀ a b, u.val a b ∈ Set.range φ ∧ (u⁻¹).val a b ∈ Set.range φ) :
    ∃ u0 : GL (Fin n) O, Matrix.GeneralLinearGroup.map φ u0 = u := by
  choose M hM using fun a b => (h a b).1
  choose M' hM' using fun a b => (h a b).2
  have e1 : φ.mapMatrix (Matrix.of M) = u.val := by ext a b; simp [hM]
  have e2 : φ.mapMatrix (Matrix.of M') = (u⁻¹).val := by ext a b; simp [hM']
  have inj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) C) := fun A B hAB => by
    ext a b; exact hφ (congrFun (congrFun hAB a) b)
  have h1 : Matrix.of M * Matrix.of M' = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have h2 : Matrix.of M' * Matrix.of M = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  refine ⟨⟨Matrix.of M, Matrix.of M', h1, h2⟩, Units.ext ?_⟩
  exact e1

theorem det_map_gl {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {n : ℕ} (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem lamG_mem_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  intro l _ ι _ _ n lamW c F hinj hlam u hu z
  choose u0 hu0 using fun τ => exists_gl_preimage F.emb hinj (u τ) (hu τ)
  have hu' : u = fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ) := funext fun τ => (hu0 τ).symm
  subst hu'
  have hs : ((∏ τ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (u0 τ)) ^ c τ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      F.emb ((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) := by
    simp only [det_map_gl, ← map_zpow, ← map_prod]
    rfl
  have key : ∀ x, lamG (PadicAlgCl l) n lamW c (fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ)) (GlobalTheory.LatBC.bc F.emb n lamW x) =
      GlobalTheory.LatBC.bc F.emb n lamW (((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) • grp F.O n lamW u0 x) := by
    intro x
    rw [lamG_apply, hs, ← GlobalTheory.LatBC.bc_grp, LinearMap.map_smulₛₗ]
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 hz
    exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨_, (key x).symm⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.LatBC.latD_iff F lamW hlam _).1 hz
    refine (GlobalTheory.LatBC.latD_iff F lamW hlam _).2 ⟨_, ?_, (key x).symm⟩
    exact Submodule.smul_mem _ _ (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta F.O ι (fun _ => n) (fun _ => n) (fun _ => le_rfl)
      (fun τ => res n (lamW τ)) u0 x hx)

end GlobalTheory.FrameRead
