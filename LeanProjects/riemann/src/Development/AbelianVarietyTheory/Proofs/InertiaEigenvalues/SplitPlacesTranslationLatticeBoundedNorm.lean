import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqSmulMulVecMemHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongOneOfSuppAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatCmpQ

theorem nsmul_mulVec_eq {R : Type*} [CommRing R] {n : ℕ} (N m : ℕ) (g w : Matrix (Fin n) (Fin n) R)
    (hwe : ∀ i j, (N : R) * (g i j - (1 : Matrix (Fin n) (Fin n) R) i j) = (m : R) * w i j) (y : Fin n → R) :
    N • (g *ᵥ y) = N • y + m • (w *ᵥ y) := by
  have e1 : (N : R) • (g - 1) = (m : R) • w := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    exact hwe i j
  have e2 : ((N : R) • (g - 1)) *ᵥ y = N • (g *ᵥ y) - N • y := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_sub]
  have e3 : ((m : R) • w) *ᵥ y = m • (w *ᵥ y) := by
    rw [Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
  rw [← e3, ← e1, e2]
  abel

set_option maxHeartbeats 1000000 in

theorem step {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a N : ℕ)
    (h1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) (h2 : ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n)
    (g : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hg : ∀ i j, ∃ w ∈ intAE D, ((N : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (g i j - (1 : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w)
    {y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    N • (g *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  choose w hw hwe using hg
  have key := nsmul_mulVec_eq N (a ^ 2) g (Matrix.of w) hwe y
  rw [key]
  exact add_mem (AddSubgroup.nsmul_mem _ hy N) (GlobalTheory.HatIntSmul.sq_smul_mulVec_mem_hat D n Λ a h1 h2 _ hw y hy)

set_option maxHeartbeats 1000000 in

theorem latAt_translate_bounded : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  intro D ρ hρ i j b Q h hQ hS hsupp
  have hΛ : ∀ x, x ∈ (ρ.B i j b).F.ΛS ↔ x ∈ L0c D (Vc D j) := by
    obtain ⟨_, _, _, h1, h2⟩ := hρ.latS i j b
    intro x
    constructor
    · intro hx; simpa using h2 x hx
    · intro hx; simpa using h1 x hx
  obtain ⟨a, ha, hs1, hs2⟩ := GlobalTheory.LatSandwich.sandwich D (Vc D j) (ρ.B i j b).F.ΛS hΛ
  obtain ⟨c, hc⟩ := GlobalTheory.SuppIntCong.cong_one_of_suppAt D (Vc D j) Q hQ a ha hS hsupp
  have ev : ∀ x : Fin (Vc D j).rank → D.host.E, (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x) k)) =
      (normProd Q ^ c) • (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] x k) := by
    intro x
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, Nat.cast_smul_eq_nsmul]
    exact map_nsmul ((TensorProduct.mk D.host.F (Af D.host.F) D.host.E) 1) _ _
  have hmul : ((finPt (Vc D j) (h * hQ)).1⁻¹).val = (finHom (Vc D j) hQ)⁻¹.val * ((finPt (Vc D j) h).1⁻¹).val := by
    have e : (finPt (Vc D j) (h * hQ)).1 = finHom (Vc D j) h * finHom (Vc D j) hQ := map_mul (finHom (Vc D j)) h hQ
    rw [e, _root_.mul_inv_rev, Units.val_mul]
    rfl
  have hmul' : ((finPt (Vc D j) h).1⁻¹).val = (finHom (Vc D j) hQ).val * ((finPt (Vc D j) (h * hQ)).1⁻¹).val := by
    rw [hmul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨c, fun x hx => ?_, fun x hx => ?_⟩
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    rw [ev x, Matrix.mulVec_smul, hmul, ← Matrix.mulVec_mulVec]
    exact step _ a _ hs1 hs2 _ (fun i j => (hc i j).2) hx
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    have hst := step _ a _ hs1 hs2 _ (fun i j => (hc i j).1) hx
    rw [Matrix.mulVec_mulVec, ← hmul'] at hst
    rw [ev x, Matrix.mulVec_smul]
    exact hst

end GlobalTheory.LatCmpQ
