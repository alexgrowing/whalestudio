import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegOneEMul

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

def topEquiv : (⊤ : AddSubmonoid (Gam n d)) ≃ Gam n d := Equiv.Set.univ _

def lrBasis : Module.Basis (Gam n d) K (Lr K n d) :=
  (Module.Basis.ofRepr (AddMonoidAlgebra.coeffLinearEquiv K)).reindex topEquiv

theorem lrBasis_apply (g : Gam n d) : lrBasis (K := K) g = monL K g := by
  rw [lrBasis, Module.Basis.reindex_apply, Module.Basis.coe_ofRepr]
  rfl

def setEquiv (a : ℕ) : {D : Finset (E n d) // D.card = a} ≃ Set.powersetCard (Fin (n + d)) a where
  toFun D := ⟨D.1.map finSumFinEquiv.toEmbedding, by simpa using D.2⟩
  invFun s := ⟨s.1.map finSumFinEquiv.symm.toEmbedding, by simp⟩
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

theorem wedge_basis (bΩ : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K]) (h : ∀ e, bΩ e = dl e) (a : ℕ) :
    ∃ c : Module.Basis {D : Finset (E n d) // D.card = a} (Lr K n d) (Om K (Lr K n d) a),
      ∀ D, c D = wedge (K := K) (enumD D) := by
  refine ⟨((bΩ.reindex finSumFinEquiv).exteriorPower a).reindex (setEquiv a).symm, fun D => ?_⟩
  rw [Module.Basis.reindex_apply, exteriorPower.basis_apply]
  simp only [Equiv.symm_symm]
  unfold exteriorPower.ιMulti_family wedge
  congr 1
  funext i
  simp only [Function.comp_apply, Module.Basis.reindex_apply, h]
  rfl

theorem monW_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  intro K _ n d a
  obtain ⟨bΩ, h⟩ := GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis.exists_basis_dl (K := K) (n := n) (d := d)
  obtain ⟨c, hc⟩ := wedge_basis bΩ h a
  refine ⟨lrBasis.smulTower c, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, lrBasis_apply, hc]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
