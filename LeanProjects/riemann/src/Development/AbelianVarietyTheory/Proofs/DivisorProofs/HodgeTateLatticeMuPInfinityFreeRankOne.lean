import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.MuLattice

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}

def muMap (hε : IsPrimitiveSystem ε) (a : Ainf p O) : TDual (PDivGroup.mu p O) where
  toFun t := ofPadic p O ((epsEquiv hε).symm t) * a
  map_add' s t := by rw [map_add, map_add, add_mul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl

theorem muMap_apply (hε : IsPrimitiveSystem ε) (a : Ainf p O) (t) :
    muMap hε a t = ofPadic p O ((epsEquiv hε).symm t) * a := rfl

theorem epsEquiv_symm_eps (hε : IsPrimitiveSystem ε) : (epsEquiv hε).symm (epsTate hε) = 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℤ_[p] (epsTate hε)).symm

theorem muMap_mem (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : muMap hε (Sandwich.mu ε * a) ∈ latt (PDivGroup.mu p O) := fun n =>
  ⟨0, fun t => by
    rw [muMap_apply, ghost_mul, ghost_mul, hμ, zero_mul, mul_zero, LinearMap.zero_apply]⟩

def toLatt (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0) :
    Ainf p O →ₗ[Ainf p O] latt (PDivGroup.mu p O) where
  toFun a := ⟨muMap hε (Sandwich.mu ε * a), muMap_mem hε hμ a⟩
  map_add' a b := by
    ext t
    simp only [muMap_apply, Submodule.coe_add, LinearMap.add_apply]
    ring_nf
  map_smul' c a := by
    ext t
    simp only [muMap_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem toLatt_eps (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : (toLatt hε hμ a).1 (epsTate hε) = Sandwich.mu ε * a := by
  change ofPadic p O ((epsEquiv hε).symm (epsTate hε)) * _ = _
  rw [epsEquiv_symm_eps, map_one, one_mul]

theorem latt_mu_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  have hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0 :=
    (GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε).2.2.1
  have hdom := GlobalTheory.ainf_isDomain_and_mu_ne_zero p C v O hv ε (by simpa [zeta] using hε 1)
  haveI := hdom.1
  have hbij : Function.Bijective (toLatt hε hμ) := by
    constructor
    · intro a b hab
      have h := congrArg (fun y : latt (PDivGroup.mu p O) => y.1 (epsTate hε)) hab
      simp only [toLatt_eps] at h
      exact mul_left_cancel₀ hdom.2 h
    · intro y
      have hg : ∀ n, ghost p O n (y.1 (epsTate hε)) = 0 := fun n => by
        obtain ⟨x, hx⟩ := y.2 n
        rw [hx, Subsingleton.elim (hodgeTate (PDivGroup.mu p O) (epsTate hε)) 0, map_zero]
      obtain ⟨a, ha⟩ := GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ hg
      refine ⟨a, Subtype.ext (LinearMap.ext fun t => ?_)⟩
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change ofPadic p O ((epsEquiv hε).symm (epsEquiv hε c)) * (Sandwich.mu ε * a) = y.1 (epsEquiv hε c)
      rw [LinearEquiv.symm_apply_apply, ← ha]
      have hc : epsEquiv hε c = c • epsTate hε := rfl
      rw [hc, LinearMap.map_smulₛₗ, smul_eq_mul]
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm, fun y => ?_⟩
  have h := toLatt_eps hε hμ ((LinearEquiv.ofBijective _ hbij).symm y)
  rw [← h]
  congr 2
  exact (LinearEquiv.ofBijective _ hbij).apply_symm_apply y

end GlobalTheory.MuLattice
