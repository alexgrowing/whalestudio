import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinfStatement

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.ConstMu

theorem frobenius_ofPadic {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem frobenius_phiInv' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem frobenius_mu' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv']

theorem existsUnique_lattMap : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε g hg
  obtain ⟨ec, hec⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
  obtain ⟨em, hem⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
  have eig := GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf p C v O hv ε hε
  set l : latt (PDivGroup.mu p O) := em.symm 1 with hl_def
  have hl : l.1 (epsTate hε) = Sandwich.mu ε := by
    rw [← hem l, hl_def, LinearEquiv.apply_symm_apply, mul_one]
  have htate : ∀ t : (PDivGroup.mu p O).Tate, ∃ a : ℤ_[p], t = a • epsTate hε := by
    intro t
    obtain ⟨a, rfl⟩ := (epsEquiv hε).surjective t
    exact ⟨a, rfl⟩
  have hlval : ∀ a : ℤ_[p], l.1 (a • epsTate hε) = ofPadic p O a * Sandwich.mu ε := by
    intro a
    rw [map_smulₛₗ, hl, smul_eq_mul]
  have hgen : ∀ y : latt (PDivGroup.mu p O), y = em y • l := by
    intro y
    apply em.injective
    rw [map_smul, hl_def, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hpull : ∀ (f : const p O ⟶ PDivGroup.mu p O) (y : latt (PDivGroup.mu p O)),
      ec (lattMap f y) = y.1 (tateMap _ _ O f (constGen p O)) := by
    intro f y
    rw [hec]
    rfl

  set b : Ainf p O := ((g l).1 (constGen p O)) with hb_def
  have hbeig : WittVector.frobenius b = WittVector.frobenius (xi ε) * b := by
    have h1 := hg l (WittVector.frobenius (xi ε) • l) (by
      intro t
      obtain ⟨a, rfl⟩ := htate t
      rw [Submodule.coe_smul, LinearMap.smul_apply, hlval, smul_eq_mul, map_mul,
        frobenius_ofPadic, frobenius_mu']
      ring) (constGen p O)
    rw [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hb_def, ← h1]
  obtain ⟨c, hc, hcu⟩ := eig b hbeig
  have hfix : ∀ f : const p O ⟶ PDivGroup.mu p O, lattMap f = g ↔
      ec (lattMap f l) = ec (g l) := by
    intro f
    constructor
    · intro h; rw [h]
    · intro h
      apply LinearMap.ext
      intro y
      rw [hgen y, map_smul, map_smul, ec.injective h]
  refine ⟨constHom (PDivGroup.mu p O) (c • epsTate hε), ?_, ?_⟩
  · show lattMap _ = g
    rw [hfix, hpull, tateMap_constHom, hlval, hec, hc]
  · intro f hf
    rw [hfix, hpull, hec] at hf
    obtain ⟨a, ha⟩ := htate (tateMap _ _ O f (constGen p O))
    rw [ha, hlval] at hf
    have hac : a = c := hcu a hf
    rw [← (constHom (PDivGroup.mu p O)).apply_symm_apply f, constHom_symm_apply, ha, hac]

end GlobalTheory.PDivLat.ConstMu
