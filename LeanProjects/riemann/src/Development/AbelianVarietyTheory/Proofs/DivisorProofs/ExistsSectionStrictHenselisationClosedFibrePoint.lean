import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem exists_section_strictHenselisation_at_closed : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  intro hKey T E _ _ _ _ _ _ _ _ hT y _ hyT hyne q hq hqu DE _ _ actE htor
  obtain ⟨S, _, _, _, _, _, _, _, _, hmax, hflat, hloc, φ, hφ, hsh⟩ := GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt T E y
  have hKey' := hKey
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith at hKey'
  have htriv : GlobalTheory.LocAcyc.TorsorsTrivial (GlobalTheory.LocAcyc.GenFib T S) q :=
    hKey' T S hT (y.comap (algebraMap (Polynomial T) E)) φ hφ hsh hyT hyne q hq hqu
  have hMN : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors T)).comap (algebraMap E S) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hx
    exact Submonoid.mem_map.mpr ⟨t, ht, IsScalarTower.algebraMap_apply T E S t⟩
  let f : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T S :=
    IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S) hMN
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) := f.toAlgebra
  obtain ⟨act', -, htor'⟩ :=
    GlobalTheory.T.isZModTorsorFiniteProjective_baseChange (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) DE q hq actE htor
  obtain ⟨σ⟩ := (GlobalTheory.LocAcyc.torsorsTrivial_iff _ q).mp htriv _ act' htor'
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hmax, hflat, hloc, σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        DE →ₐ[GlobalTheory.LocAcyc.GenFib T E] GlobalTheory.LocAcyc.GenFib T S ⊗[GlobalTheory.LocAcyc.GenFib T E] DE).toRingHom,
    fun e => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  have hσ := σ.commutes (algebraMap (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S)
    (algebraMap E (GlobalTheory.LocAcyc.GenFib T E) e))
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hσ
  rw [hσ, RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq hMN e

end GlobalTheory.LocAcyc
