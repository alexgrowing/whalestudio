import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
import Mathlib

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Lit.KT

section Lin

variable {Γ k : Type} [Group Γ] [Field k]

private def diagRep (χ : Fin 2 → Γ →* kˣ) : Γ →* GL (Fin 2) k :=
  MonoidHom.toHomUnits ⟨⟨fun g => Matrix.diagonal fun i => (χ i g : k), by simp⟩, fun s t => by
    simp [Matrix.diagonal_mul_diagonal]⟩

end Lin

open GlobalTheory.WeilDeligne Polynomial in

private theorem norm_root {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (hu : ∀ s ∈ Ine (F := F) A, r s = 1) {x : WD h} (hx : IsWDOf ι r x) {s : ℝ} (ht : (x.lpTw s).tempered) {b : ℂ}
    (hb : ((r ((frob h : Weil h) : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot b) :
    ‖b‖ = (normV w : ℝ) ^ s := by
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := id hx
  have hxu : x.unr := e ▸ (hN.unr_wdOf_iff hl ht' ι).2 hu
  have hc := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  rw [e] at hc
  have hr : (x.charPol (frob h)⁻¹).IsRoot b := by
    rw [hc]
    exact hb
  have hm : b ≠ 0 ∧ b⁻¹ ∈ x.eig (frob h) := by
    obtain ⟨m, a, rfl⟩ := WD.exists_rep x
    rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hr
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have h1 : v = b • a.ρ (frob h) v := by
      rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hv.2 (by simpa using h1)
    refine ⟨hb0, ?_⟩
    rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
  have h1 := (WD.tempered_unr _ ((WD.unr_tw x s).2 hxu)).1 ht (b⁻¹ * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [WD.frobEig_tw x s hxu]
    exact Multiset.mem_map_of_mem _ hm.2)
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)),
    Complex.ofReal_re, inv_mul_eq_one₀ (norm_ne_zero_iff.2 hm.1)] at h1
  exact h1

end UpperTheory.V.Lit.KT
