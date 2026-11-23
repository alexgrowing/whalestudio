import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceDarbouxWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceIdempotentLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeDoubleVectorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitVacAny

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hgS : omd gd S = c • S := by
    rw [hb]
    funext x
    simp only [hS, boxFun, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨e, θ, he1, he2, he3, hθ1, hθ2, hθ3, hθ4⟩ := GlobalTheory.T.split_place_idempotent_lattice σ B hT.base v hsp₀
  obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.split_lattice_double_vector σ G.V v e θ he1 he2 he3 hθ1 hθ2 hθ3 (hθ4 G.V)
  obtain ⟨h1, h2⟩ := hW k hk gd hgd hgdK
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.split_place_darboux_weil F E σ B a a' G X om om' hT v hsp₀ hv d' hd' dd omd hdc hsp r hr w₀ hw₀
  have hSne : S ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := hS0
    exact hx (by rw [h]; rfl)
  have hμ0 : μ ≠ 0 := fun h0 => by
    apply hSne
    have e : omd w₀⁻¹ (omd w₀ S) = S := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← e, hμ, h0, zero_smul, map_zero]
  have hinv : omd w₀⁻¹ S = μ⁻¹ • S := by
    have e : omd w₀⁻¹ (omd w₀ S) = S := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hμ, LinearMap.map_smul] at e
    calc omd w₀⁻¹ S = μ⁻¹ • (μ • omd w₀⁻¹ S) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • S := by rw [e]
  have hp : omd (w₀ * gd * w₀⁻¹) S = c • S := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, LinearMap.map_smul, hgS,
      LinearMap.map_smul, LinearMap.map_smul, hμ, smul_smul, smul_smul]
    rw [show μ⁻¹ * c * μ = c by field_simp]
  exact GlobalTheory.SplitVacV.siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 _ h1 h2 c hp

end GlobalTheory.SplitVacAny
