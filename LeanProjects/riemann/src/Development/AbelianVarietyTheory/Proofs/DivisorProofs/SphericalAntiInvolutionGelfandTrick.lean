import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPrimeNonsplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualScaledHermitianInertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryIsoStabilizerStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLine

theorem inv_mem_locK_mul_locK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∀ g ∈ locU σ G.W v, ∃ x ∈ locK σ G.W v, ∃ y ∈ locK σ G.W v, g⁻¹ = x * g * y := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv g hg
  have hσ : IsCMExt F E σ := hT.base.cm
  obtain ⟨w, h, hw⟩ := GlobalTheory.T.exists_inert_prime_nonsplit_place F E σ hσ hT.base.unram v hv
  obtain ⟨δ, hδ, hH, hsd⟩ := GlobalTheory.T.exists_self_dual_scaled_hermitian_inert F E σ B _ _ _ G.W hσ hT.base.unram hT.geo.hW v w h hw
  have hlat := hT.geo.hW.lat
  obtain ⟨e1, he1⟩ := GlobalTheory.T.local_unitary_iso_stabilizer F E σ (InertChart.conj_conj hσ) _ G.W v δ hδ hlat.fg
  obtain ⟨-, hI⟩ := exists_isInertChart σ hσ v
  obtain ⟨-, ⟨c, hc, -⟩, -, -, hC⟩ := hI w h hw
  obtain ⟨⟨ϖ, hU⟩, hE⟩ := hC c hc
  obtain ⟨e2, he2, -⟩ := hE _ _ _ hH hlat.fg hlat.span_eq_top hsd
  let e := e1.trans e2
  have hK : ∀ k : locU σ G.W v, k.1 ∈ locK σ G.W v ↔ e k ∈ Formalism.UG.KU c (a + a') := fun k =>
    (he1 k).trans (he2.2.2 _)
  have hint : ∀ i j, Formalism.UG.antiJ (w.adicCompletion E) (a + a') i j ∈ Formalism.UG.intL (w.adicCompletion E) := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL (w.adicCompletion E)) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := w.adicCompletion E) (n := a + a')) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, ek⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ
    (g := ((e ⟨g, hg⟩ : Formalism.UG.GU c (a + a')) : GL (Fin (a + a')) (w.adicCompletion E))) (by
      intro i j
      rw [hJe]
      simp only [Formalism.UG.antiJ, add_comm i.val j.val]
      split_ifs <;> simp) (by rw [hJe]; exact (e ⟨g, hg⟩).2)
  rw [hJe] at hk₁ hk₂
  let K₁ : Formalism.UG.GU c (a + a') := ⟨k₁, hk₁.1⟩
  let K₂ : Formalism.UG.GU c (a + a') := ⟨k₂, hk₂.1⟩
  have hK₁ : K₁ ∈ Formalism.UG.KU c (a + a') := hk₁
  have hK₂ : K₂ ∈ Formalism.UG.KU c (a + a') := hk₂
  have key : (⟨g, hg⟩ : locU σ G.W v)⁻¹ = e.symm K₁ * ⟨g, hg⟩ * e.symm K₂ := by
    apply e.injective
    rw [map_inv, map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Subtype.ext ek
  refine ⟨(e.symm K₁).1, (hK _).2 (by rw [MulEquiv.apply_symm_apply]; exact hK₁),
    (e.symm K₂).1, (hK _).2 (by rw [MulEquiv.apply_symm_apply]; exact hK₂), ?_⟩
  exact congrArg Subtype.val key

theorem gelfand_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∃ θ : GlobalTheory.SphLine.locU σ G.W v → GlobalTheory.SphLine.locU σ G.W v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ (GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v),
        ∃ b ∈ (GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v), θ g = a * g * b := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  refine ⟨fun x => x⁻¹, fun x y => mul_inv_rev x y, fun x => inv_inv x, fun g => ?_⟩
  obtain ⟨x, hx, y, hy, e⟩ := inv_mem_locK_mul_locK F E σ B a a' G X om om' hT v hv g.1 g.2
  exact ⟨⟨x, locK_le_locU σ G.W v hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨y, locK_le_locU σ G.W v hy⟩,
    Subgroup.mem_subgroupOf.2 hy, Subtype.ext e⟩

end GlobalTheory.SphLine

end
