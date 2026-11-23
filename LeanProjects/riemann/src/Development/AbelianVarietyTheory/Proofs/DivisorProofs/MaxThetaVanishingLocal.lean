import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormInvariantQuotientDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOrbitSmoothVectorFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataLocalSmoothVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistsInvariantPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalStabiliserInvarianceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.ThKExSimple

noncomputable def locRep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    {G : Geo σ a a'} (om : Rep σ G.V G.W) (v : Pl F) :
    UAtSub σ G.W (evFin F v) →* Module.End ℂ (Fn F a (a + a')) :=
  (om.comp (MonoidHom.inr _ _)).comp (UAtSub σ G.W (evFin F v)).subtype

theorem exsimple : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ S : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), S ≤ GlobalTheory.ThK.PolData B G.M ∧ GlobalTheory.ThKLocSS.IsSimpleOver (GlobalTheory.ThKLocSS.opsAt om v) N S := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT N hmax hker v
  set D := PolData B G.M with hDdef
  set ρ := locRep (G := G) om v with hρ
  have hρapp : ∀ g : UAtSub σ G.W (evFin F v), ρ g = om (1, g.1) := fun g => rfl
  have hinv2 : ∀ x, σ (σ x) = x := GlobalTheory.ThK.Inhab.conj_conj hT.base.cm
  let 𝒦 : Set (Subgroup (UAtSub σ G.W (evFin F v))) := {K | ∃ K' : Subgroup (UA σ G.W.J),
    K = K'.comap (UAtSub σ G.W (evFin F v)).subtype ∧ (∀ g ∈ K', g ∈ UAt σ G.W (evFin F v)) ∧
    IsCompact (K' : Set (UA σ G.W.J)) ∧ (∃ O : Set (UA σ G.W.J), IsOpen O ∧ (1 : UA σ G.W.J) ∈ O ∧
      ∀ g ∈ O, g ∈ UAt σ G.W (evFin F v) → g ∈ K')}
  obtain ⟨Bf, hadd, hsmul, hherm, hpos, hinvB, hrad⟩ := GlobalTheory.T.triple_exists_invariant_pairing hK F E σ B a a' G X om om' hT
  have hD : ∀ g : UAtSub σ G.W (evFin F v), ∀ x ∈ D, ρ g x ∈ D := fun g x hx =>
    GlobalTheory.ThKPolFin.polData_stable (GlobalTheory.T.theta_action_exists hK.base) B G.M (GlobalTheory.ThK.Inhab.pairV hT) v g.1 g.2 x hx
  have hsm := GlobalTheory.T.polynomial_data_local_smooth_vector hK F E σ B a a' G X om om' hT v
  obtain ⟨S, hSD, hS⟩ := GlobalTheory.T.hermitian_form_invariant_quotient_definite ρ 𝒦 Bf D N hD hmax.le hmax.ne
    (fun g x hx => hmax.stab.fin v g.1 g.2 x hx) hadd hsmul hherm hpos
    (fun g x hx y hy => hinvB v g.1 g.2 x hx y hy)
    (fun x hx h0 => hker x hx ((hrad x hx).1 h0))
    (by
      intro x hx
      obtain ⟨U, hU, hUx⟩ := hsm x hx
      obtain ⟨K', hK'1, hK'2, hK'3, hK'4⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hinv2 G.W v U hU
      refine ⟨K'.comap (UAtSub σ G.W (evFin F v)).subtype, ⟨K', rfl, hK'1, hK'2, hK'3⟩, fun k hk => ?_⟩
      exact hUx k.1 (hK'4 hk) k.2)
    (by
      rintro K ⟨K', rfl, hK'1, hK'2, -⟩ x hx
      obtain ⟨U, hU, hUx⟩ := hsm x hx
      have := GlobalTheory.T.compact_orbit_smooth_vector_finite (om.comp (MonoidHom.inr _ _)) K' hK'2 x ⟨U, hU, fun h hh hk => hUx h hh (hK'1 h hk)⟩
      refine this.subset ?_
      rintro y ⟨k, hk, rfl⟩
      exact ⟨k.1, hk, rfl⟩)
    (by
      rintro K ⟨K', rfl, hK'1, hK'2, hK'3⟩ x hx
      obtain ⟨s, hsD, hs⟩ := GlobalTheory.T.triple_local_stabiliser_invariance hK F E σ B a a' G X om om' hT v K' hK'1 hK'2 hK'3 x hx
      refine ⟨s, hsD, fun y hy hfix => ?_⟩
      obtain ⟨z, hz, hIz⟩ := hs y hy (fun k hk => hfix ⟨k, hK'1 k hk⟩ hk)
      have hyD : y ∈ D := by
        refine Submodule.span_le.2 ?_ hy
        rintro _ ⟨g, rfl⟩
        exact hD g x hx
      have hzD : z ∈ D := Submodule.span_le.2 hsD hz
      exact ⟨z, hz, (hrad _ (D.sub_mem hyD hzD)).2 hIz⟩)
  refine ⟨S, hSD, ?_⟩
  have hT' : Set.range ρ = GlobalTheory.ThKLocSS.opsAt om v := by
    ext T
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  rwa [← hT']

end GlobalTheory.ThKExSimple

end
