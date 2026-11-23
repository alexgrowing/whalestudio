import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFixesVacuumNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandPairIrreduciblePairingSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalUnitaryRepresentationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCompactConjugateRelativeIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalAntiInvolutionGelfandTrickStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLine

theorem fixed_eq_smul_vac : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ k ∈ KAt σ G.W v, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, k)) φ φ₁ → Rf.p v φ₁ = Rf.p v φ) → ∃ c : ℂ, Rf.p v φ = c • Rf.p v (G.M.vac v) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v hv φ hφ hfix
  have hvT : v ∉ X.T := fun hT => hv.false (B.τ ⟨v, hM.triple.chars.sub hT⟩)
  obtain ⟨ρ, hex, hρ⟩ := GlobalTheory.T.matched_local_unitary_representation_exists hKP F E σ B a a' G X om om' R Rf hM v
  obtain ⟨θ, h1, h2, h3⟩ := GlobalTheory.T.spherical_anti_involution_gelfand_trick F E σ B a a' G X om om' hM.triple v hv
  have hcomm := GlobalTheory.T.spherical_compact_conjugate_relative_index F E σ B a a' G X om om' hM.triple v
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    have h1 : Module.rank ℂ ((SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v)) ≤ Cardinal.aleph0 :=
      (rank_map_le _ _).trans (GlobalTheory.SBCount.rank_sb_localField_le v _)
    rwa [hM.fin.onto v, rank_top] at h1
  have hirr : ∀ N : Submodule ℂ (Rf.Pi v), (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    refine hM.fin.irred v N (fun h hh φ₀ hφ₀ φ₁ hφ₁ hA hN' => ?_)
    rw [← hρ ⟨h, hh⟩ φ₀ hφ₀ φ₁ hφ₁ hA]
    exact hN _ _ hN'
  have hvac : G.M.vac v ∈ SB (Fin a × Fin (a + a') → Fv F v) := (hM.triple.geo.hM.vac v).1
  have hx0 : ∀ k ∈ (locK σ G.W v).subgroupOf (locU σ G.W v), ρ k (Rf.p v (G.M.vac v)) = Rf.p v (G.M.vac v) :=
    fun k hk => hρ k _ hvac _ hvac (GlobalTheory.T.compact_fixes_vacuum_nonsplit F E σ B a a' G X om om' hM.triple v hv hvT k (Subgroup.mem_subgroupOf.1 hk))
  have hx : ∀ k ∈ (locK σ G.W v).subgroupOf (locU σ G.W v), ρ k (Rf.p v φ) = Rf.p v φ := by
    intro k hk
    obtain ⟨φ₁, hφ₁, hA⟩ := hex k φ hφ
    rw [hρ k φ hφ φ₁ hφ₁ hA]
    exact hfix k (Subgroup.mem_subgroupOf.1 hk) φ₁ hφ₁ hA
  exact GlobalTheory.T.gelfand_pair_irreducible_pairing_symmetric _ _ hcomm θ h1 h2 h3 (Rf.Pi v) ρ hrank hirr _ _ hx0 hx (hM.fin.sph v hvT).2

end GlobalTheory.SphLine

end
