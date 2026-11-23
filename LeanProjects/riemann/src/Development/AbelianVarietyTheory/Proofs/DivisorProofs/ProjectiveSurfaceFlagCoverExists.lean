import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSurfaceNonzeroLineQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurfaceAlterationEffectiveCartierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFiniteCompDegreeMulStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.FlagCover

theorem step (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T] (hT : IsProjSurface k T)
    (E : T.Modules) (r : ℕ) (hE : IsVB E (r + 1)) :
    ∃ (T' : Scheme.{0}) (_ : Algebra k Γ(T', ⊤)) (_ : IsIntegral T') (ρ : T' ⟶ T)
        (S : ShortComplex T'.Modules) (L : LB T'), IsProjSurface k T' ∧ ρ ≫ strHom k T = strHom k T' ∧
          IsGenFinite ρ 1 ∧ S.ShortExact ∧ Nonempty (S.X₂ ≅ (Scheme.Modules.pullback ρ).obj E) ∧ L.IsLB ∧
            Nonempty (S.X₃ ≅ toMod L) ∧ IsVB S.X₁ r := by
  obtain ⟨M, φ, hM, hφ⟩ := GlobalTheory.T.vector_bundle_surface_nonzero_line_quotient k T hT E r hE
  have := hE.isFiniteQC
  have := hM.isFiniteQC
  obtain ⟨T', _, _, ρ, hT', hc, hd, hC⟩ := GlobalTheory.T.surface_alteration_effective_cartier k T hT (QCoh.annihilatorSheaf (cokernel φ))
    fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero T E M φ hM hφ
      ((QCoh.coe_support_annihilatorSheaf _).le h)
  obtain ⟨hsub, hK⟩ := VB.isSubbundle_kernel_of_locally_principal T' _ _ ((Scheme.Modules.pullback ρ).map φ) r
    (hE.pullback ρ) (hM.pullback ρ) (VB.exists_image_principal_of_effCartier T T' ρ E M φ _ hE hM hC)
  let S : ShortComplex T'.Modules :=
    ShortComplex.mk _ _ (cokernel.condition (kernel.ι ((Scheme.Modules.pullback ρ).map φ)))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨s, h₃⟩ := hsub.isVB_cokernel
  have h₂ : IsVB S.X₂ (r + 1) := hE.pullback ρ
  have h₃' : IsVB S.X₃ s := h₃
  have hs : s = 1 := by
    have := h₂.isFiniteQC
    have g := genRank_shortExact hS
    rw [(show IsVB S.X₁ r from hK).genRank_eq, h₂.genRank_eq, h₃'.genRank_eq] at g
    omega
  subst hs
  exact ⟨T', inferInstance, inferInstance, ρ, S, det S.X₃ 1, hT', hc, hd, hS, ⟨Iso.refl _⟩, h₃'.isLB_det,
    ⟨h₃'.isoDet⟩, hK⟩

theorem hasFlag_of_iso {X : Scheme.{0}} {E E' : X.Modules} {l : List (LB X)} (h : HasFlag E l) (φ : E ≅ E') :
    HasFlag E' l := by
  cases h with
  | nil h => exact .nil (h.of_iso φ.symm)
  | cons S hS hL e h =>
    let S' : ShortComplex X.Modules := ShortComplex.mk (S.f ≫ φ.hom) (φ.inv ≫ S.g) (by simp)
    have ψ : S ≅ S' := ShortComplex.isoMk (Iso.refl _) φ (Iso.refl _) (by simp [S']) (by simp [S'])
    exact .cons S' (ShortComplex.shortExact_of_iso ψ hS) hL e h

theorem shortExact_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {r s : ℕ} (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) : (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have := hS.epi_g
  haveI := h₁.isQuasicoherent
  haveI := GlobalTheory.FlagPull.isQuasicoherent_X₂ S hS h₃
  exact ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f hS.exact).1
    (GlobalTheory.FlagPull.mono_pullback_map_f f S hS h₃) (QCoh.exact_map_pullback f hS.exact).2

theorem exists_of_rank (k : Type) [Field k] (r : ℕ) : ∀ (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T],
    IsProjSurface k T → ∀ E : T.Modules, IsVB E r →
      ∃ (T' : Scheme.{0}) (_ : Algebra k Γ(T', ⊤)) (_ : IsIntegral T') (ρ : T' ⟶ T) (d : ℕ)
        (l : List (LB T')), IsProjSurface k T' ∧ ρ ≫ strHom k T = strHom k T' ∧ IsGenFinite ρ d ∧
          HasFlag ((Scheme.Modules.pullback ρ).obj E) l := by
  induction r with
  | zero =>
    intro T _ _ hT E hE
    exact ⟨T, inferInstance, inferInstance, 𝟙 T, 1, [], hT, Category.id_comp _, isGenFinite_id,
      .nil (isVB_zero_iff.1 (hE.pullback (𝟙 T)))⟩
  | succ r ih =>
    intro T _ _ hT E hE
    obtain ⟨T₁, _, _, ρ, S, L, hT₁, hc, hd, hS, ⟨e₂⟩, hL, ⟨e₃⟩, h₁⟩ := step k T hT E r hE
    obtain ⟨T₂, _, _, ρ', d', l, hT₂, hc', hd', hfl⟩ := ih T₁ hT₁ S.X₁ h₁
    have h₃ : IsVB S.X₃ 1 := (isVB_toMod hL).of_iso e₃.symm
    have hS' := shortExact_pullback ρ' S hS h₁ h₃
    obtain ⟨φ⟩ := nonempty_pullback_toMod_iso hL ρ'
    have H : HasFlag ((Scheme.Modules.pullback ρ').obj S.X₂) (L.pull ρ' :: l) :=
      .cons (S.map (Scheme.Modules.pullback ρ')) hS' (Semi.LB.isLB_pull hL ρ')
        ((Scheme.Modules.pullback ρ').mapIso e₃ ≪≫ φ) hfl
    refine ⟨T₂, inferInstance, inferInstance, ρ' ≫ ρ, d' * 1, L.pull ρ' :: l, hT₂, ?_,
      GlobalTheory.T.gen_finite_comp_degree_mul _ _ _ ρ' ρ d' 1 hd' hd, ?_⟩
    · rw [Category.assoc, hc, hc']
    · exact hasFlag_of_iso H ((Scheme.Modules.pullback ρ').mapIso e₂ ≪≫ (Scheme.Modules.pullbackComp ρ' ρ).app E)

theorem flagCoverExists : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T],
    IsProjSurface k T → FlagCoverExists k T :=
  fun k _ T _ _ hT E r hE => exists_of_rank k r T hT E hE

end GlobalTheory.FlagCover
