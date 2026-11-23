import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct Topology

noncomputable section
namespace GlobalTheory.KPartLocConst

theorem locOp_kpart : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      IsLocallyConstant (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ) ∧
        (Set.range fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ).Finite := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT K hK φ hφ
  have hP : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a a']; exact GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F B.v₁) := (UAtSub σ G.W (evFin F B.v₁)).one_mem
  have hex : ∀ x : UA σ G.V'.J × UA σ G.W.J, x.1 ∈ UAt σ G.V' (evFin F B.v₁) → x.2 ∈ UAt σ G.W (evFin F B.v₁) →
      ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∃ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' x) ψ ψ₁ :=
    fun x hx1 hx2 ψ hψ => GlobalTheory.ThK.LocalOps.acts_exists hP B.v₁ x hx1 hx2 ψ hψ
  obtain ⟨U, hU, hUact⟩ := GlobalTheory.T.weilRep_smooth_at_finitePlace B G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP B.v₁ hex φ hφ

  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V' :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V' g).symm
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    have hX := hT.geo.hV'
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B a' G.V' _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V' (GlobalTheory.T.isClosed_adelic_lattice_closure F E a' G.V' hX.lat)) hsub
  haveI : CompactSpace (KAt K (evFin F B.v₁)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  have hlc : IsLocallyConstant (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k₀
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hc : Continuous fun k : KAt K (evFin F B.v₁) => ((k₀⁻¹ * k : KAt K (evFin F B.v₁)).1, (1 : UA σ G.W.J)) :=
      (continuous_subtype_val.comp (continuous_const.mul continuous_id)).prodMk continuous_const
    have h0 : ((k₀⁻¹ * k₀ : KAt K (evFin F B.v₁)).1, (1 : UA σ G.W.J)) = 1 := by
      rw [inv_mul_cancel]; rfl
    have hev : ∀ᶠ k in 𝓝 k₀, ((k₀⁻¹ * k : KAt K (evFin F B.v₁)).1, (1 : UA σ G.W.J)) ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    filter_upwards [hev] with k hk
    set h : KAt K (evFin F B.v₁) := k₀⁻¹ * k with hh
    have hh1 : h.1 ∈ UAt σ G.V' (evFin F B.v₁) := (mem_KAt.1 h.2).2
    have hk01 : k₀.1 ∈ UAt σ G.V' (evFin F B.v₁) := (mem_KAt.1 k₀.2).2
    have hfix : Acts (evFin F B.v₁) (om' (h.1, 1)) φ φ := hUact _ hk hh1 h1W
    obtain ⟨φ₁, hφ₁, ha₁⟩ := hex (k₀.1, 1) hk01 h1W φ hφ
    have hkeep : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' (h.1, 1) Φ ∈ schA F _ := fun Φ hΦ => hW.pres _ Φ hΦ
    have hprod : Acts (evFin F B.v₁) (om' (k₀.1, 1) * om' (h.1, 1)) φ φ₁ :=
      GlobalTheory.ThK.LocalOps.acts_mul B.v₁ hkeep hfix ha₁
    have ek : (k.1, (1 : UA σ G.W.J)) = (k₀.1, 1) * (h.1, 1) := by
      rw [Prod.mk_mul_mk, mul_one, hh]
      congr 1
      show k.1 = k₀.1 * (k₀⁻¹ * k).1
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [← map_mul, ← ek] at hprod
    rw [locOp_eq hφ hφ₁ hprod, locOp_eq hφ hφ₁ ha₁]
  exact ⟨hlc, hlc.range_finite⟩

end GlobalTheory.KPartLocConst
