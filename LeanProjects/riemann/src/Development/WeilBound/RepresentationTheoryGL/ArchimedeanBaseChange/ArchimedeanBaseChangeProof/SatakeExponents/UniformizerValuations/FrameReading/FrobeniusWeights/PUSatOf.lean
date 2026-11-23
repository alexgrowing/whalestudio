import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinusculeSetEqDoubleCoset
import GroundTheory.AutomorphicForms.Satake

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcs_of_finDoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {f : G → ℂ} (hf : FinDosetSupp K f) : HasCompactSupport f := by
  obtain ⟨S, hS⟩ := hf
  refine HasCompactSupport.intro (K := ⋃ s ∈ S, (fun p : G × G => p.1 * s * p.2) '' ((K : Set G) ×ˢ (K : Set G)))
    (S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)) fun g hg => ?_
  by_contra h0
  obtain ⟨s, hs, a, b, rfl⟩ := hS g h0
  exact hg (Set.mem_biUnion hs ⟨((a : G), (b : G)), ⟨a.2, b.2⟩, rfl⟩)

theorem uSatOf_holds : USatOf := by
  intro hSD E _ _ _ n π w σ hw hcomp hfix
  obtain ⟨P, T, hT, hP, hlev⟩ := hSD E n w hw σ
  have hUL : UL n w = ⊤ := if_pos hw
  have hmemUL : ∀ g : GLw n w, g ∈ UL n w := fun g => hUL ▸ Subgroup.mem_top g
  have hKmap : (KL n w).map (UL n w).subtype = KGL w n := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
    · intro hg
      exact ⟨⟨g, hmemUL g⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hoc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hKLopen : IsOpen (KL n w : Set (UL n w)) := by
    have : (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (KGL w n : Set (GLw n w)) := by
      ext x
      exact Subgroup.mem_subgroupOf
    rw [this]
    exact hoc.1.preimage continuous_subtype_val
  have hLev : IsLevel (MonoidHom.id _) (KL n w) (KL n w) := ⟨hKLopen, le_rfl, fun k hk => hk⟩
  have hHk : ∀ ϖ : w.adicCompletion E, IsUnifV E w ϖ → ∀ k : ℕ,
      PositivityTheory.Rg.BcN.F2.IsHk ((KL n w).map (UL n w).subtype) (Tj ℂ n (Ov E w) ϖ k) := by
    intro ϖ hϖ k
    have hT' := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ k
    rw [hKmap]
    exact ⟨hoc.1, hoc.2, hcs_of_finDoset hoc.2 hT'.2, fun k₁ hk₁ k₂ hk₂ g => hT'.1 ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ g⟩
  obtain ⟨ϖ₀, hϖ₀⟩ := GlobalTheory.LFun.exists_isUnifV w

  have hTfix : ∀ y ∈ fixed σ.ρ (KL n w), T y ∈ fixed P.ρ (KGL w n) := fun y hy => by
    have := ((hlev (KL n w) hLev _ (hHk ϖ₀ hϖ₀ 0)).2 y hy).1
    rwa [hKmap] at this
  obtain ⟨y₀, hy₀, hy₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hsph : GlobalTheory.LGrp.IsSpherical P.ρ (KGL w n) := by
    intro h
    have h1 := hTfix y₀ hy₀
    rw [h, Submodule.mem_bot] at h1
    exact hy₀0 (T.injective (h1.trans T.map_zero.symm))
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible P.smooth P.irred hsph
  refine ⟨B, ⟨P, hP π hcomp, hB⟩, ?_⟩
  intro ϖ hϖ k hk

  have hff : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (H : Subgroup (GLw n w)),
      fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := fun ρ H => by
    ext v
    simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]
  have e1 := GlobalTheory.CompanionTheory.SatakeTyping.integralGL_eq_KGL w n
  have hP1 : Module.finrank ℂ (fixed P.ρ (KGL w n)) = 1 := by
    have := P.irred
    have hne : GroundTheory.Automorphic.fixedVectors P.ρ (GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ := by
      rw [e1, ← hff]
      exact hsph
    have h := GroundTheory.Automorphic.Spherical.finrank_fixedVectors_eq_one (fun v => P.smooth v) hne
    rwa [e1, ← hff] at h
  have : FiniteDimensional ℂ (fixed P.ρ (KGL w n)) := Module.finite_of_finrank_pos (by omega)

  let Tf : fixed σ.ρ (KL n w) →ₗ[ℂ] fixed P.ρ (KGL w n) :=
    { toFun := fun y => ⟨T y, hTfix y.1 y.2⟩
      map_add' := fun a b => Subtype.ext (T.map_add a b)
      map_smul' := fun c a => Subtype.ext (T.map_smul c a) }
  have hTf : Function.Injective Tf := fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h))
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.Finite.of_injective Tf hTf
  have hσ1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hTf
    have h2 : 0 < Module.finrank ℂ (fixed σ.ρ (KL n w)) := Module.finrank_pos_iff.2
      ⟨⟨⟨y₀, hy₀⟩, 0, fun h => hy₀0 (congrArg Subtype.val h)⟩⟩
    omega

  set c := satEig (qV E w) n B k
  have heig : ∀ y ∈ fixed σ.ρ (KL n w),
      levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id y = c • y := by
    intro y hy
    obtain ⟨-, hall⟩ := hlev (KL n w) hLev _ (hHk ϖ hϖ k)
    obtain ⟨-, h2⟩ := hall y hy
    simp only [Subgroup.relIndex_self, Nat.cast_one, one_mul] at h2
    apply T.injective
    rw [h2, T.map_smul]
    by_cases hy0 : y = 0
    · subst hy0
      simp only [T.map_zero, smul_zero]
      simp [PositivityTheory.Rg.BcN.F2.hk]
    · have hs := hB.2 (T y) (hTfix y hy) (fun h => hy0 (T.injective (h.trans T.map_zero.symm)))
      have := hs.2.2.2 ϖ hϖ k hk
      rw [← hKmap] at this
      exact this
  have hcond : ∀ v ∈ fixed σ.ρ (KL n w),
      levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id v ∈ fixed σ.ρ (KL n w) :=
    fun v hv => by rw [heig v hv]; exact Submodule.smul_mem _ _ hv
  rw [twTr, dif_pos hcond]
  have hres : (levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id).restrict hcond =
      c • (1 : Module.End ℂ (fixed σ.ρ (KL n w))) := by
    ext v
    simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
    exact heig v.1 v.2
  rw [hres, map_smul, LinearMap.trace_one, hσ1]
  simp

end PositivityTheory.Rg.BcB.F.FG

end
