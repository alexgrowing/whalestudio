import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMultTransport

section Density

open GlobalTheory.AdelicU GlobalTheory.PlaceGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_levelOff_subset [Submodule.IsLattice E L] (N : Set (GAd σ J)) (hN : IsOpen N)
    (h1 : (1 : GAd σ J) ∈ N) : ∃ S, (levelOff σ J L S : Set (GAd σ J)) ⊆ N := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ N)
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hN)
    (fun S => ((isCompact_levelOff σ J L S).diff hN).isClosed)
  rw [Set.mem_iInter] at hg
  have e : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (e ▸ h1)

end Density

theorem dense_locFin (D : D7) (V : HSp D) :
    Dense ((⨆ v, (locFin V v).range : Subgroup (GfC V)) : Set (GfC V)) := by
  classical
  haveI hL : Submodule.IsLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  set H : Subgroup (GfC V) := ⨆ v, (locFin V v).range with hH
  have hemb : ∀ v x, GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x ∈ H.map (GfC V).subtype := fun v x =>
    ⟨locFin V v x, Subgroup.mem_iSup_of_mem v ⟨x, rfl⟩, rfl⟩
  intro g
  rw [mem_closure_iff]
  intro o ho hgo
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 ho
  let N : Set (GA D V) := (fun k => (g : GA D V) * k⁻¹) ⁻¹' U
  have hN : IsOpen N := hU.preimage (continuous_const.mul continuous_inv)
  have h1 : (1 : GA D V) ∈ N := by simpa [N] using hgo
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.TrMultTransport.exists_levelOff_subset D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) N hN h1
  have hf := Filter.eventually_cofinite.1
    (GlobalTheory.AdelicU.eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) (g : GA D V))
  set S' := S₀ ∪ hf.toFinset with hS'
  set x := embAt D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)) with hx
  have hxm := GlobalTheory.AdelicU.mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)))
  have hgfin : (g : GA D V) ∈ GlobalTheory.AdelicU.finPts D.sp.cm.sig V.gram := g.2
  have hrest : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈
      levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hxm.1) hgfin, mem_awayPts.1 (partAway _ _ S' (g : GA D V)).2, fun v hv => ?_⟩
    change proj D.sp.cm.sig V.gram v ((embAt _ _ S' (projAt _ _ S' (g : GA D V)))⁻¹ * (g : GA D V)) ∈ _
    rw [map_mul, map_inv, hxm.2 v hv, inv_one, one_mul]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  have hp : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈ N :=
    hS₀ (GlobalTheory.PlaceGen.levelOff_anti _ _ _ Finset.subset_union_left hrest)
  have hxe : (g : GA D V) * (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V)⁻¹ = x := by
    exact mul_inv_eq_of_eq_mul (embAt_mul_partAway D.sp.cm.sig V.gram S' (g : GA D V)).symm
  have hxH : x ∈ H.map (GfC V).subtype :=
    GlobalTheory.PlaceGen.piCoprod_mem (fun v : S' => GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) _ _ (fun v y => hemb v y) _
  obtain ⟨y, hy, hye⟩ := hxH
  refine ⟨y, ?_, hy⟩
  show (y : GA D V) ∈ U
  have : (y : GA D V) = x := hye
  rw [this, ← hxe]
  exact hp

theorem finLoc_transport {D : D7} {V V' : HSp D}
    (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v) (Φ : GfC V ≃ₜ* GfC V')
    (hΦ : ∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    finLoc V' v (Φ g) = j v (finLoc V v g) := by
  let f₁ : GfC V →* Gv V' v := (finLoc V' v).comp Φ.toMulEquiv.toMonoidHom
  let f₂ : GfC V →* Gv V' v := (j v).toMulEquiv.toMonoidHom.comp (finLoc V v)
  have hc : ∀ {W : HSp D}, Continuous (finLoc W v) := fun {W} =>
    (continuous_proj D.sp.cm.sig W.gram v).comp continuous_subtype_val
  have c₁ : Continuous f₁ := hc.comp Φ.continuous
  have c₂ : Continuous f₂ := (j v).continuous.comp hc
  have hle : (⨆ u, (locFin V u).range) ≤ MonoidHom.eqLocus f₁ f₂ := iSup_le fun u => by
    rintro _ ⟨x, rfl⟩
    show finLoc V' v (Φ (locFin V u x)) = j v (finLoc V v (locFin V u x))
    rw [hΦ]
    by_cases h : v = u
    · subst h
      simp [finLoc]
    · simp [finLoc, proj_emb_ne _ _ h]
  have := Set.EqOn.closure (s := ((⨆ u, (locFin V u).range : Subgroup (GfC V)) : Set (GfC V)))
    (fun x hx => hle hx) c₁ c₂
  rw [(dense_locFin D V).closure_eq] at this
  exact this (Set.mem_univ g)

theorem transport :
    ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v),
      (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V',
      (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) →
      (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧
      ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  intro D V V' j hK Φ hΦ
  have h1 : ∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g := fun ff g => by
    refine finprod_congr fun v => ?_
    have := finLoc_transport j Φ hΦ v g
    simp only [finLoc, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
    simp only [GlobalTheory.Orb.transfer, Function.comp_apply, this, ContinuousMulEquiv.symm_apply_apply]
  refine ⟨h1, fun μf ν hν => ?_⟩
  haveI := hν.1
  refine ⟨Φ.isHaarMeasure_map ν, fun ff' hff' => ?_⟩
  let ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ := fun v => ff' v ∘ j v
  have ht : GlobalTheory.Orb.transfer j ff = ff' := funext fun v => funext fun y => by
    simp [ff, GlobalTheory.Orb.transfer]
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := by
    have := hff'.transfer (fun v => (j v).symm) (Filter.Eventually.of_forall fun v g => by
      have := hK v ((j v).symm g)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this.symm)
    convert this using 1
    funext v y
    simp [ff, GlobalTheory.Orb.transfer]
  have hm : MeasurableEmbedding (⇑Φ) := Φ.toHomeomorph.measurableEmbedding
  rw [hm.integral_map]
  have e1 : ∀ g, finFn V' ff' (Φ g) = finFn V ff g := fun g => by
    rw [← h1 ff g, ht]
  simp only [e1, hν.2 ff hff]
  refine finprod_congr fun v => ?_
  have hjm : MeasurableEmbedding (⇑(j v)) := (j v).toHomeomorph.measurableEmbedding
  show _ = ∫ x, ff' v x ∂(μf v).map (j v)
  rw [hjm.integral_map]
  rfl
