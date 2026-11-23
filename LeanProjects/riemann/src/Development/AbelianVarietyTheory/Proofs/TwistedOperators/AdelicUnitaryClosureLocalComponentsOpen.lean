import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceGen

open GlobalTheory.AdelicU

theorem piCoprod_mem {ι G : Type} [Fintype ι] [Monoid G] {N : ι → Type} [∀ i, Monoid (N i)] (φ : ∀ i, N i →* G)
    (h : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y)) (M : Submonoid G) (hM : ∀ i x, φ i x ∈ M)
    (x : ∀ i, N i) : MonoidHom.noncommPiCoprod φ h x ∈ M := by
  rw [MonoidHom.noncommPiCoprod_apply]
  exact Submonoid.noncommProd_mem _ _ _ _ fun i _ => hM i (x i)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem levelOff_anti {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S') :
    levelOff σ J L S' ≤ levelOff σ J L S := fun g hg => by
  rw [mem_levelOff] at hg ⊢
  refine ⟨hg.1, fun v hv => hg.2.1 v (h hv), fun v _ => ?_⟩
  by_cases hv : v ∈ S'
  · rw [hg.2.1 v hv]; exact one_mem _
  · exact hg.2.2 v hv

theorem exists_levelOff_le [Submodule.IsLattice E L] (U : Subgroup (GAd σ J)) (hU : IsOpen (U : Set (GAd σ J))) :
    ∃ S, levelOff σ J L S ≤ U := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ (U : Set (GAd σ J)))
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hU)
    (fun S => ((isCompact_levelOff σ J L S).diff hU).isClosed)
  rw [Set.mem_iInter] at hg
  have h1 : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (h1 ▸ one_mem U)

omit [NumberField E] in
theorem emb_proj_mem_levelOff {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GAd σ J} (hk : k ∈ levelOff σ J L S)
    (v : HeightOneSpectrum (𝓞 F)) : emb σ J v (proj σ J v k) ∈ levelOff σ J L S := by
  by_cases hv : v ∈ S
  · rw [(mem_levelOff.1 hk).2.1 v hv, map_one]; exact one_mem _
  · exact emb_mem_levelOff hv ((mem_levelOff.1 hk).2.2 v hv)

theorem eq_top_of_local [Submodule.IsLattice E L] (M : Submonoid (GAd σ J)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : ∀ v x, emb σ J v x ∈ M) (h2 : ∀ w x, embArch σ J w x ∈ M) (h3 : ∀ k ∈ levelOff σ J L S, k ∈ M) :
    M = ⊤ := by
  classical
  refine top_unique fun g _ => ?_
  have hinf : ∀ y, ofInf σ J y ∈ M := fun y => by
    rw [← (infEquivPi σ J).symm_apply_apply y]
    generalize infEquivPi σ J y = x
    have : embArchPi σ J x ∈ M.comap (ofInf σ J) := by
      exact piCoprod_mem (fun w => embArchInf σ J w) _ _ (fun w y => h2 w y) x
    exact this
  have hat : ∀ S' x, embAt σ J S' x ∈ M := fun S' x => by
    exact piCoprod_mem (fun v : S' => emb σ J v) _ _ (fun v y => h1 v y) x
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  set g' := ofFin σ J (projFin σ J g) with hg'
  set S' := S ∪ hf.toFinset with hS'
  have hfin : g' ∈ finPts σ J := mem_finPts.2 (by simp [hg'])
  have hx := mem_atPts.1 (embAt_mem σ J S' (projAt σ J S' g'))
  have hrest : (partAway σ J S' g' : GAd σ J) ∈ levelOff σ J L S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hx.1) hfin, mem_awayPts.1 (partAway σ J S' g').2, fun v hv => ?_⟩
    change proj σ J v ((embAt σ J S' (projAt σ J S' g'))⁻¹ * g') ∈ _
    rw [map_mul, map_inv, hx.2 v hv, inv_one, one_mul, hg', proj_ofFin, projFinLoc_projFin]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  rw [← ofInf_projInf_mul_ofFin_projFin σ J g, ← hg', ← embAt_mul_partAway σ J S' g']
  exact mul_mem (hinf _) (mul_mem (hat _ _) (h3 _ (levelOff_anti σ J L Finset.subset_union_left hrest)))

end General

theorem gen_by_local : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  intro D V U hU
  haveI hL : Submodule.IsLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  obtain ⟨S, hS⟩ := exists_levelOff_le D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) U hU
  have hG : ∀ k ∈ levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S, k ∈ U ∧ k ∈ GfC V :=
    fun k hk => ⟨hS hk, (mem_levelOff.1 hk).1⟩
  refine ⟨fun g => ?_, eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) _ S
    (fun v x => Submonoid.subset_closure (Or.inl ⟨.inl v, by simp [gAt]⟩)) (fun w x => ?_) fun k hk => ?_⟩
  · have hf := Filter.eventually_cofinite.1
      (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) g)
    haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
    refine (((hf.union S.finite_toSet).image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
    rintro (v | τ) hp
    · refine Or.inl ⟨v, ?_, rfl⟩
      by_contra hc
      rw [Set.mem_union, not_or] at hc
      exact hp (hG _ (emb_mem_levelOff hc.2 (not_not.1 hc.1)))
    · exact Or.inr ⟨τ, rfl⟩
  · obtain ⟨τ, rfl⟩ : ∃ τ, plTau D τ = w := (placeOf_bijective D).2 w
    refine Submonoid.subset_closure (Or.inl ⟨.inr τ, ?_⟩)
    simp only [gAt, projArch_embArch_self]
  · refine Submonoid.subset_closure (Or.inr ⟨(hG k hk).1, (hG k hk).2, ?_⟩)
    rintro (v | τ)
    · exact hG _ (emb_proj_mem_levelOff _ _ _ hk v)
    · have : gAt V (.inr τ) k = 1 := by
        simp only [gAt, mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 _, map_one]
      rw [this]
      exact ⟨one_mem _, one_mem _⟩

end GlobalTheory.PlaceGen

end
