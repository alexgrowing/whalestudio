import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem exists_core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K M : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hMo : IsOpen (M : Set G)) (hMK : M ≤ K) :
    ∃ C : Subgroup G, IsOpen (C : Set G) ∧ C ≤ M ∧ ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set M' : Subgroup K := M.subgroupOf K with hM'
  have hM'o : IsOpen (M' : Set K) := hMo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ M') := Subgroup.quotient_finite_of_isOpen M' hM'o
  haveI : M'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcl : IsClosed (M'.normalCore : Set K) := by
    have hc : IsClosed (M' : Set K) := Subgroup.isClosed_of_isOpen M' hM'o
    have : (M'.normalCore : Set K) = ⋂ b : K, (fun a : K => b * a * b⁻¹) ⁻¹' (M' : Set K) := by
      ext a
      simp [Subgroup.normalCore, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun b => hc.preimage (by fun_prop)
  have hop : IsOpen (M'.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨M'.normalCore.map K.subtype, ?_, ?_, ?_⟩
  · have : ((M'.normalCore.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (M'.normalCore : Set K) := by
      ext x; simp
    rw [this]
    exact hKo.isOpenMap_subtype_val _ hop
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ M' := Subgroup.normalCore_le M' ha
    exact h1
  · rintro k hk _ ⟨a, ha, rfl⟩
    refine ⟨⟨k, hk⟩ * a * (⟨k, hk⟩ : K)⁻¹, ?_, by simp⟩
    exact (Subgroup.normalCore_normal M').conj_mem a ha _

private theorem hecke_slice {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (K' : Subgroup (GLw n w × GLw 0 w)) (f : GLw n w × GLw 0 w → ℂ) (hf : IsHecke K' f)
    (N : Subgroup (GLw n w)) (hN : ∀ k ∈ N, ((k, 1) : GLw n w × GLw 0 w) ∈ K') :
    IsHecke N (fun g => f (g, 1)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · haveI : Unique (GLw 0 w) := Unique.mk' _
    have e : (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) =
        ⇑(Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm := by
      funext g
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have h : Topology.IsClosedEmbedding (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) := by
      rw [e]
      exact (Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm.isClosedEmbedding
    exact hf.1.comp_isClosedEmbedding h
  · have h := hf.2 _ (hN k hk) (x, 1)
    simpa using h

theorem lcLevel_pf : LcLevel := by
  classical
  intro E _ _ _ n Z N₀ hN₀ φ₁ φ₂ hφ
  have hK := fun w : Pl E => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have key : ∀ w ∈ Z, ∃ C : Subgroup (GLw n w), IsOpen (C : Set (GLw n w)) ∧ C ≤ N₀ w ∧
      (∀ k ∈ KGL w n, ∀ x ∈ C, k * x * k⁻¹ ∈ C) ∧ ∀ b, IsHecke C (two φ₁ φ₂ w b) := by
    intro w hw
    obtain ⟨⟨A, hAo, -, hA⟩, ⟨B, hBo, -, hB⟩⟩ := hφ w hw
    let ι : GLw n w →* GLw n w × GLw 0 w := MonoidHom.inl _ _
    have hι : Continuous ι := continuous_id.prodMk continuous_const
    have hMo : IsOpen ((N₀ w ⊓ A.comap ι ⊓ B.comap ι : Subgroup (GLw n w)) : Set (GLw n w)) :=
      ((hN₀ w).1.inter (hAo.preimage hι)).inter (hBo.preimage hι)
    obtain ⟨C, hCo, hCM, hCn⟩ := exists_core (KGL w n) (N₀ w ⊓ A.comap ι ⊓ B.comap ι) (hK w).1 (hK w).2
      hMo (fun x hx => (hN₀ w).2.1 hx.1.1)
    refine ⟨C, hCo, fun x hx => (hCM hx).1.1, hCn, ?_⟩
    rintro (_ | _)
    · exact hecke_slice w A (φ₁ w) hA C fun k hk => (hCM hk).1.2
    · exact hecke_slice w B (φ₂ w) hB C fun k hk => (hCM hk).2
  choose! C hC using key
  refine ⟨fun w => if w ∈ Z then C w else N₀ w, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      obtain ⟨a, b, c, -⟩ := hC w hw
      exact ⟨a, b.trans (hN₀ w).2.1, c, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact hN₀ w
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact (hC w hw).2.1
    · simp only [if_neg hw]
      exact le_rfl
  · intro w hw b
    simp only [if_pos hw]
    exact (hC w hw).2.2.2 b

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
