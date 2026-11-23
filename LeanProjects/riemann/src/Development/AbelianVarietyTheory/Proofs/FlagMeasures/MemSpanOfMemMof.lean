import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PrimTerm

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  unfold Frames.spanTo
  congr 1
  ext x
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem left_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) : g b ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inl ⟨b, rfl⟩)

theorem diff_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) :
    algebraMap F E S.th⁻¹ • (g' b - g b) ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem th_smul (h0 : S.th ≠ 0) (v : S.V) :
    algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
  rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]

theorem Mof_le_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g ≤ S.Mof g g' := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · have h1 := (S.Mof g g').smul_mem ⟨_, hO⟩ (diff_mem S g g' b)
    have h2 : (⟨_, hO⟩ : L.O) • algebraMap F E S.th⁻¹ • (g' b - g b) = g' b - g b :=
      th_smul S h0 _
    rw [h2] at h1
    have h3 := (S.Mof g g').add_mem h1 (left_mem S g g' b)
    rwa [sub_add_cancel] at h3
  · have h1 := (S.Mof g g').neg_mem (diff_mem S g g' b)
    rw [← smul_neg, neg_sub] at h1
    exact h1

theorem Mof_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g = S.Mof g g' :=
  le_antisymm (Mof_le_swap S h0 hO g g') (Mof_le_swap S h0 hO g' g)

theorem mem_span_of_mem_Mof (P P' : Submodule E S.V) (hd : Disjoint P P')
    (g g' : Fin (r + 1) → S.V) (hg : ∀ b, g b ∈ P) (hg' : ∀ b, g' b ∈ P')
    (hi : LinearIndependent E g') (x : S.V) (hx : x ∈ S.Mof g g') (hP : x ∈ P) :
    x ∈ Submodule.span L.O (Set.range g) := by
  unfold Frames.Mof at hx
  rw [Submodule.span_union] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hz
  have hyP : y ∈ P := by
    have : Submodule.span L.O (Set.range g) ≤ P.restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact hg b
    exact this hy
  set e : Fin (r + 1) → E := fun b => (c b : E) * algebraMap F E S.th⁻¹ with he
  have hs : ∑ b, c b • algebraMap F E S.th⁻¹ • (g' b - g b) = ∑ b, e b • g' b - ∑ b, e b • g b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_sub, he, mul_smul]
    rfl
  rw [hs] at hP ⊢
  have h1 : ∑ b, e b • g b ∈ P := P.sum_mem fun b _ => P.smul_mem _ (hg b)
  have h2 : ∑ b, e b • g' b ∈ P' := P'.sum_mem fun b _ => P'.smul_mem _ (hg' b)
  have h3 : ∑ b, e b • g' b ∈ P := by
    have := P.add_mem (P.sub_mem hP hyP) h1
    rwa [add_sub_cancel_left, sub_add_cancel] at this
  have h4 : ∑ b, e b • g' b = 0 := (Submodule.disjoint_def.1 hd) _ h3 h2
  have h5 : ∀ b, e b = 0 := Fintype.linearIndependent_iff.1 hi e h4
  simpa [h5] using hy

theorem trace_iff (Λ : Submodule L.O S.V) (f f' g g' : Fin (r + 1) → S.V)
    (hd : Disjoint (Submodule.span E (Set.range f)) (Submodule.span E (Set.range f')))
    (hg : ∀ b, g b ∈ Submodule.span E (Set.range f))
    (hg' : ∀ b, g' b ∈ Submodule.span E (Set.range f'))
    (hi : LinearIndependent E g') (hME : S.spanTo f (r + 1) ≤ S.ME) (hs : S.sat Λ = S.Mof g g')
    (x : S.V) : (x ∈ Λ ∧ x ∈ S.spanTo f (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => g b) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : x ∈ S.sat Λ := ⟨h1, hME h2⟩
    rw [hs] at h3
    rw [spanTo_top] at h2
    exact mem_span_of_mem_Mof S _ _ hd g g' hg hg' hi x h3 h2
  · intro hx
    have : Submodule.span L.O (Set.range fun b => g b) ≤
        Λ ⊓ (S.spanTo f (r + 1)).restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have h1 : g b ∈ S.sat Λ := hs ▸ left_mem S g g' b
      refine ⟨h1.1, ?_⟩
      change g b ∈ S.spanTo f (r + 1)
      rw [spanTo_top]
      exact hg b
    exact this hx

end

theorem term_of_primitive : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ, IsSD L S.Hm Λ → ∀ C, S.IsCls C → ∀ p ∈ C, S.sat Λ = S.Mof p.1 p.2 → ∃ d, S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.BBzero d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ C hC p hp hs
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hs
  obtain ⟨hli, -, -, -, -, h0, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hon, hon', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hO : algebraMap F E S.th ∈ L.O :=
    (L.O_def _).2 (isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨S.th, hth⟩))
  obtain ⟨hf, hf', hd⟩ := linearIndependent_sum.1 hli
  have hf1 : LinearIndependent E S.f := hf
  have hf2 : LinearIndependent E S.f' := hf'
  have hd1 : Disjoint (Submodule.span E (Set.range S.f)) (Submodule.span E (Set.range S.f')) := hd
  have hi : LinearIndependent E fun b => n (S.f b) :=
    hf1.map' (n : S.V →ₗ[E] S.V) n.ker
  have hi' : LinearIndependent E fun b => n' (S.f' b) :=
    hf2.map' (n' : S.V →ₗ[E] S.V) n'.ker
  have hg : ∀ b, n (S.f b) ∈ Submodule.span E (Set.range S.f) := by
    obtain ⟨s, -, h⟩ := hon n hn
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg' : ∀ b, n' (S.f' b) ∈ Submodule.span E (Set.range S.f') := by
    obtain ⟨s, -, h⟩ := hon' n' hn'
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA, m, hm, hme, hΛA⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) Λ hΛ n hn
    (trace_iff S Λ S.f S.f' _ _ hd1 hg hg' hi' le_sup_left hs)
  obtain ⟨A', hA', m', hm', hme', hΛA'⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) Λ hΛ n' hn'
    (trace_iff S Λ S.f' S.f _ _ hd1.symm hg' hg hi le_sup_right (hs.trans (Mof_swap S h0 hO _ _)))
  have hW : S.IsTermW (A, A', S.graphOf Λ) Λ m m' := by
    refine ⟨hA, hA', hm, hm', hΛA, hΛA', fun b => ?_, rfl⟩
    rw [hme, hme']
    have h1 := diff_mem S (fun b => n (S.f b)) (fun b => n' (S.f' b)) b
    rw [← hs] at h1
    exact ⟨_, h1.1, (th_smul S h0 _).symm⟩
  obtain ⟨-, hM, hFr, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S _ _ _ _ hW
  simp only [hme, hme'] at hM hFr
  exact ⟨_, ⟨(m, m'), hW⟩, hFr, hM.trans hs.symm⟩

end GlobalTheory.HL.PrimTerm
