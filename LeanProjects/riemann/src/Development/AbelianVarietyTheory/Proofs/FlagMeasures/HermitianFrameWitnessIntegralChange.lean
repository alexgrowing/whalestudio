import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeFrameUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentAddIsotropicToAnisotropicStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.WitChange

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext v
  simp only [img, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨k u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

lemma prF_e (Fr : FrameD H r) (a : Fin r) : Fr.prF (Fr.f a.castSucc) = 0 := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f a.castSucc) (Fr.es c) • Fr.e c = Fr.f a.castSucc := by
    rw [Finset.sum_eq_single a]
    · rw [Fr.h_es, if_pos rfl, one_smul]; rfl
    · intro c _ hc; rw [Fr.h_es, if_neg (Ne.symm hc), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ c, H.h (Fr.f a.castSucc) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_projection_last_eq_self (Fr : FrameD H r) : Fr.prF (Fr.f (Fin.last r)) = Fr.f (Fin.last r) := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.es c) • Fr.e c = 0 :=
    Finset.sum_eq_zero (fun c _ => by rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero, zero_smul])
  have h2 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_mem (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) (b : Fin (r + 1)) :
    Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  rcases Fin.eq_castSucc_or_eq_last b with ⟨a, rfl⟩ | rfl
  · refine ⟨fun c => ?_, fun c => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [Fr.h_es]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)]; exact M.L.O.zero_mem
    · exact (prF_e Fr a).symm
    · rw [map_zero]; exact L.zero_mem
  · obtain ⟨xz, hxz, hxL, _⟩ := hL.2.2
    refine ⟨fun c => ?_, fun c => ?_, ⟨xz, ?_, hxL⟩⟩
    · rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero]; exact M.L.O.zero_mem
    · show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) ∈ _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne)]; exact M.L.O.zero_mem
    · rw [hxz]; exact (frame_projection_last_eq_self Fr).symm

end

theorem integral_change {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} (hOK : M.OK) {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : Uni A) (hAO : ∀ a b, A a b ∈ M.L.O) :
    ∃ k ∈ Fr.N, (∀ b, k (Fr.f b) = ∑ a, A a b • Fr.f a) ∧ img k (Fr.LamStd L) = Fr.LamStd L := by
  obtain ⟨kl, hkl, hkle, hklz, hklL⟩ := GlobalTheory.T.unitriangular_change_frame_unipotent M hOK H r Fr L A hA hAO
  obtain ⟨y, hyL, hyz, hyes⟩ := GlobalTheory.T.exists_inner_lattice_vector_anisotropic M hOK H r Fr L hL
  have hx : ∑ a : Fin r, A a.castSucc (Fin.last r) • Fr.f a.castSucc ∈
      Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc) :=
    Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ (⟨A a.castSucc (Fin.last r), hAO _ _⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨kz, hkz, hkzz, hkzX, hkzL⟩ := GlobalTheory.T.exists_unipotent_add_isotropic_to_anisotropic M hOK H r Fr L hL y hyL hyz hyes _ hx
  refine ⟨kz * kl, mul_mem hkz hkl, fun b => ?_, by rw [img_mul, hklL, hkzL]⟩
  induction b using Fin.lastCases with
  | last =>
    rw [LinearEquiv.mul_apply, hklz, hkzz, Fin.sum_univ_castSucc, hA.2, one_smul, add_comm]
  | cast c =>
    rw [LinearEquiv.mul_apply, hkle c]
    apply hkzX
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem witness_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hk hrel d t ht A A' g g' hA hA' hAA hg hg'
  obtain ⟨hT, hT', ⟨n, hn, hf, hLam⟩, ⟨n', hn', hf', hLam'⟩, hadm⟩ := ht
  obtain ⟨kA, hkA, hkAf, hkAL⟩ := integral_change hOK P.A d.L d.hL A hA (fun a b => (hAA a b).1)
  obtain ⟨kB, hkB, hkBf, hkBL⟩ := integral_change hOK P.B d.L' d.hL' A' hA' (fun a b => (hAA a b).2.1)
  have hfΛ : ∀ a, t.f a ∈ t.abelian₂ := by
    intro a; rw [hf, hLam]; exact ⟨P.A.f a, frame_mem P.A d.hL a, rfl⟩
  refine ⟨hT, hT', ⟨n * kA, mul_mem hn hkA, ?_, ?_⟩, ⟨n' * kB, mul_mem hn' hkB, ?_, ?_⟩, ?_⟩
  · funext b
    show g b = n (kA (P.A.f b))
    rw [hg b, hkAf b, map_sum, hf]
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkAL, hLam]
  · funext b
    show g' b = n' (kB (P.B.f b))
    rw [hg' b, hkBf b, map_sum, hf']
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkBL, hLam']
  · intro gg hgg
    obtain ⟨had, hio⟩ := hadm gg hgg
    refine ⟨fun b => ?_, hio⟩
    have hθ : theta M = (gg.q : F) := by simp [theta, hgg]
    show g' b - g b ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂
    have e1 : g' b - g b = ∑ a, (A' a b • (t.f' a - t.f a) - (A a b - A' a b) • t.f a) := by
      rw [hg b, hg' b, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [smul_sub, sub_smul]; abel
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ (⟨A' a b, (hAA a b).2.1⟩ : M.L.O) (had a)
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hAA a b).2.2
      rw [hθ] at hc
      rw [← hc]
      have h1 : algebraMap F E (gg.q : F) • t.f a ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂ :=
        Submodule.subset_span ⟨t.f a, hfΛ a, rfl⟩
      rw [smul_assoc]
      exact Submodule.smul_mem _ c h1

end GlobalTheory.LocOver.WitChange
