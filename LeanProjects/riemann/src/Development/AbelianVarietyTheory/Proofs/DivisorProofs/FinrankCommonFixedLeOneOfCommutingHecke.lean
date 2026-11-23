import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

open Module

namespace GlobalTheory.CommutingHecke

theorem fixed_mem_of_stable {ι : Type} [Finite ι] {H : ι → Type} [∀ c, Monoid (H c)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (E : Submodule ℂ V) (hE : E ≠ ⊥) (hst : ∀ c g, ∀ v ∈ E, e c (a c g v) ∈ E)
    (v : V) (hv : ∀ c, e c v = v) : v ∈ E := by
  classical
  haveI := Fintype.ofFinite ι
  let Y : Finset ι → Submodule ℂ V := fun s =>
    sInf {Y | E ≤ Y ∧ ∀ c ∈ s, ∀ g, ∀ v ∈ Y, a c g v ∈ Y}
  have hEY : ∀ s, E ≤ Y s := fun s => le_sInf fun _ h => h.1
  have hYst : ∀ s, ∀ c ∈ s, ∀ g, ∀ v ∈ Y s, a c g v ∈ Y s := by
    intro s c hc g v hv
    simp only [Y, Submodule.mem_sInf] at hv ⊢
    exact fun p hp => hp.2 c hc g v (hv p hp)
  have hind : ∀ s, v ∈ Y s → v ∈ E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      have : Y ∅ ≤ E := sInf_le ⟨le_rfl, by simp⟩
      exact this h
    | insert c s hc ih =>
      intro h
      apply ih
      let Z : Submodule ℂ V := ⨅ g, (Y s).comap (e c * a c g)
      have hZ : ∀ w, w ∈ Z ↔ ∀ g, e c (a c g w) ∈ Y s := by
        intro w
        simp [Z, Submodule.mem_iInf]
      have hle : Y (insert c s) ≤ Z := by
        refine sInf_le ⟨fun w hw => (hZ w).2 fun g => hEY s (hst c g w hw), ?_⟩
        intro c' hc' g w hw
        rw [hZ] at hw ⊢
        intro g'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · have := hw (g' * g)
          rwa [map_mul, Module.End.mul_apply] at this
        · have hne : c ≠ c' := fun h => hc (h ▸ hc')
          have h1 : a c g' (a c' g w) = a c' g (a c g' w) :=
            LinearMap.congr_fun (haa c c' hne g' g).eq w
          have h2 : e c (a c' g (a c g' w)) = a c' g (e c (a c g' w)) :=
            LinearMap.congr_fun (hea c c' hne g).eq _
          rw [h1, h2]
          exact hYst s c' hc' g _ (hw g')
      have := (hZ v).1 (hle h) 1
      rwa [map_one, Module.End.one_apply, hv] at this
  apply hind Finset.univ
  rcases hirr (Y Finset.univ) (fun c => hYst _ c (Finset.mem_univ c)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hEY _)) hE
  · rw [h]; trivial

theorem finrank_fixed_le_one (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hee : ∀ c, e c * e c = e c)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (hec : ∀ c c', c ≠ c' → Commute (e c) (e c'))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hhk : ∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c)
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (W : Submodule ℂ V) (hW : ∀ v ∈ W, ∀ c, e c v = v) : finrank ℂ W ≤ 1 := by
  classical
  let W0 : Submodule ℂ V := ⨅ c, LinearMap.eqLocus (e c) LinearMap.id
  have hW0 : ∀ v, v ∈ W0 ↔ ∀ c, e c v = v := by
    intro v
    simp [W0, Submodule.mem_iInf]
  have hpres : ∀ c g, ∀ v ∈ W0, e c (a c g v) ∈ W0 := by
    intro c g v hv
    rw [hW0] at hv ⊢
    intro c'
    by_cases h : c' = c
    · subst h
      exact LinearMap.congr_fun (hee c') _
    · have h1 : e c' (e c (a c g v)) = e c (e c' (a c g v)) :=
        LinearMap.congr_fun (hec c' c h).eq _
      have h2 : e c' (a c g v) = a c g (e c' v) := LinearMap.congr_fun (hea c' c h g).eq _
      rw [h1, h2, hv]
  have hcomm : ∀ c g c' h, ∀ v ∈ W0,
      e c (a c g (e c' (a c' h v))) = e c' (a c' h (e c (a c g v))) := by
    intro c g c' h v hv
    rw [hW0] at hv
    by_cases hc : c = c'
    · subst hc
      have := LinearMap.congr_fun (hhk c g h) v
      simpa only [Module.End.mul_apply, hv] using this
    · have : Commute (e c * a c g) (e c' * a c' h) :=
        Commute.mul_left ((hec c c' hc).mul_right (hea c c' hc h))
          ((hea c' c (Ne.symm hc) g).symm.mul_right (haa c c' hc g h))
      exact LinearMap.congr_fun this.eq v
  have hWle : W ≤ W0 := fun v hv => (hW0 v).2 (hW v hv)
  refine le_trans (Submodule.finrank_mono hWle) ?_
  by_cases hbot : W0 = ⊥
  · rw [hbot]; simp
  haveI : Nontrivial W0 := Submodule.nontrivial_iff_ne_bot.2 hbot
  have hscal : ∀ c g, ∃ μ : ℂ, ∀ v ∈ W0, e c (a c g v) = μ • v := by
    intro c g
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
      ((e c * a c g).restrict (p := W0) (q := W0) (hpres c g))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : e c (a c g w) = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨μ, fun v hv => ?_⟩
    have := fixed_mem_of_stable a e hea haa hirr (W0 ⊓ Module.End.eigenspace (e c * a c g) μ)
      ?_ ?_ v ((hW0 v).1 hv)
    · exact Module.End.mem_eigenspace_iff.1 this.2
    · rw [Submodule.ne_bot_iff]
      exact ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩
    · intro c' h u hu
      refine ⟨hpres c' h u hu.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hu2 : e c (a c g u) = μ • u := Module.End.mem_eigenspace_iff.1 hu.2
      rw [Module.End.mul_apply, hcomm c g c' h u hu.1, hu2, map_smul, map_smul]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hle : W0 ≤ ℂ ∙ w := by
    intro v hv
    refine fixed_mem_of_stable a e hea haa hirr (ℂ ∙ w) (by simpa using hw0) ?_ v ((hW0 v).1 hv)
    intro c g u hu
    obtain ⟨μ, hμ⟩ := hscal c g
    rw [hμ u ((Submodule.span_singleton_le_iff_mem _ _).2 hw hu)]
    exact Submodule.smul_mem _ _ hu
  exact le_trans (Submodule.finrank_mono hle) (finrank_span_singleton hw0).le

end GlobalTheory.CommutingHecke
