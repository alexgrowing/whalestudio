import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolumeStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace PositivityTheory.RgUd.CellB

set_option maxHeartbeats 2000000 in

theorem openJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ →
    ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), Function.Surjective J ∧
      (∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔
        (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N)) ∧
      (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ),
        (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧
      (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d),
        pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 →
        ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧
      ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
        (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
        0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
          (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
            f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
          (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  obtain ⟨J, vol, hU, hL, hV⟩ := GlobalTheory.T.open_cell_jacquet_integral_volume k ψ hψ h N d hd ρ hρ
  obtain ⟨hfac, -⟩ := GlobalTheory.T.unipotent_radical_decomposition_normal k h N d hd
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.open_cell_levi_unipotent_conjugation k ψ h N d hd
  obtain ⟨-, huniq, -⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hUB : unipU k d hd ≤ unipB k (Fin N) := inf_le_left
  have hLB : unipL k d hd ≤ unipB k (Fin N) := inf_le_left
  have surj : Function.Surjective J := by
    intro v
    obtain ⟨L₀, hL₀U, hc, hO, hθ, f, hf, h1, h2⟩ := GlobalTheory.T.exists_bump_section_on_compact_unipotent k ψ hψ h N d hd ρ hρ v
    obtain ⟨hpos, hJ⟩ := hV L₀ hL₀U hc hO
    have e := hJ ⟨f, hf⟩ v (fun u hb hu => by
      show f.1.1 (pm k (wOpen d hd) * u) = _
      rw [h1 u hu, hθ u hb hu]
      simp) h2
    refine ⟨((vol L₀ : ℂ))⁻¹ • ⟨f, hf⟩, ?_⟩
    have hne : (vol L₀ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have gen : ∀ (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (g : openFns d hd ρ),
      ∃ hx : parInd (stdBlocks d hd) ρ n g.1 - ((whitChar ψ N ⟨n, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ,
        J ⟨_, hx⟩ ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro n hn g
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac n hn
    have hub := hUB hu
    have hab := hLB ha
    obtain ⟨m, hm, hθm⟩ := hl1 a ha hab
    let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ u g.1, OpenCoinv.translate_mem d hd ρ hub g.2⟩
    let g2 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g1.1, OpenCoinv.translate_mem d hd ρ hab g1.2⟩
    have e1 : J g1 = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • J g := hU u hu hub g g1 rfl
    have e2 : J g2 = ρ m.1 (J g1) := hL a ha m hm g1 g2 rfl
    have e3 : parInd (stdBlocks d hd) ρ (a * u) g.1 = g2.1 := by
      rw [map_mul]
      rfl
    have hθ : whitChar ψ N ⟨a * u, hn⟩ = whitChar ψ N ⟨a, hab⟩ * whitChar ψ N ⟨u, hub⟩ := by
      rw [← map_mul]
      rfl
    have hx : parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ :=
      sub_mem (OpenCoinv.translate_mem d hd ρ hn g.2) (Submodule.smul_mem _ _ g.2)
    refine ⟨hx, ?_⟩
    have e4 : (⟨_, hx⟩ : openFns d hd ρ) = g2 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g :=
      Subtype.ext (by
        show parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 =
          g2.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1
        rw [e3])
    rw [e4, map_sub, map_smul, e2, e1, map_smul, hθ, hθm, Units.val_mul]
    have e5 : ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • ρ m.1 (J g) -
        (((whitM d ψ m : ℂˣ) : ℂ) * ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ)) • J g =
        ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • (ρ m.1 (J g) - ((whitM d ψ m : ℂˣ) : ℂ) • J g) := by
      rw [smul_sub, smul_smul, mul_comm]
    rw [e5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, J g, rfl⟩)
  have bwd : ∀ f : openFns d hd ρ, f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) →
      J f ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro f hf
    have hs := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ (unipB k (Fin N)) le_rfl
      (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) (whitChar ψ N)
      (fun q hq => rfl) f.1 f.2 hf
    obtain ⟨_, h2⟩ := OpenCoinv.span_mem d hd ρ J (twKer ρ (unipM k d) (whitM d ψ)) _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      exact gen q.1 q.2 ⟨g, hg⟩) hs
    exact h2
  have key : ∀ f : openFns d hd ρ, J f = 0 →
      f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
    intro f hf
    obtain ⟨L, hLU, hLc, hLO, hsupp⟩ := GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f.1 f.2
    have hLB' : L ≤ unipB k (Fin N) := hLU.trans hUB
    let θL : L →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion hLB')
    have hopen : IsOpen (θL.ker : Set L) :=
      (GlobalTheory.Whittaker.isSmoothChar_whitChar (N := N) hψ).preimage (f := Subgroup.inclusion hLB') (continuous_subtype_val.subtype_mk fun x => hLB' x.2)
    obtain ⟨f', hd1, hd2, hd3⟩ := GlobalTheory.T.projection_to_twisted_eigenfunction_support _ _ L hLc θL hopen f.1
    have hsupp' : ∀ g, f'.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
      intro g hg
      obtain ⟨l, hl, hne⟩ := hd2 g hg
      obtain ⟨p, hp, u, hu, e⟩ := hsupp _ hne
      refine ⟨p, hp, u * l⁻¹, mul_mem hu (inv_mem hl), ?_⟩
      rw [← mul_assoc, ← e]
      group
    have hf'o : f' ∈ openFns d hd ρ := fun g hg => by
      obtain ⟨p, hp, u, hu, e⟩ := hsupp' g hg
      exact ⟨p, hp, u, hLB' hu, e⟩
    have hdiff := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ L hLB' (fun s hs => ⟨L, le_rfl, hs, hLc⟩) θL
      (fun q hq => rfl) (f.1 - f') (sub_mem f.2 hf'o) hd1
    obtain ⟨hx, hJ0⟩ := OpenCoinv.span_mem d hd ρ J ⊥ _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      have hqb := hLB' q.2
      have hx : parInd (stdBlocks d hd) ρ q.1 g - ((θL q : ℂˣ) : ℂ) • g ∈ openFns d hd ρ :=
        sub_mem (OpenCoinv.translate_mem d hd ρ hqb hg) (Submodule.smul_mem _ _ hg)
      refine ⟨hx, ?_⟩
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ q.1 g, OpenCoinv.translate_mem d hd ρ hqb hg⟩
      have e1 : J g1 = ((whitChar ψ N ⟨q.1, hqb⟩ : ℂˣ) : ℂ) • J ⟨g, hg⟩ := hU q.1 (hLU q.2) hqb ⟨g, hg⟩ g1 rfl
      have e2 : (⟨_, hx⟩ : openFns d hd ρ) = g1 - ((θL q : ℂˣ) : ℂ) • ⟨g, hg⟩ := rfl
      rw [e2, map_sub, map_smul, e1]
      exact (sub_self _ : _ = (0 : W))) hdiff
    let F' : openFns d hd ρ := ⟨f', hf'o⟩
    have hJF : J F' = 0 := by
      have e : (⟨_, hx⟩ : openFns d hd ρ) = f - F' := rfl
      rw [e, map_sub, hf] at hJ0
      simpa using hJ0
    obtain ⟨hpos, hJ⟩ := hV L hLU hLc hLO
    have hv := hJ F' (f'.1.1 (pm k (wOpen d hd))) (fun u hb hu => hd3 ⟨u, hu⟩ _) (fun u hu hnot => by
      by_contra hne
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' _ hne
      exact hnot (huniq p hp l (hLU hl) u hu e.symm ▸ hl))
    have hne : (vol L : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hv0 : f'.1.1 (pm k (wOpen d hd)) = 0 := by
      rw [hJF] at hv
      exact (smul_eq_zero.1 hv.symm).resolve_left hne
    have hf0 : f' = 0 := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      by_contra hg
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' g hg
      apply hg
      have h1 := f'.1.2 ⟨p, hp⟩ (pm k (wOpen d hd))
      rw [hv0, map_zero] at h1
      rw [e]
      have h2 := hd3 ⟨l, hl⟩ (p * pm k (wOpen d hd))
      rw [show f'.1.1 (p * pm k (wOpen d hd)) = 0 from h1, smul_zero] at h2
      exact h2
    rw [hf0, sub_zero] at hd1
    refine (Submodule.span_le.2 ?_ : twKer (parInd (stdBlocks d hd) ρ) L θL ≤ _) hd1
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨⟨n.1, hLB' n.2⟩, v, rfl⟩
  have lift : ∀ s ∈ twKer ρ (unipM k d) (whitM d ψ), ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨m, v, rfl⟩
      obtain ⟨g, rfl⟩ := surj v
      obtain ⟨a, ha, hm⟩ := hl2 m
      have hab := hLB ha
      obtain ⟨m', hm', hθ⟩ := hl1 a ha hab
      have hmm : m = m' := Subtype.ext (OpenCoinv.leviEmb_inj d hd (hm.symm.trans hm'))
      subst hmm
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g.1, OpenCoinv.translate_mem d hd ρ hab g.2⟩
      refine ⟨g1 - ((whitChar ψ N ⟨a, hab⟩ : ℂˣ) : ℂ) • g, Submodule.subset_span ⟨⟨a, hab⟩, g.1, rfl⟩, ?_⟩
      rw [map_sub, map_smul, hL a ha m hm g g1 rfl, hθ]
    · exact ⟨0, zero_mem _, map_zero J⟩
    · rintro x y _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
      exact ⟨F + F', add_mem hF hF', map_add J F F'⟩
    · rintro c x _ ⟨F, hF, rfl⟩
      exact ⟨c • F, Submodule.smul_mem _ c hF, map_smul J c F⟩
  refine ⟨J, vol, surj, fun f => ⟨fun hf => ?_, bwd f⟩, hU, hL, hV⟩
  obtain ⟨F, hF, e⟩ := lift _ hf
  have h0 := key (f - F) (by rw [map_sub, e, sub_self])
  have h1 : (f : IndSp (stdBlocks d hd) ρ) = (f - F).1 + F.1 := by
    show (f : IndSp (stdBlocks d hd) ρ) = (f.1 - F.1) + F.1
    rw [sub_add_cancel]
  rw [h1]
  exact add_mem h0 hF

end PositivityTheory.RgUd.CellB
