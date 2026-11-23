import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedUnipotentCompactExhaustion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellHeightStratification
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentDescentOrOpenCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCharacterNontrivialOnCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellHeightLocalReduction
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.Bad

section Gen

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  {P : Subgroup G} {τ : Representation ℂ P W}

theorem isClopen_supp (f : smoothPart (ind P τ)) : IsClopen {g | f.1.1 g ≠ 0} := by
  have ho : IsOpen {g : G | ind P τ g f.1 = f.1} := f.2
  have hlc : IsLocallyConstant f.1.1 := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x =>
      ⟨(fun y => x⁻¹ * y) ⁻¹' {g | ind P τ g f.1 = f.1}, ho.preimage (by fun_prop), ?_, ?_⟩
    · show ind P τ (x⁻¹ * x) f.1 = f.1
      simp
    · intro y hy
      have h : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
      rwa [mul_inv_cancel_left] at h
  exact (hlc.isClopen_fiber 0).compl

theorem ne_zero_left (f : smoothPart (ind P τ)) (p : P) (g : G) (hg : f.1.1 g ≠ 0) : f.1.1 (p * g) ≠ 0 := by
  intro h
  have h1 : τ p (f.1.1 g) = 0 := (f.1.2 p g).symm.trans h
  apply hg
  have h2 := congrArg (τ p⁻¹) h1
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
  exact h2

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cell_mul {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {w : Equiv.Perm (Fin N)} {g n : GL (Fin N) k}
    (hg : g ∈ cell k d hd w) (hn : n ∈ unipB k (Fin N)) : g * n ∈ cell k d hd w := by
  obtain ⟨p, hp, m, hm, rfl⟩ := hg
  exact ⟨p, hp, m * n, mul_mem hm hn, by simp only [mul_assoc]⟩

theorem kill_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (w : Equiv.Perm (Fin N)) (hbad : cell k d hd w ≠ cell k d hd (wOpen d hd))
    (hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w)) :
    ∃ f' : IndSp (stdBlocks d hd) ρ,
      f - f' ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ n ∈ unipB k (Fin N), f.1.1 (g * n) ≠ 0) ∧
      ∀ g ∈ cell k d hd w, f'.1.1 g = 0 := by
  classical
  obtain ⟨L, hLm, hLc, hLU, hLex⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N (unipB k (Fin N)) le_rfl
    GlobalTheory.LocLanglands.InvInt.isClosed_unipB
  have hcellL : cell k d hd w =
      {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ j, ∃ n ∈ L j, g = p * pm k w * n} := by
    ext g
    constructor
    · rintro ⟨p, hp, n, hn, rfl⟩
      obtain ⟨j, hj⟩ := hLex n hn
      exact ⟨p, hp, j, n, hj, rfl⟩
    · rintro ⟨p, hp, j, n, hn, rfl⟩
      exact ⟨p, hp, n, hLU j hn, rfl⟩
  have : T2Space (GL (Fin N) k) := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    infer_instance
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset (parab k (stdBlocks d hd))
    (GlobalTheory.WhitHered.CellLoc.isClosed_parab (stdBlocks d hd)) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k)) GlobalTheory.SplitFlip.isCompact_KO
    (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩)
    L hLm hLc (pm k w) {g | f.1.1 g ≠ 0} (isClopen_supp f).isOpen
    (fun p hp g hg => ne_zero_left f ⟨p, hp⟩ g hg) (by rw [← hcellL]; exact hcl)
  obtain ⟨i, j, hij, hb⟩ := (exists_adjacent_blk_lt_or_cell_eq_open k h N d hd w).resolve_right hbad
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (by ext x; simp [hc x])
  obtain ⟨u, hu, hwu, hrad⟩ := GlobalTheory.CompanionTheory.Rodier.RootElt.exists_root_conj_mem_unipRad k ψ h N d hd w i j hij hb t
  obtain ⟨j₁, hj₁⟩ := hLex u hu
  have hJ0 : L j₀ ≤ L (max j₀ j₁) := hLm (le_max_left _ _)
  have hJ1 : L j₁ ≤ L (max j₀ j₁) := hLm (le_max_right _ _)
  generalize max j₀ j₁ = J at hJ0 hJ1
  let θ : L J →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion (hLU J))
  have hθ : IsOpen (θ.ker : Set (L J)) :=
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ).preimage
      (Continuous.subtype_mk continuous_subtype_val _ : Continuous (Subgroup.inclusion (hLU J)))
  obtain ⟨f', h1, h2, h3⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd (parab k (stdBlocks d hd)) _ (L J) (hLc J) θ hθ f
  have hu' : u ∈ L J := hJ1 hj₁
  have hfw : f'.1.1 (pm k w) = 0 := by
    have e1 := h3 ⟨u, hu'⟩ (pm k w)
    have hθu : θ ⟨u, hu'⟩ = Circle.toUnits (ψ t) := hwu
    have hq : leviProj k (stdBlocks d hd) ⟨_, unipRad_le_parab k _ hrad⟩ = 1 :=
      (coe_mem_unipRad k (⟨_, unipRad_le_parab k _ hrad⟩ : parab k (stdBlocks d hd))).1 hrad
    have e2 := parInd_law (stdBlocks d hd) ρ f' ⟨_, unipRad_le_parab k _ hrad⟩ (pm k w)
    rw [hq] at e2
    simp only [map_one, Units.val_one, one_smul, Module.End.one_apply, inv_mul_cancel_right] at e2
    rw [e2] at e1
    rw [hθu] at e1
    have hne : ((Circle.toUnits (ψ t) : ℂˣ) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
    have h0 : (((Circle.toUnits (ψ t) : ℂˣ) : ℂ) - 1) • f'.1.1 (pm k w) = 0 := by
      rw [sub_smul, one_smul, ← e1, sub_self]
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  refine ⟨f', ?_, ?_, ?_⟩
  · refine (Submodule.span_mono ?_) h1
    rintro _ ⟨n, v, rfl⟩
    exact ⟨⟨n.1, hLU J n.2⟩, v, rfl⟩
  · intro g hg
    obtain ⟨l, hl, hne⟩ := h2 g hg
    exact ⟨l, hLU J hl, hne⟩
  · intro g hg
    by_contra hne
    obtain ⟨l, hl, hfl⟩ := h2 g hne
    have hgl := cell_mul hg (hLU J hl)
    obtain ⟨p, hp, n, hn, e⟩ := hj₀ (g * l) hfl (by rw [hcellL] at hgl; exact hgl)
    have hl2 : n * l⁻¹ ∈ L J := mul_mem (hJ0 hn) (inv_mem hl)
    have hg' : g = (⟨p, hp⟩ : parab k (stdBlocks d hd)) * (pm k w * (n * l⁻¹)) := by
      show g = p * (pm k w * (n * l⁻¹))
      rw [← mul_assoc, ← mul_assoc, ← e]
      group
    apply hne
    have e3 := h3 ⟨_, hl2⟩ (pm k w)
    rw [hfw, smul_zero] at e3
    rw [hg', f'.1.2 ⟨p, hp⟩, e3, map_zero]

end GlobalTheory.CompanionTheory.Rodier.Bad

namespace GlobalTheory.CompanionTheory.Rodier

open Bad in

theorem exists_open_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ),
    ∃ f₀ ∈ openFns d hd ρ, f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd W _ _ ρ f
  classical
  obtain ⟨hcov, ht, hconst, hclos, hmax⟩ := GlobalTheory.CompanionTheory.Rodier.CellOrder.cells_main k h N d hd
  let bad : IndSp (stdBlocks d hd) ρ → Finset (Equiv.Perm (Fin N)) := fun f =>
    Finset.univ.filter fun w => cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0
  have mem_bad : ∀ f w, w ∈ bad f ↔
      cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0 := fun f w => by
    simp [bad]
  suffices H : ∀ n, ∀ f, (bad f).card = n → ∃ f₀ ∈ openFns d hd ρ,
      f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) from H _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn
  rcases (bad f).eq_empty_or_nonempty with hE | hne
  · refine ⟨f, ?_, by simp⟩
    intro g hg
    obtain ⟨w, hw⟩ := hcov g
    by_contra hno
    have hb : w ∈ bad f := (mem_bad f w).2 ⟨fun e => hno (e ▸ hw), g, hw, hg⟩
    simp [hE] at hb
  · obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (bad f) (fun w => ht (pm k w)) hne
    obtain ⟨hbad, hmet⟩ := (mem_bad f w).1 hw
    have hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w) := by
      refine isClosed_of_closure_subset fun x hx => ?_
      have hxS : x ∈ {g | f.1.1 g ≠ 0} :=
        (isClopen_supp f).isClosed.closure_subset_iff.2 Set.inter_subset_left hx
      refine ⟨hxS, ?_⟩
      rcases hclos w (closure_mono Set.inter_subset_right hx) with hC | hlt
      · exact hC
      · exfalso
        have hlt' : ht x < ht (pm k w) := hlt
        obtain ⟨w', hw'⟩ := hcov x
        by_cases ho : cell k d hd w' = cell k d hd (wOpen d hd)
        · have h1 : ht x = ht (pm k (wOpen d hd)) := by
            rw [hconst w' x hw']
            refine (hconst w' _ ?_).symm
            rw [ho]
            exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
          have := hmax w hbad
          omega
        · have h1 := hmin w' ((mem_bad f w').2 ⟨ho, x, hw', hxS⟩)
          have h2 := hconst w' x hw'
          omega
    obtain ⟨f', h1, h2, h3⟩ := kill_cell ψ hψ hψ1 d hd ρ f w hbad hcl
    have hsub : bad f' ⊂ bad f := by
      refine (Finset.ssubset_iff_of_subset fun w' hw' => ?_).2 ⟨w, hw, fun hw' => ?_⟩
      · obtain ⟨hb, g, hg, hfg⟩ := (mem_bad f' w').1 hw'
        obtain ⟨n, hn, hfn⟩ := h2 g hfg
        exact (mem_bad f w').2 ⟨hb, g * n, cell_mul hg hn, hfn⟩
      · obtain ⟨_, g, hg, hfg⟩ := (mem_bad f' w).1 hw'
        exact hfg (h3 g hg)
    have hlt : (bad f').card < n := hn ▸ Finset.card_lt_card hsub
    obtain ⟨f₀, hf₀, h4⟩ := ih _ hlt f' rfl
    refine ⟨f₀, hf₀, ?_⟩
    have := add_mem h1 h4
    simpa using this

end GlobalTheory.CompanionTheory.Rodier

end
