import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem exists_compl_of_admissible {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hs : IsSmooth ρ) (hun : IsUnitarisable ρ) (W : Subrepresentation ρ) (hW : IsAdmissible W.toRepresentation) :
    ∃ W' : Subrepresentation ρ, (∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule → v = 0) ∧
      ∀ v, ∃ w ∈ W.toSubmodule, v - w ∈ W'.toSubmodule := by
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hi W, fun v hv hv' => ?_, fun v => ?_⟩
  · by_contra hv0
    have h0 : B v v = 0 := hv' v hv
    simpa [h0] using hp v hv0
  · obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hs v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed W.toRepresentation K) := hW.2 K hKo hKc
    have hmap : (fixed W.toRepresentation K).map W.toSubmodule.subtype = W.toSubmodule ⊓ fixed ρ K := by
      ext u
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u.2, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K _).2 fun g hg => ?_⟩
        exact congrArg Subtype.val ((GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff _ K u).1 hu g hg)
      · rintro ⟨h1, h2⟩
        refine ⟨⟨u, h1⟩, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff _ K _).2 fun g hg => ?_, rfl⟩
        exact Subtype.ext ((GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K u).1 h2 g hg)
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := by
      rw [← hmap]
      exact (Module.Finite.iff_fg.1 hfd).map _
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    exact ⟨w, hw.1, fun y hy =>
      GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hs y)⟩

private theorem isIrreducible_of_occurs (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (hun : IsUnitarisable π)
    (hone : ∀ (T : Subrepresentation π) (v : V), v ∈ T.toSubmodule → v ≠ 0 →
      1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : π.IsIrreducible := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hSs : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs
  have hSa : IsAdmissible S.toRepresentation :=
    (hBZ k).1 _ _ _ hSs (GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS)
  have hS1 : 1 ≤ jhMult ρ (jac e S.toRepresentation) := by
    by_contra hc
    refine hS.1 (le_antisymm (fun v hv => ?_) bot_le)
    by_contra hv0
    exact hc (hone S v hv hv0)
  obtain ⟨T, hST, hsum⟩ := exists_compl_of_admissible π
    (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun S hSa
  have hT : ∀ v ∈ T.toSubmodule, v = 0 := by
    intro v hv
    by_contra hv0
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      exact Subtype.ext (hST _ ((hp0 _).1 hu) u.2)
    have h1 : 1 ≤ jhMult ρ (jac e T.toRepresentation) :=
      hone T v hv hv0
    have h2 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S)) :=
      h1.trans (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have h3 : (2 : ℕ∞) ≤ jhMult ρ (jac e π) := by
      rw [GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans
        (add_le_add hS1 h2)
    exact absurd (h3.trans hjm) (by norm_num)
  have htop : S = ⊤ := by
    refine le_antisymm le_top fun v _ => ?_
    obtain ⟨w, hw, h⟩ := hsum v
    rw [sub_eq_zero.1 (hT _ h)]
    exact hw
  rw [htop] at hS
  exact isSimpleOrder_iff_isAtom_top.2 hS

private theorem isIrreducible_parInd_emb (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s s' N : ℕ} {d : Fin s → ℕ}
    {d' : Fin s' → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (e' : (Σ a, Fin (d' a)) ≃ Fin N) {X X' : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ)
    {σ : Representation ℂ (Levi k fun a => Fin (d' a)) X'} (hσ : σ.IsIrreducible)
    (hun : IsUnitarisable (parInd e ρ)) (f : (parInd e ρ).IntertwiningMap (parInd e' σ))
    (hf : Function.Injective f) (hjm : jhMult σ (jac e' (parInd e' σ)) ≤ 1) :
    (parInd e ρ).IsIrreducible := by
  haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp e hρ hsρ
  have hsw : IsSmooth (parInd e' σ) := isSmooth_parInd _ _
  refine isIrreducible_of_occurs hBZ e' hσ (parInd e ρ) (isSmooth_parInd _ _)
    ((hBZ k).2.2.1 _ _ _ e _ ρ hsρ (hasFiniteLength_of_isIrreducible hρ)) hun (fun T v hv hv0 => ?_) ?_
  · let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    exact GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e' hσ (f.comp ιT)
      ⟨⟨v, hv⟩, fun h0 => hv0 (hf (h0.trans (map_zero f).symm))⟩
  · exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ (jacMap e' f)
      (GlobalTheory.JacInj.jacMap_injective k _ _ _ e' _ _ _ _ _ hsw hf)).trans hjm

theorem UpperTheory.Lit.Full.ssEmb :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL k) (N h : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (w : Fin h → IrrGL k) (hw : ∑ a, (w a).1 = N), IsUnitarisable x.rep → IsUnitarisable y.rep → (∃ f : (prodIrr ![x, y] hd).IntertwiningMap (prodIrr w hw), Function.Injective f) → jm w hw (prodIrr w hw) ≤ 1 → (prodIrr ![x, y] hd).IsIrreducible := by
  intro hBZ k _ _ _ _ x y N h hd w hw hx hy hf hjm
  obtain ⟨f, hf⟩ := hf
  have hρ : (piTensor fun a => (![x, y] a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) ![x, y]
  have hsρ : IsSmooth (piTensor fun a => (![x, y] a).rep) := isSmooth_piTensor fun a => (![x, y] a).2.rep.smooth
  have hσ : (piTensor fun a => (w a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) w
  have hu : ∀ a, IsUnitarisable (![x, y] a).rep := fun a => by
    fin_cases a
    · exact hx
    · exact hy
  exact isIrreducible_parInd_emb hBZ _ _ hρ hsρ hσ (GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd _ hu) f hf hjm
