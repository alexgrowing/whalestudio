import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem exists_compl_of_admissible {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hs : IsSmooth ρ) (hun : IsUnitarisable ρ) (W : Subrepresentation ρ) (hW : IsAdmissible W.toRepresentation) :
    ∃ W' : Subrepresentation ρ, (∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule → v = 0) ∧
      ∀ v, ∃ w ∈ W.toSubmodule, v - w ∈ W'.toSubmodule := by
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  refine ⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hinv W, ?_, ?_⟩
  · intro v hv hv'
    have h0 : B v v = 0 := hv' v hv
    by_contra hne
    have := hpos v hne
    rw [h0] at this
    simp at this
  · intro v
    obtain ⟨K, hKo, hKc, hKU⟩ := hbasis {g | ρ g v = v} ((hs v).mem_nhds (by simp))
    have hmap : (fixed W.toRepresentation K).map W.toSubmodule.subtype = W.toSubmodule ⊓ fixed ρ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ fixed W.toRepresentation K := hy
        refine ⟨y.2, ?_⟩
        show (y : V) ∈ fixed ρ K
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hy' ⊢
        intro k hk
        have := congrArg Subtype.val (hy' k hk)
        exact this
      · rintro ⟨hxW, hx⟩
        have hx' : x ∈ fixed ρ K := hx
        refine ⟨⟨x, hxW⟩, ?_, rfl⟩
        show (⟨x, hxW⟩ : W.toSubmodule) ∈ fixed W.toRepresentation K
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hx' ⊢
        intro k hk
        apply Subtype.ext
        exact hx' k hk
    have hfd0 : FiniteDimensional ℂ (fixed W.toRepresentation K) := hW.2 K hKo hKc
    have hfd : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) := by
      rw [← hmap]
      infer_instance
    obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
    obtain ⟨w, hw, hperp⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hpos t v
    rw [ht] at hw hperp
    refine ⟨w, hw.1, ?_⟩
    show ∀ x ∈ W.toSubmodule, B (v - w) x = 0
    intro x hx
    refine GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hinv K hKc W (v - w) ?_ hperp x hx (hs x)
    intro k hk
    have hv : ρ k v = v := hKU hk
    have hw' : ρ k w = w := (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K w).mp hw.2 k hk
    simp [map_sub, hv, hw']

private theorem isIrreducible_of_occurs (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (hun : IsUnitarisable π)
    (hone : ∀ (T : Subrepresentation π) (v : V), v ∈ T.toSubmodule → v ≠ 0 →
      1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : π.IsIrreducible := by
  have hGL := hBZ k
  have hnz : ∀ A : Subrepresentation π, A ≠ ⊥ → ∃ v, v ∈ A.toSubmodule ∧ v ≠ 0 := by
    intro A hA
    by_contra hcon
    push_neg at hcon
    apply hA
    apply Subrepresentation.ext
    show A.toSubmodule = ⊥
    rw [Submodule.eq_bot_iff]
    exact hcon
  have key : ∀ A : Subrepresentation π, IsAtom A → A = ⊤ := by
    intro A hA
    by_contra hAt
    have hAirr : A.toRepresentation.IsIrreducible :=
      GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom A hA
    have hAs : IsSmooth A.toRepresentation := by
      intro v
      have hset : {g | A.toRepresentation g v = v} = {g | π g v = v} := by
        ext g
        simp only [Set.mem_setOf_eq]
        exact Subtype.ext_iff
      rw [hset]
      exact hs v
    have hAad : IsAdmissible A.toRepresentation := hGL.1 (Fin N) _ A.toRepresentation hAs hAirr
    obtain ⟨A', hdis, hcod⟩ := exists_compl_of_admissible π
      (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun A hAad
    have hc : IsCompl A'.toSubmodule A.toSubmodule := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx' hx
        exact hdis x hx hx'
      · rw [Submodule.codisjoint_iff_exists_add_eq]
        intro z
        obtain ⟨w, hw, hzw⟩ := hcod z
        exact ⟨z - w, w, hzw, hw, by abel⟩
    let P := A'.toSubmodule.projectionOnto A.toSubmodule hc
    have hPv : ∀ v w, w ∈ A.toSubmodule → (hm : v - w ∈ A'.toSubmodule) → P v = ⟨v - w, hm⟩ := by
      intro v w hw hm
      have hv : v = w + (v - w) := by abel
      have h0 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
      have h1 : P (v - w) = ⟨v - w, hm⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v - w, hm⟩
      conv_lhs => rw [hv]
      rw [map_add, h0, zero_add, h1]
    have hPeq : ∀ g v, P (π g v) = A'.toRepresentation g (P v) := by
      intro g v
      obtain ⟨w, hw, hzw⟩ := hcod v
      have hm2 : π g v - π g w ∈ A'.toSubmodule := by
        rw [← map_sub]
        exact A'.apply_mem_toSubmodule g hzw
      rw [hPv v w hw hzw, hPv (π g v) (π g w) (A.apply_mem_toSubmodule g hw) hm2]
      apply Subtype.ext
      show π g v - π g w = π g (v - w)
      rw [map_sub]
    let p : π.IntertwiningMap A'.toRepresentation := ⟨P, fun g => LinearMap.ext fun v => hPeq g v⟩
    let ι : A.toRepresentation.IntertwiningMap π := ⟨A.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    have hsurj : Function.Surjective p := by
      intro y
      exact ⟨y, Submodule.linearProjOfIsCompl_apply_left hc y⟩
    have hexact : Function.Exact ι p := by
      intro y
      constructor
      · intro hy
        have hy' : y ∈ A.toSubmodule := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).mp hy
        exact ⟨⟨y, hy'⟩, rfl⟩
      · rintro ⟨z, rfl⟩
        exact Submodule.linearProjOfIsCompl_apply_right hc z
    have hex := GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact e hρ ι p hs Subtype.val_injective hsurj hexact
    obtain ⟨a, haA, ha0⟩ := hnz A hA.1
    have hA1 := hone A a haA ha0
    have hnt : ∃ v, v ∉ A.toSubmodule := by
      by_contra hcon
      push_neg at hcon
      apply hAt
      apply Subrepresentation.ext
      show A.toSubmodule = ⊤
      rw [Submodule.eq_top_iff']
      exact hcon
    obtain ⟨v, hv⟩ := hnt
    obtain ⟨w, hw, hzw⟩ := hcod v
    have hvw : v - w ≠ 0 := by
      intro h0
      apply hv
      rw [sub_eq_zero] at h0
      rw [h0]
      exact hw
    have hA2 := hone A' (v - w) hzw hvw
    have h2 : 1 + 1 ≤ jhMult ρ (jac e π) := by
      rw [hex]
      exact add_le_add hA1 hA2
    have h3 := h2.trans hjm
    norm_num at h3
  have hwf := ((hasFiniteLength_iff_wellFounded π).mp hfl).2
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt hwf.wf
  haveI : Nontrivial (Subrepresentation π) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    have hmem : v ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h'] at hmem
    exact hv ((Submodule.mem_bot ℂ).mp hmem)
  refine ⟨fun T => ?_⟩
  rcases eq_bot_or_exists_atom_le T with hT | ⟨A, hA, hAT⟩
  · exact Or.inl hT
  · right
    rw [key A hA] at hAT
    exact top_le_iff.mp hAT

private theorem isIrreducible_parInd (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ)
    (hun : IsUnitarisable (parInd e ρ)) (hjm : jhMult ρ (jac e (parInd e ρ)) ≤ 1) :
    (parInd e ρ).IsIrreducible := by
  haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp e hρ hsρ
  refine isIrreducible_of_occurs hBZ e hρ (parInd e ρ) (isSmooth_parInd _ _)
    ((hBZ k).2.2.1 _ _ _ e _ ρ hsρ (hasFiniteLength_of_isIrreducible hρ)) hun (fun T v hv hv0 => ?_) hjm
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  exact GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e hρ ιT ⟨⟨v, hv⟩, hv0⟩

theorem UpperTheory.Lit.Mix.ss :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), IsUnitarisable x.rep → IsUnitarisable y.rep → jm ![x, y] hd (prodIrr ![x, y] hd) ≤ 1 → (prodIrr ![x, y] hd).IsIrreducible := by
  intro hBZ k _ _ _ _ x y N hd hx hy hjm
  have hρ : (piTensor fun a => (![x, y] a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) ![x, y]
  have hsρ : IsSmooth (piTensor fun a => (![x, y] a).rep) := isSmooth_piTensor fun a => (![x, y] a).2.rep.smooth
  have hu : ∀ a, IsUnitarisable (![x, y] a).rep := fun a => by
    fin_cases a
    · exact hx
    · exact hy
  exact isIrreducible_parInd hBZ _ hρ hsρ (GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd _ hu) hjm
