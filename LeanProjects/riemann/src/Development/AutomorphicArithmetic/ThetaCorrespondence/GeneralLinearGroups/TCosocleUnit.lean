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
    by_contra hne
    have h1 : B v v = 0 := hv' v hv
    have h2 := hpos v hne
    rw [h1] at h2
    simp at h2
  · intro v
    obtain ⟨K, hKo, hKc, hKU⟩ := hbasis _ ((hs v).mem_nhds (by simp))
    have hfd := hW.2 K hKo hKc
    obtain ⟨t, ht⟩ := (Module.Finite.iff_fg.mp hfd).map W.toSubmodule.subtype
    have hM : ∀ s, s ∈ Submodule.span ℂ (t : Set V) ↔ s ∈ W.toSubmodule ∧ ∀ k ∈ K, ρ k s = s := by
      intro s
      rw [ht, Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hx
        exact ⟨x.2, fun k hk => congrArg Subtype.val (hx k hk)⟩
      · rintro ⟨hsW, hsK⟩
        refine ⟨⟨s, hsW⟩, ?_, rfl⟩
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff]
        intro k hk
        exact Subtype.ext (hsK k hk)
    obtain ⟨w, hw, hperp⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hpos t v
    refine ⟨w, ((hM w).mp hw).1, ?_⟩
    intro w' hw'
    have hvK : ∀ k ∈ K, ρ k v = v := fun k hk => hKU hk
    have huK : ∀ k ∈ K, ρ k (v - w) = v - w := fun k hk => by
      rw [map_sub, hvK k hk, ((hM w).mp hw).2 k hk]
    refine GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hinv K hKc W (v - w) huK (fun s hs' => hperp s ?_) w' hw' (hs w')
    rw [hM]
    exact ⟨hs'.1, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K s).mp hs'.2⟩

private theorem isCoatom_of_compl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {S T : Subrepresentation ρ} (hS : IsAtom S) (hST : ∀ v, v ∈ S.toSubmodule → v ∈ T.toSubmodule → v = 0)
    (hsum : ∀ v, ∃ w ∈ S.toSubmodule, v - w ∈ T.toSubmodule) : IsCoatom T := by
  constructor
  · intro hT
    obtain ⟨s, hsS, hs0⟩ : ∃ s ∈ S.toSubmodule, s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hS.1
      apply Subrepresentation.ext
      ext v
      show v ∈ S.toSubmodule ↔ v ∈ (⊥ : Submodule ℂ V)
      rw [Submodule.mem_bot]
      exact ⟨hcon v, fun h => h ▸ S.toSubmodule.zero_mem⟩
    apply hs0 (hST s hsS _)
    rw [hT]
    show s ∈ (⊤ : Submodule ℂ V)
    trivial
  · intro U hTU
    obtain ⟨hle, u, huU, huT⟩ := SetLike.lt_iff_le_and_exists.mp hTU
    obtain ⟨w, hwS, hwT⟩ := hsum u
    have hwU : w ∈ U.toSubmodule := by
      rw [← sub_sub_cancel u w]
      exact U.toSubmodule.sub_mem huU (hle hwT)
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply huT
      rw [sub_zero] at hwT
      exact hwT
    have hSU : S ≤ U := by
      have hinf : S ⊓ U = S := (hS.le_iff.mp inf_le_left).resolve_left (by
        intro h
        apply hw0
        have hm : w ∈ (S ⊓ U).toSubmodule := ⟨hwS, hwU⟩
        rw [h] at hm
        exact (Submodule.mem_bot ℂ).mp hm)
      rw [← hinf]
      exact inf_le_right
    apply Subrepresentation.ext
    ext v
    show v ∈ U.toSubmodule ↔ v ∈ (⊤ : Submodule ℂ V)
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨w', hw'S, hw'T⟩ := hsum v
    have hadd := U.toSubmodule.add_mem (hSU hw'S) (hle hw'T)
    simpa using hadd

private theorem equiv_of_isCosocle (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin N) k) X) (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (hfl : HasFiniteLength π) (hun : IsUnitarisable π) (hc : IsCosocle σ π) : Nonempty (σ.Equiv π) := by
  obtain ⟨-, f, hfs, hker⟩ := hc
  have hinj : Function.Injective f := by
    intro v w hvw
    by_contra hne
    have hmem : v - w ∈ (Representation.IntertwiningMap.ker π σ f).toSubmodule := by
      show v - w ∈ LinearMap.ker f.toLinearMap
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hvw
    have hK : Representation.IntertwiningMap.ker π σ f ≠ ⊥ := by
      intro hK0
      rw [hK0] at hmem
      exact hne (sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem))
    haveI := ((hasFiniteLength_iff_wellFounded π).mp hfl).2
    obtain ⟨S, hS, hSK⟩ := (eq_bot_or_exists_atom_le _).resolve_left hK
    let ι : S.toRepresentation.IntertwiningMap π :=
      (S.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => rfl)
    have hSs : IsSmooth S.toRepresentation :=
      IsSubquotient.isSmooth (IsSubquotient.of_injective ι Subtype.val_injective) hs
    have hSadm : IsAdmissible S.toRepresentation :=
      (hBZ k).1 (Fin N) _ S.toRepresentation hSs (GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS)
    obtain ⟨T, hST, hsum⟩ := exists_compl_of_admissible π
      (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun S hSadm
    have hTK := hker T (isCoatom_of_compl hS hST hsum)
    apply hS.1
    apply Subrepresentation.ext
    ext s
    show s ∈ S.toSubmodule ↔ s ∈ (⊥ : Submodule ℂ V)
    rw [Submodule.mem_bot]
    constructor
    · intro hs'
      apply hST s hs'
      rw [hTK]
      exact hSK hs'
    · rintro rfl
      exact S.toSubmodule.zero_mem
  exact ⟨(equivOfBijective f ⟨hinj, hfs⟩).symm⟩

theorem UpperTheory.Lit.Cas.cosocleUnit :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), (∀ a, IsUnitarisable (x a).rep) → IsCosocle π (prodIrr x hd) → Nonempty (π.Equiv (prodIrr x hd)) := by
  intro hBZ k _ _ _ _ h N x hd V _ _ π hun hc
  have hIA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k' _ _ _ _ n W _ _ ρ hs hi => (hBZ k').1 (Fin n) W ρ hs hi
  have hsm : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor (fun a => (x a).snd.rep.smooth)
  have hfl0 : HasFiniteLength (piTensor fun a => (x a).rep) :=
    hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hIA x)
  have hfl : HasFiniteLength (prodIrr x hd) :=
    (hBZ k).2.2.1 (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) _ _ hsm hfl0
  exact equiv_of_isCosocle hBZ π (prodIrr x hd) (isSmooth_prodIrr x hd) hfl
    (UnitInd.isUnitarisable_multiProd _ hun) hc
