import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem unit_eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : kˣ) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  apply Units.ext
  have h' : ((x : k) - 1) ^ l ^ m = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero)).mp h')

private theorem mu_pow {l : ℕ} [Fact l.Prime] (F : GFrame l) (v : F.Vl) (g : F.mu v) :
    ∃ m : ℕ, (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := by
  have hg : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ∈
      CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l := g.2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ^ l ^ m = 1 := by
    first
      | exact hg
      | (obtain ⟨m, hm⟩ := hg; exact ⟨m, by rw [← hm]; exact pow_orderOf_eq_one _⟩)
  refine ⟨m, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  exact hm

theorem UpperTheory.V.W.residualDatum_inertia_characters_trivial :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v), r.psib v i g = 1 ∧ Units.map (residue O : O →* ResidueField O) (r.th v i g) = 1 := by
  intro l _ F O _ _ _ _ n r v i g
  obtain ⟨m, hm⟩ := mu_pow F v g
  constructor
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow]
    have hle : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
      Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
        (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
    exact hle hm
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow, ← map_pow, r.th_comm v i (g ^ l ^ m) (by simpa using hm), map_one]
