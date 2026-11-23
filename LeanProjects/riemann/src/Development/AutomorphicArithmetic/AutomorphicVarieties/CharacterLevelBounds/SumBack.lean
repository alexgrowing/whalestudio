import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sumBack_one {ι : Type} (S : Finset ι) (f : ι → ℕ∞) (a : ℕ∞) (b E : ℕ) (hE : E ≠ 0)
    (hf : ∀ i ∈ S, f i ≠ ⊤) (h : a * (E : ℕ∞) ≤ ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞))) :
    a ≠ ⊤ ∧ (a.toNat : ℝ) ≤ ∑ i ∈ S, ((f i).toNat : ℝ) / (E : ℝ) + S.card * (b : ℝ) := by
  have hsum : ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞)) = ((∑ i ∈ S, ((f i).toNat + b * E) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    push_cast
    rw [ENat.coe_toNat (hf i hi)]
  rw [hsum] at h
  have ha : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (by exact_mod_cast hE)] at h
    exact absurd h (not_le.2 (ENat.coe_lt_top _))
  refine ⟨ha, ?_⟩
  have h2 : a.toNat * E ≤ ∑ i ∈ S, ((f i).toNat + b * E) := by
    rw [← ENat.coe_toNat ha] at h
    exact_mod_cast h
  have hE' : (0 : ℝ) < E := by exact_mod_cast Nat.pos_of_ne_zero hE
  have h3 : (a.toNat : ℝ) * E ≤ ∑ i ∈ S, (((f i).toNat : ℝ) + b * E) := by exact_mod_cast h2
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h3
  rw [← Finset.sum_div]
  have h4 : (∑ i ∈ S, ((f i).toNat : ℝ)) / E + S.card * (b : ℝ) = ((∑ i ∈ S, ((f i).toNat : ℝ)) + S.card * ((b : ℝ) * E)) / E := by
    field_simp
  rw [h4, le_div_iff₀ hE']
  exact h3

theorem UpperTheory.V.Chr.sumBack :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) (T : ℕ → Finset ι) (T₀ : Finset ι) (f : ι → ℕ → ℕ∞) (a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ),
          (∀ e, T e ⊆ T₀) → (∀ e, 0 < e → e < t → (∀ i ∈ T e, f i e ≠ ⊤) ∧ a e * eO l O ≤ ∑ i ∈ T e, (f i e + (b e : ℕ∞) * eO l O)) →
          (∀ e, 0 < e → e < t → a e ≠ ⊤) ∧
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, nrm l O (f i e) + T₀.card * ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) := by
  intro l _ O _ _ _ _ _ ι T T₀ f a b t hT h
  obtain ⟨-, -, -, -, -, hne, hle, -, -⟩ := dvrFacts l O
  have htop : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  have hEO : eO l O = (((eO l O).toNat : ℕ) : ℕ∞) := (ENat.coe_toNat htop).symm
  have hE : (eO l O).toNat ≠ 0 := by
    intro h0
    apply hne
    rw [hEO, h0]
    rfl
  have key : ∀ e ∈ Finset.Ico 1 t, a e ≠ ⊤ ∧ ((a e).toNat : ℝ) ≤ ∑ i ∈ T e, ((f i e).toNat : ℝ) / ((eO l O).toNat : ℝ) + (T e).card * (b e : ℝ) := by
    intro e he
    rw [Finset.mem_Ico] at he
    obtain ⟨h1, h2⟩ := h e (by omega) he.2
    rw [hEO] at h2
    exact sumBack_one (T e) (fun i => f i e) (a e) (b e) _ hE h1 h2
  refine ⟨fun e he0 het => (key e (Finset.mem_Ico.2 ⟨he0, het⟩)).1, ?_⟩
  have hn : ∀ x, nrm l O x = (x.toNat : ℝ) / ((eO l O).toNat : ℝ) := fun x => rfl
  simp only [hn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => (key e he).2.trans ?_
  gcongr
  exact hT e
