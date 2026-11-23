import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.Overlap

theorem omHT_pow_smul_mem : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R N V), (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin N → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ R) • w) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ a ∈ chartRing o (mseg y) s.1, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n * a ∈ chartRing o (mseg y) t.1) → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ' := by
  intro o _ Ω _ _ K _ J _ y E _ _ c p R N V _ _ Dc hom hh hρ hring s t σ'
  set f : Ω := mseg y s.1 / mseg y t.1 with hf
  have hfA : f ∈ chartRing o (mseg y) t.1 := Algebra.subset_adjoin ⟨s.1, rfl⟩
  have hfMn : ∀ n : ℕ, ∀ z ∈ (Dc t).om', f ^ n • z ∈ (Dc t).om' := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact (Dc t).om'.smul_mem (⟨f, hfA⟩ : chartRing o (mseg y) t.1) (ih z hz)
  let P : Submodule (chartRing o (mseg y) s.1) V :=
    { carrier := {z | ∃ n : ℕ, f ^ n • z ∈ (Dc t).om'}
      add_mem' := by
        rintro a b ⟨n, hn⟩ ⟨m, hm⟩
        refine ⟨n + m, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [add_comm, pow_add, mul_smul]; exact hfMn m _ hn
        · rw [pow_add, mul_smul]; exact hfMn n _ hm
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro a z ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hring s t (a : Ω) a.2
        refine ⟨n + m, ?_⟩
        have e1 : f ^ (n + m) • (a • z) = (⟨f ^ m * a, hm⟩ : chartRing o (mseg y) t.1) • (f ^ n • z) := by
          show f ^ (n + m) • ((a : Ω) • z) = (f ^ m * a) • (f ^ n • z)
          rw [smul_smul, smul_smul]; congr 1; ring
        rw [e1]; exact (Dc t).om'.smul_mem _ hn }
  have hle : (Dc s).om' ≤ P := by
    unfold HTChart.om'
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨δ, rfl⟩
      obtain ⟨n, w, hw, he⟩ := hh s t δ
      refine ⟨n, ?_⟩
      have e2 : f ^ n • (Dc s).h δ = f ^ n • (Dc t).h δ + ((p : Ω) ^ R) • w := by
        rw [← he, smul_sub]; abel
      rw [e2]
      refine add_mem (hfMn n _ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨δ, rfl⟩)
      · refine Submodule.mem_sup_right ⟨w, hw, ?_⟩
        simp [Subalgebra.smul_def]
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := hom s t u hu
      refine ⟨n, ?_⟩
      refine Submodule.mem_sup_right ⟨f ^ n • u, hn, ?_⟩
      simp [Subalgebra.smul_def, smul_comm ((p : Ω) ^ R) (f ^ n) u]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hle hz
  refine ⟨n, ⟨f ^ n • z, hn, ?_⟩⟩
  show eigProj (Dc t).ρΩ σ' (f ^ n • z) = f ^ n • eigProj (Dc s).ρΩ σ' z
  rw [hρ s t, map_smul]

end GlobalTheory.CompanionTheory.Ar.HT.Overlap
