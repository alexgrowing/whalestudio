import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q F 𝔞 had h𝔞 h1 h2
  obtain ⟨h3, h4⟩ := LevelTowerAlt.sub_eig A had.2
  have h5 := (LevelTowerAlt.Sub.of_smul_le h𝔞 h1).trans h3
  have h6 := h4.trans (LevelTowerAlt.Sub.of_smul_le h𝔞 h2)
  have e1 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h3 h4 h5 h2
  have e2 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h5 h6 h3 h1
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  push_cast at e1 e2
  rw [LinPt.labDeg, LinPt.labDeg, ← sub_div, abs_div, abs_of_pos hn]
  refine div_le_div_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) hn.le <;> linarith
