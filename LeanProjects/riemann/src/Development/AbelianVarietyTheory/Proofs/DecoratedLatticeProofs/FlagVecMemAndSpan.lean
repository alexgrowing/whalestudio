import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagBasis

theorem flagVec_mem_and_span (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I)
    (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
      (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧
        ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  intro hF hn
  obtain ⟨⟨hef, hz, hb⟩, -, -, -, ⟨hidem, horth, hint, -⟩, ⟨hbw, hbwd⟩, -, hspan⟩ := hF
  refine ⟨fun j => ?_, fun y hy => ?_⟩
  · unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact (hef _).1
    · exact I.Lf.add_mem (hb _).1 (hb _).2
    · exact hz
    · exact (hef _).2
    · exact I.Lf.zero_mem
  · set R : Set (VA I) := Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val with hR
    have hmem : ∀ j, j < I.n → flagVec e0 f0 z0 bw bwd j ∈ Submodule.span (IntAf I.F I.E) R :=
      fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    have hsig : sigA I ew ∈ IntAf I.F I.E := Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I hint
    have hc : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) = bw l + bwd (Fin.rev l) := by
      intro l
      have h1 : ¬ (ρ + l.val < ρ) := by omega
      have h2 : ρ + l.val - ρ < k := by omega
      unfold flagVec
      rw [dif_neg h1, dif_pos h2]
      congr <;> simp
    have hcl : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.val) ∈ Submodule.span (IntAf I.F I.E) R :=
      fun l => hmem _ (by omega)
    have hsub : Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ⊆
        (Submodule.span (IntAf I.F I.E) R : Set (VA I)) := by
      rintro v ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
      · have h := hmem a.val (by omega)
        unfold flagVec at h
        rwa [dif_pos a.isLt] at h
      · have h := hmem (2 * ρ + k - a.val) (by omega)
        have h1 : ¬ (2 * ρ + k - a.val < ρ) := by omega
        have h2 : ¬ (2 * ρ + k - a.val - ρ < k) := by omega
        have h3 : ¬ (2 * ρ + k - a.val = ρ + k) := by omega
        have h4 : 2 * ρ + k - (2 * ρ + k - a.val) < ρ := by omega
        unfold flagVec at h
        rw [dif_neg h1, dif_neg h2, if_neg h3, dif_pos h4] at h
        have e : (⟨2 * ρ + k - (2 * ρ + k - a.val), h4⟩ : Fin ρ) = a := by ext; simp; omega
        rwa [e] at h
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        have h := hmem (ρ + k) (by omega)
        have h1 : ¬ (ρ + k < ρ) := by omega
        have h2 : ¬ (ρ + k - ρ < k) := by omega
        unfold flagVec at h
        rwa [dif_neg h1, dif_neg h2, if_pos rfl] at h
      · have h := Submodule.smul_mem _ (⟨ew, hint⟩ : IntAf I.F I.E) (hcl l)
        rw [hc l] at h
        have e : ((⟨ew, hint⟩ : IntAf I.F I.E) • (bw l + bwd (Fin.rev l)) : VA I) = bw l := by
          show ew • (bw l + bwd (Fin.rev l)) = bw l
          rw [smul_add, hbwd (Fin.rev l), smul_smul, horth, zero_smul, add_zero, ← hbw l]
        rwa [e] at h
      · have h := Submodule.smul_mem _ (⟨sigA I ew, hsig⟩ : IntAf I.F I.E) (hcl (Fin.rev l))
        rw [hc (Fin.rev l), Fin.rev_rev] at h
        have e : ((⟨sigA I ew, hsig⟩ : IntAf I.F I.E) • (bw (Fin.rev l) + bwd l) : VA I) = bwd l := by
          show sigA I ew • (bw (Fin.rev l) + bwd l) = bwd l
          rw [smul_add, hbw (Fin.rev l), smul_smul, mul_comm, horth, zero_smul, zero_add,
            hbwd l, smul_smul, ← map_mul, hidem]
        rwa [e] at h
    have := hspan y hy
    exact sup_le_sup_right (Submodule.span_le.2 hsub) _ this

end GlobalTheory.FlagBasis
