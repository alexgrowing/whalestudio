import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

theorem id_unit : ScalarRootOfUnity := by
  intro E _ _ _ S r T Λ F F' c hsc hzΛ hprim hcc hz hX
  have hz'o : F'.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    intro x hx
    have hx' : x ∈ F'.fl.X := by rw [hX]; exact hx
    exact tie_X_le_ker F'.fl _ F'.fl.z_orth x hx'
  have hzo : F.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    exact tie_X_le_ker F.fl _ F.fl.z_orth
  have hmem : c • F.fl.z ∈ Lsub Λ F := by
    unfold Lsub
    refine ⟨?_, (orth S (Xsp F)).smul_mem c hzo⟩
    have e : c • F.fl.z = F'.fl.z - (F'.fl.z - c • F.fl.z) := by abel
    rw [e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hz)
    exact ⟨hzΛ, hz'o⟩
  obtain ⟨o, ho⟩ := hprim c hmem
  refine ⟨o, ho, ?_⟩
  have hn : ∀ φ : E →+* ℂ, ‖φ (o : E)‖ = 1 := by
    intro φ
    have h1 := b_tau_norm hsc φ c
    rw [mul_comm, hcc, map_one] at h1
    have h2 : ‖φ c‖ ^ 2 = 1 := by exact_mod_cast h1.symm
    rw [ho]
    have h3 : 0 ≤ ‖φ c‖ := norm_nonneg _
    nlinarith
  obtain ⟨n, hn0, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ (x := (o : E)) o.isIntegral_coe hn
  refine ⟨n, hn0, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using h

theorem id_cong : ScalarCongruentOne := by
  intro E _ _ _ S r T Λ g F F' o hU hzΛ hadm hz P hg hT
  obtain ⟨ξ, _, hξ2, hξ3⟩ := hadm
  obtain ⟨s, hs, hw⟩ := hξ3 (Fin.last r) P hg

  have hzX : ∀ x ∈ Xsp F, S.hT F.fl.z x = 0 := fun x hx =>
    p_symm_zero S (tie_X_le_ker F.fl _ F.fl.z_orth x hx)
  have hze : ∀ a : Fin r, S.hT F.fl.z (F.fl.e a) = 0 := fun a => hzX _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : S.hT F.fl.z F'.fl.z = (o : E) * (-(T : E)) := by
    have e : F'.fl.z = (F'.fl.z - (o : E) • F.fl.z) + (o : E) • F.fl.z := by abel
    rw [e, map_add, hzX _ hz, zero_add, map_smul, smul_eq_mul, F.fl.z_norm]
  have h2 : S.hT F.fl.z (frameAct (frame F) ξ (Fin.last r)) = -(T : E) := by
    unfold frameAct
    rw [map_sum, Fin.sum_univ_castSucc]
    have hl : frame F (Fin.last r) = F.fl.z := by simp [FlagG.fvec]
    have hc : ∀ a : Fin r, frame F a.castSucc = F.fl.e a := fun a => by simp [FlagG.fvec]
    rw [hl, hξ2, map_smul, F.fl.z_norm]
    have : ∑ a : Fin r, S.hT F.fl.z (((ξ a.castSucc (Fin.last r) : 𝓞 E) : E) • frame F a.castSucc) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hc, map_smul, hze, smul_zero]
    rw [this, zero_add]
    simp
  have h3 : S.hT F.fl.z (frame F' (Fin.last r) - frameAct (frame F) ξ (Fin.last r)) =
      -(((o - 1 : 𝓞 E) : E) * (T : E)) := by
    have hl : frame F' (Fin.last r) = F'.fl.z := by simp [FlagG.fvec]
    rw [map_sub, hl, h1, h2]
    push_cast
    ring

  have h4 : ∀ y ∈ Ideal.span {(g : 𝓞 E)} • Λ, ∃ a : 𝓞 E, S.hT F.fl.z y = (((g : 𝓞 E) * a : 𝓞 E) : E) := by
    intro y hy
    rw [Submodule.ideal_span_singleton_smul] at hy
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hd : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hl
    obtain ⟨a, ha⟩ := d_mem_dual.1 hd _ hzΛ
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul E (g : 𝓞 E) l, map_smul, smul_eq_mul, ← ha]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := h4 _ hw
  rw [← algebraMap_smul E s, map_smul, smul_eq_mul, h3] at ha
  have h5 : s * ((o - 1) * (T : 𝓞 E)) = -((g : 𝓞 E) * a) := by
    apply RingOfIntegers.coe_injective
    have : (algebraMap (𝓞 E) E s) * (((o - 1 : 𝓞 E) : E) * (T : E)) = -(((g : 𝓞 E) * a : 𝓞 E) : E) := by
      rw [← ha]; ring
    simpa using this
  have h6 : s * ((o - 1) * (T : 𝓞 E)) ∈ P.asIdeal := by
    rw [h5]
    exact P.asIdeal.neg_mem (P.asIdeal.mul_mem_right _ hg)
  rcases P.isPrime.mem_or_mem h6 with h | h
  · exact absurd h hs
  · rcases P.isPrime.mem_or_mem h with h | h
    · exact h
    · exact absurd h hT

end Formalism.MainNotions.BridgeLemma

end
