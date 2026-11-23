import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfolding

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Proof.hasLatticeNormalForm_of_between

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.Proof.normal_form_bounds_unfolding

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n c : ℕ}

omit [StarRing E] in
theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N s : ℕ) : IntV P (Loc.eN E N s) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem read_bounds (P : HeightOneSpectrum (𝓞 E)) (j : ℕ) (h ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))
    (e : Fin c → ℤ) (z : Fin n → E) (hρ : ρ ∈ Loc.R1 E n c) (h1 : IntHom P h.symm.toLinearMap)
    (h2 : IntHom P (((qOf P : E) ^ j) • h.toLinearMap)) (hL : (ρ * h) '' {v | IntV P v} = nfLat P n c e z) :
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (1 ≤ c → IntV P z) := by
  have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
  have hmem : ∀ v, IntV P v → ρ v ∈ nfLat P n c e z := fun v hv => by
    rw [← hL]
    refine ⟨h.symm v, h1 v hv, ?_⟩
    change ρ (h (h.symm v)) = ρ v
    rw [h.apply_symm_apply]
  refine ⟨fun i => ⟨?_, ?_⟩, fun hc a => ?_⟩
  · obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ (ρ * h) '' {v | IntV P v} := hL ▸ nfGen_mem P e z i
    change ρ (h v) = _ at hrv
    have hU : h v ∈ Loc.Ufl E n c (i.1 + 1) := by
      have := hρ.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
      change ρ.symm (ρ (h v)) ∈ _ at this
      rwa [ρ.symm_apply_apply] at this
    have h3 : h v (Fin.natAdd n i) = (qOf P : E) ^ e i := by
      rw [← atN_natAdd (h v) i, ← atN_of_R1cond hρ.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h4 : IntAt P ((qOf P : E) ^ j * h v (Fin.natAdd n i)) := h2 v hv (Fin.natAdd n i)
    rw [h3, ← zpow_natCast, ← zpow_add₀ hq] at h4
    have := nonneg_of_intAt_zpow h4
    omega
  · have hc : 1 ≤ c := by have := i.2; omega
    obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem _ (intV_eN P (n + c) (n + i.1)))).1 i
    refine le_of_zpow_eq hu ?_
    rw [← h', ← atN_natAdd (ρ _) i, atN_of_R1cond hρ.1 (eN_mem_Ufl (by omega)), atN_natAdd]
    simp [Loc.eN]
  · have h3 := (coords_of_mem hc (hmem _ (intV_eN P (n + c) n))).2 a
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [hρ.1.2.1, h4, h5, one_mul, zero_sub] at h3
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h3

theorem nfLat_of_eq_zero (P : HeightOneSpectrum (𝓞 E)) (hc : c = 0) (e : Fin c → ℤ) (z z' : Fin n → E) :
    nfLat P n c e z = nfLat P n c e z' := by
  subst hc
  simp [nfLat]

end General

theorem nf_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  intro X Pr R j P hP h ρ e z hρ hb hL
  obtain ⟨he, hz⟩ := read_bounds P j h ρ e z hρ hb.1 hb.2 hL
  rcases Nat.eq_zero_or_pos (cOf R j) with hc | hc
  · exact ⟨e, 0, he, zero_mem _, by rw [lamYat_coe hP, hL, nfLat_of_eq_zero P hc e z 0]⟩
  · exact ⟨e, z, he, (mem_stdAt_iff _).2 (hz hc), by rw [lamYat_coe hP, hL]⟩

end GlobalTheory.Proof.hasLatticeNormalForm_of_between

end
