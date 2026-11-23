import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntInvOfLoc

noncomputable section

open NumberField Ideal Matrix IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

def AwayLat0 (T : Forms0 D u) : Prop :=
  ∀ (v v' : (D.mem u).A.vT), v' ≠ v → ∀ (c c' : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
    (∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') η.1 = 1) →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c').1 = (T.cls0.y c).1 * η.1 * κ.1 →
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v') (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c')) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v') (Ld D u 0 (Nat.zero_le _) c)

theorem unif (A : AtTTied u) (v : (D.mem u).A.vT) (p : 𝓞 D.host.E) (hp : p ∈ A.Pv v) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∃ t : 𝓞 D.host.E, p * s = ((D.mem u).A.T : 𝓞 D.host.E) * t := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  have hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s := by
    intro s; rw [map_natCast]; exact CharP.cast_eq_zero_iff _ (D.mem u).A.T s
  have := span_isPrime (D.mem u).A.T
  have hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)}) := by
    refine ⟨?_⟩
    have hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0
      rw [map_natCast]
      exact (hres_nat _).2 dvd_rfl
    have hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal := by
      refine this.isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (D.mem u).A.T_prime.ne_zero
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle
  have hN := T_ne A v
  obtain ⟨I, hI, hIP⟩ := map_eq_mul_coprime D.host (D.mem u).A.T hN (A.Pv v)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hps : p * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E)) := by
    rw [hI]; exact Ideal.mul_mem_mul hp hsI
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at hps
  obtain ⟨z, hz⟩ := hps
  exact ⟨s, hsP, z, by rw [← hz, mul_comm]⟩

theorem up_smul_mem (A : AtTTied u) (v : (D.mem u).A.vT) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E))
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ L) (p : 𝓞 D.host.E) (hp : p ∈ A.Pv v) (x : Fin (D.R.N 0) → D.host.E)
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (L ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z})) :
    p • x ∈ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) L := by

  change ∃ s ∈ (A.Pv v).primeCompl, s • x ∈
    (L ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) at hx
  show ∃ s ∈ (A.Pv v).primeCompl, s • (p • x) ∈ L
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.mp hsx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s', hs', t, hpt⟩ := unif A v p hp
  refine ⟨s' * s, (A.Pv v).primeCompl.mul_mem hs' hs, ?_⟩
  have e : (s' * s) • (p • x) = (s' * p) • (s • x) := by
    rw [smul_smul, smul_smul, mul_right_comm]
  rw [e, ← hly, smul_add]
  refine L.add_mem (L.smul_mem _ hl) ?_
  by_cases hT0 : (((D.mem u).A.T : ℕ) : D.host.E) = 0
  · rw [hT0, _root_.inv_zero, zero_smul, smul_zero, smul_zero]
    exact L.zero_mem
  · have hc : algebraMap (𝓞 D.host.E) D.host.E (s' * p) =
        (((D.mem u).A.T : ℕ) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E t := by
      rw [mul_comm s' p, hpt, map_mul, map_natCast]
    have key : (s' * p) • (a • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z)) = (a * t) • z := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      rw [hc, map_mul]
      have hTT : (((D.mem u).A.T : ℕ) : D.host.E) * (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ = 1 :=
        mul_inv_cancel₀ hT0
      linear_combination (algebraMap (𝓞 D.host.E) D.host.E a * algebraMap (𝓞 D.host.E) D.host.E t * z i) * hTT
    rw [key]
    exact L.smul_mem _ hz

theorem upLatLoc0_of (T : Forms0 D u) (hA : AwayLat0 T) : UpLatLoc0 T := by
  intro w hw hs v c z hz γ η κ h1 h2 h3 h4 B B₂ B' hB hB₂ hB' τ
  by_cases hτ : τ = (D.fm u).tauOf w v
  · subst hτ
    rw [if_pos rfl]
    refine intInv_of_loc T.atT w hw hs v B' B γ.1 hB' hB ?_ ?_
    · calc Ld D u 0 (Nat.zero_le _) c ≤ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) := le_locP' (T.atT.Pv v) _
        _ = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v)
            (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) := h3.symm
        _ ≤ _ := localization_mono' _ (Submodule.map_mono le_sup_left)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_add]
      refine add_mem ?_ ?_
      · have hm : γ.1.1 *ᵥ y1 ∈ mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z))) :=
          Submodule.mem_map_of_mem hy1
        rw [← h3]
        exact le_locP' (T.atT.Pv v) _ hm
      · refine Submodule.smul_induction_on (p := fun y => γ.1.1 *ᵥ y ∈
            Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c)) hy2 (fun p hp l hl => ?_) (fun a b ha hb => ?_)
        · have hm : γ.1.1 *ᵥ l ∈ mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z))) :=
            Submodule.mem_map_of_mem hl
          have hm' := le_locP' (T.atT.Pv v) _ hm
          rw [h4] at hm'
          have e : γ.1.1 *ᵥ (p • l) = p • (γ.1.1 *ᵥ l) := by
            rw [← algebraMap_smul D.host.E p l, Matrix.mulVec_smul, algebraMap_smul]
          rw [e]
          exact up_smul_mem T.atT v _ z.1 z.2 p hp _ hm'
        · simp only [Matrix.mulVec_add]
          exact add_mem ha hb
  · obtain ⟨v', rfl⟩ := ((D.fm u).tauOf w).surjective τ
    have hvv : v' ≠ v := fun h => hτ (by rw [h])
    rw [if_neg hτ]
    have hE := hA v v' hvv c ((D.fm u).up 0 v c (T.lv0.pr v c z)) γ η κ h1 h2
    refine intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_
    · rw [hE]; exact le_locP' (T.atT.Pv v') _
    · rw [← hE]; exact le_locP' (T.atT.Pv v') _

end PI.UnitaryGroupMassFormula.IAT

end
