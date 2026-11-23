import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

section Field

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem eigSp_apply {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (hx : x ∈ eigSp ρ σ) (a : O) :
    ρ a x = σ a • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

theorem iSup_eigSp_stable (ρ : O →+* Module.End k V) (T : Set (O →+* k)) (a : O) {x : V}
    (hx : x ∈ ⨆ τ ∈ T, eigSp ρ τ) : ρ a x ∈ ⨆ τ ∈ T, eigSp ρ τ := by
  have hle : (⨆ τ ∈ T, eigSp ρ τ) ≤ (⨆ τ ∈ T, eigSp ρ τ).comap (ρ a) := by
    refine iSup₂_le fun τ hτ y hy => ?_
    rw [Submodule.mem_comap, eigSp_apply hy a]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hτ hy))
  exact hle hx

theorem eq_zero_of_mem_finset (ρ : O →+* Module.End k V) (σ : O →+* k)
    (t : Finset {τ : O →+* k // τ ≠ σ}) :
    ∀ x ∈ eigSp ρ σ, x ∈ (⨆ i ∈ t, eigSp ρ i.1) → x = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro x _ h
    simpa using h
  | insert τ t _ ih =>
    intro x hx hxs
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, hyz⟩ := hxs
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ τ.1 a := by
      by_contra h
      push_neg at h
      exact τ.2 (RingHom.ext fun a => (h a).symm)
    have hzs : ∀ b : O, ρ b z ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      intro b
      have hle : (⨆ i ∈ t, eigSp ρ i.1) ≤ (⨆ i ∈ t, eigSp ρ i.1).comap (ρ b) := by
        refine iSup₂_le fun i hi u hu => ?_
        rw [Submodule.mem_comap, eigSp_apply hu b]
        exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hu))
      exact hle hz
    have hkey : (σ a - τ.1 a) • x = ρ a z - τ.1 a • z := by
      have e1 := eigSp_apply hx a
      have e2 := eigSp_apply hy a
      rw [← hyz, map_add, e2] at e1
      have e3 : ρ a z = σ a • (y + z) - τ.1 a • y := by rw [← e1]; abel
      rw [e3, ← hyz, sub_smul]
      simp only [smul_add]
      abel
    have hmem : (σ a - τ.1 a) • x ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      rw [hkey]
      exact Submodule.sub_mem _ (hzs a) (Submodule.smul_mem _ _ hz)
    have h0 := ih _ (Submodule.smul_mem _ _ hx) hmem
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 ha)

theorem eq_zero_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {x : V} (hx : x ∈ eigSp ρ σ)
    (hS : x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) : x = 0 := by
  have h : (⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) = ⨆ i : {τ : O →+* k // τ ≠ σ}, eigSp ρ i.1 := by
    rw [iSup_subtype']
    rfl
  rw [h, Submodule.mem_iSup_iff_exists_finset] at hS
  obtain ⟨t, ht⟩ := hS
  exact eq_zero_of_mem_finset ρ σ t x hx ht

theorem eigComp_spec {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (h0 : eigComp ρ σ x ≠ 0) :
    eigComp ρ σ x ∈ eigSp ρ σ ∧ x - eigComp ρ σ x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ := by
  by_cases h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ'
  · have e : eigComp ρ σ x = h.choose := by
      unfold eigComp
      rw [dif_pos h]
    rw [e]
    exact h.choose_spec
  · exact absurd (by unfold eigComp; rw [dif_neg h]) h0

end Field

section Main

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem linearIndependent_f (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ)
    (hO : IsOFamily A.ρ A.I v) (hA : A.IsAdapted s v q) (hq : ∀ i, (q i : V) ∈ A.eig s) :
    LinearIndependent (𝓞 L) fun c => A.f (q c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  set S : Submodule L V := ⨆ τ ∈ {τ : 𝓞 E →+* L | τ ≠ A.σ s}, eigSp A.ρ τ with hSdef
  set p : Fin r → V := fun i => eigComp A.ρ (A.σ s) (v i) with hpdef
  have hfam_l : ∀ i : Fin r, A.fam s v q (Fin.castAdd k i) = p i := by
    intro i
    simp [LinPt.fam, hpdef]
  have hfam_r : ∀ c : Fin k, A.fam s v q (Fin.natAdd r c) = (q c : V) := by
    intro c
    simp [LinPt.fam]
  have hp : ∀ i, p i ∈ eigSp A.ρ (A.σ s) ∧ v i - p i ∈ S := by
    intro i
    refine eigComp_spec ?_
    have := hA.1.ne_zero (Fin.castAdd k i)
    rwa [hfam_l] at this
  set M : Submodule L V := Submodule.span L (Set.range p) ⊔ S with hMdef
  have hT : ∀ (a : 𝓞 E) (i : Fin r), A.ρ a (v i) ∈ M := by
    intro a i
    have e : A.ρ a (v i) = A.σ s a • p i + A.ρ a (v i - p i) := by
      rw [map_sub, eigSp_apply (hp i).1 a]
      abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · exact Submodule.mem_sup_right (iSup_eigSp_stable A.ρ _ a (hp i).2)
  have hoS : oSpan A.ρ v ≤ M.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, i, rfl⟩
    exact hT a i
  have hI : ∀ x ∈ A.I, x ∈ M := by
    intro x hx
    obtain ⟨n, hn, -, hnx⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hO.2.2 hx
    have h1 : n • x ∈ M := hoS hnx.1
    have hn0 : (n : L) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have h2 : x = (n : L)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  set w : A.Λ := ∑ c, g c • q c with hw
  have hwV : (w : V) = ∑ c, g c • (q c : V) := by
    simp [hw]
  have hfw : A.f w = 0 := by
    simpa [hw, map_sum] using hg
  have hwI : (w : V) ∈ Submodule.span (𝓞 L) (A.I : Set V) := (A.ker w).1 hfw
  have hwe : (w : V) ∈ eigSp A.ρ (A.σ s) := by
    have : (w : V) ∈ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L) := by
      rw [hwV]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c).2
    exact this
  have hwM : (w : V) ∈ M := by
    have hle : Submodule.span (𝓞 L) (A.I : Set V) ≤ M.restrictScalars (𝓞 L) :=
      Submodule.span_le.2 fun x hx => hI x hx
    exact hle hwI
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 hwM
  have hue : u ∈ eigSp A.ρ (A.σ s) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨i, rfl⟩
    exact (hp i).1
  have ht0 : t = 0 := by
    refine eq_zero_of_mem_iSup A.ρ (A.σ s) ?_ ht
    have : t = (w : V) - u := by rw [← hut]; abel
    rw [this]
    exact Submodule.sub_mem _ hwe hue
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hu
  have hzero : ∑ j, (Fin.append (fun i => - b i) (fun c => algebraMap (𝓞 L) L (g c)) j) • A.fam s v q j = 0 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hfam_l, hfam_r, neg_smul, algebraMap_smul,
      Finset.sum_neg_distrib]
    rw [hb, ← hwV, ← hut, ht0]
    simp
  have := Fintype.linearIndependent_iff.1 hA.1 _ hzero (Fin.natAdd r c)
  rw [Fin.append_right] at this
  exact RingOfIntegers.coe_injective (by simpa using this)

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open scoped ComplexOrder in

theorem gramDet_pos_of_adapted : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type)
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ)
    (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) →
    ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  intro E L Ψ _ _ _ _ V _ _ _ _ A s r k v q hO hA hq e
  have hli := Adapted.linearIndependent_f A s v q hO hA hq
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec A.Bq.metric e (A.f (q i))) =
      Matrix.of fun i j ↦ (A.Bq.metric.form e).inner
        ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q i)) ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q j)) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec A.Bq.metric e hli)).det_pos
  rw [hG] at hp
  exact (Complex.lt_def.1 hp).1

end GlobalTheory.CompanionTheory.Ar.Cusp
