import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTail
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem exists_nhds_one_tube {G : Type} [Group G] [TopologicalSpace G] {C : Set G} (hC : IsCompact C)
    {n : Set (G × G)} (hn : IsOpen n) (h : ∀ c ∈ C, (c, (1 : G)) ∈ n) :
    ∃ O ∈ 𝓝 (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n :=
  _root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h

theorem finite_image_of_rightInvariant {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {W : Type}
    (φ : P → W) (K' : Subgroup P) (hK' : IsOpen (K' : Set P)) (hinv : ∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p)
    {C : Set P} (hC : IsCompact C) : (φ '' C).Finite := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by
    have ho : IsOpen {p : P | c⁻¹ * p ∈ K'} := hK'.preimage (continuous_const.mul continuous_id)
    exact ho.mem_nhds (by simp [K'.one_mem]))
  refine (t.finite_toSet.image φ).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, hc, hcp⟩ := Set.mem_iUnion₂.1 (ht hp)
  refine ⟨c, hc, ?_⟩
  have := hinv c _ hcp
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem exists_openSubgroup_consistent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} :
    LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁),
    (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) →
    ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) →
    ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) →
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧
      ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  intro hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY
  have hfin : (φ '' C).Finite := finite_image_of_rightInvariant φ K' hK' hinv hC

  have hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v} := by
    have e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact hfin.isOpen_biInter fun v _ => hσ v
  obtain ⟨UQ, hUQ, hUQe⟩ := isOpen_induced_iff.1 hopenQ
  have h1UQ : (1 : G) ∈ UQ := by
    have : (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ := by
      rw [hUQe]
      intro v _
      simp
    exact this
  have hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c := by
    intro s hs c hc
    have : s ∈ (Subtype.val : Q → G) ⁻¹' UQ := hs
    rw [hUQe] at this
    exact this _ ⟨c, hc, rfl⟩

  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hK'
  have h1U : (1 : G) ∈ U := by
    have : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U := by
      rw [hUe]
      exact K'.one_mem
    exact this
  have hC' : IsCompact ((Subtype.val : P → G) '' C) := hC.image continuous_subtype_val
  obtain ⟨OP, hOP, hOPc⟩ := exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U})
    (hU.preimage (by fun_prop)) (by
      rintro _ ⟨c, -, rfl⟩
      simpa using h1U)
  obtain ⟨O, hO, hOs⟩ := hL UQ (hUQ.mem_nhds h1UQ) OP hOP
  obtain ⟨O₁, hO₁, hO₁c⟩ := exists_nhds_one_tube hC'
    (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y})
    ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using mem_interior_iff_mem_nhds.2 hO
      · simpa using hCY c hc)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O₁ hO₁
  have hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G),
      (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y := fun c hc κ hκ =>
    hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)
  refine ⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩
  intro c hc κ hκ q p' hq
  have huO : (c : G) * κ * (c : G)⁻¹ ∈ O := interior_subset (hVc c hc κ hκ).1

  have hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x := by
    refine ⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩
    calc x * ((c : G) * κ * (c : G)⁻¹) = (q : G)⁻¹ * ((q : G) * x * (c : G) * κ) * (c : G)⁻¹ := by group
      _ = (q : G)⁻¹ * x * ((p' : G) * (c : G)⁻¹) := by rw [hq]; group
  obtain ⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩ := hOs _ huO hmem

  have hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U := hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O
  have hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K' := by
    have : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U := hconj
    rw [hUe] at this
    exact this
  have hval : φ (⟨p₂, hp₂⟩ * c) = φ c := by
    have := hinv c _ hκ'
    rwa [show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group] at this
  have hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G) := by
    have : (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G) := by group
    show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)
    rw [this, ← he, ← hq]
    group
  have hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩ := rfl
  rw [hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]

end GlobalTheory.CompanionTheory.BZRes
