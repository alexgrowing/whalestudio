import Mathlib
import GroundTheory.AutomorphicForms.ReductionMahler
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Set Matrix
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Orbit

variable {𝒢 W : Type*} [Group 𝒢]

theorem exists_finset_of_orbit (Φ : 𝒢 → W) (G Γ : Subgroup 𝒢)
    (hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ G) (C : Set 𝒢)
    (hfin : (Φ '' C ∩ Φ '' (Γ : Set 𝒢)).Finite) :
    ∃ T : Finset 𝒢, (∀ δ ∈ T, δ ∈ Γ) ∧ ∀ g ∈ G, ∀ γ ∈ Γ, ∀ c ∈ C, g = γ * c →
      ∃ δ ∈ T, γ * δ ∈ G ∧ δ⁻¹ * c ∈ G := by
  classical
  have hch : ∀ s ∈ hfin.toFinset, ∃ δ ∈ Γ, Φ δ = s := fun s hs => by
    obtain ⟨-, δ, hδ, rfl⟩ := hfin.mem_toFinset.1 hs
    exact ⟨δ, hδ, rfl⟩
  choose! f hfΓ hfΦ using hch
  refine ⟨hfin.toFinset.image f, fun δ hδ => ?_, fun g hg γ hγ c hc hgc => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hδ
    exact hfΓ s hs
  · have h1 : Φ γ⁻¹ = Φ c := (hΦ _ _).2 (by rw [inv_inv, ← hgc]; exact hg)
    have hs : Φ c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨⟨c, hc, rfl⟩, γ⁻¹, inv_mem hγ, h1⟩
    refine ⟨f (Φ c), Finset.mem_image_of_mem _ hs, ?_, (hΦ _ _).1 (hfΦ _ hs)⟩
    have := (hΦ γ⁻¹ (f (Φ c))).1 (by rw [hfΦ _ hs, h1])
    rwa [inv_inv] at this

theorem conj_eq_conj_iff {R : Type*} [Ring R] (g g' : Rˣ) (x : R) :
    (g : R) * x * ↑g⁻¹ = g' * x * ↑g'⁻¹ ↔ ((g⁻¹ * g' : Rˣ) : R) * x = x * ((g⁻¹ * g' : Rˣ) : R) := by
  rw [Units.val_mul]
  have e1 : (↑g⁻¹ * ↑g' * x : R) = ↑g⁻¹ * (↑g' * x * ↑g'⁻¹) * ↑g' := by
    simp [mul_assoc]
  have e2 : (x * (↑g⁻¹ * ↑g') : R) = ↑g⁻¹ * (↑g * x * ↑g⁻¹) * ↑g' := by
    simp [mul_assoc]
  constructor
  · intro h
    rw [e1, e2, h]
  · intro h
    have e3 : (↑g' * x * ↑g'⁻¹ : R) = ↑g * (↑g⁻¹ * ↑g' * x) * ↑g'⁻¹ := by
      simp [mul_assoc]
    have e4 : (↑g * x * ↑g⁻¹ : R) = ↑g * (x * (↑g⁻¹ * ↑g')) * ↑g'⁻¹ := by
      simp [mul_assoc]
    rw [e3, e4, h]

end Orbit

variable {K : Type*} [Field K] [NumberField K]

theorem finite_algebraMap_preimage {X : Set 𝔸[K]} (hX : IsCompact X) :
    (algebraMap K 𝔸[K] ⁻¹' X).Finite := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hc := GroundTheory.Global.isClosed_principalSubgroup K
  set P : Set 𝔸[K] := (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) with hP
  have hXP : IsCompact (X ∩ P) := hX.inter_right hc
  have hdP : DiscreteTopology P := hd
  have hdisc : DiscreteTopology (X ∩ P : Set 𝔸[K]) :=
    DiscreteTopology.of_subset hdP Set.inter_subset_right
  have hfin : (X ∩ P).Finite := hXP.finite ⟨hdisc⟩
  refine (hfin.preimage (AdeleRing.algebraMap_injective (𝓞 K) K).injOn).subset ?_
  intro k hk
  exact ⟨hk, k, rfl⟩

theorem finite_of_isCompact_coords {α Y J : Type*} [Finite J] [TopologicalSpace Y] {X : Set Y}
    (hX : IsCompact X) (ψ : α → Y) (π : J → Y → 𝔸[K]) (hπ : ∀ j, Continuous (π j))
    (φ : α → J → K) (hφ : Function.Injective φ)
    (hψ : ∀ a j, π j (ψ a) = algebraMap K 𝔸[K] (φ a j)) : {a | ψ a ∈ X}.Finite := by
  have h : (Set.univ.pi fun j => algebraMap K 𝔸[K] ⁻¹' (π j '' X)).Finite :=
    Set.Finite.pi fun j => finite_algebraMap_preimage (hX.image (hπ j))
  refine Set.Finite.of_finite_image (h.subset ?_) hφ.injOn
  rintro _ ⟨a, ha, rfl⟩ j -
  exact ⟨ψ a, ha, hψ a j⟩

variable {n : ℕ} {m : Type*}

def adelicCentralizer (L : m → Matrix (Fin n) (Fin n) K) : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {g | ∀ k, (g : Matrix (Fin n) (Fin n) 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
    (L k).map (algebraMap K 𝔸[K]) * g}
  one_mem' k := by simp
  mul_mem' {a b} ha hb k := by
    show ((a * b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * _ = _ * _
    rw [Units.val_mul, Matrix.mul_assoc, hb k, ← Matrix.mul_assoc, ha k, Matrix.mul_assoc]
  inv_mem' {a} ha k := by
    have h := ha k
    set M := (L k).map (algebraMap K 𝔸[K])
    show ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M =
      M * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
    calc ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M
        = ↑a⁻¹ * (M * ↑a) * ↑a⁻¹ := by simp [mul_assoc]
      _ = ↑a⁻¹ * (↑a * M) * ↑a⁻¹ := by rw [h]
      _ = M * ↑a⁻¹ := by simp

theorem diagonal_mem_adelicCentralizer_iff {L : m → Matrix (Fin n) (Fin n) K}
    {γ : GL (Fin n) K} :
    AdelicGLn.diagonal K n γ ∈ adelicCentralizer L ↔
      ∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ := by
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) K => M.map (algebraMap K 𝔸[K]) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 K) K)
  refine forall_congr' fun k => ?_
  show (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
      (L k).map (algebraMap K 𝔸[K]) * (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) ↔ _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact hinj.eq_iff

theorem exists_isCompact_centralizer_reduction [Finite m] (L : m → Matrix (Fin n) (Fin n) K)
    (G : Subgroup (AdelicGLn.AdelicGL K n)) (hG1 : G ≤ Reduction.normOneGL K n)
    (hGL : G ≤ adelicCentralizer L) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G, ∀ x : Fin n → K, x ≠ 0 → ε ≤ Reduction.height g x) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ G, ∃ γ : GL (Fin n) K,
      (∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ) ∧
        (AdelicGLn.diagonal K n γ)⁻¹ * g ∈ C := by
  classical
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
  let Lm : m → Matrix (Fin n) (Fin n) 𝔸[K] := fun k => (L k).map (algebraMap K 𝔸[K])
  let Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k *
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L := by
    intro g g'
    rw [funext_iff]
    exact forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)
  have hΦc : Continuous Φ := continuous_pi fun k =>
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)
  let ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun r k => (r k).map (algebraMap K 𝔸[K])
  have hψfin : {r | ψ r ∈ Φ '' C}.Finite := by
    refine finite_of_isCompact_coords (hC.image hΦc) ψ
      (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2)
      (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2)
      (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)
    intro r r' h
    funext k i j
    exact congrFun h (k, i, j)
  have hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite := by
    refine (hψfin.image ψ).subset ?_
    rintro _ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩
    have e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k *
        ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      funext k
      simp only [ψ, Φ, Lm, ← map_inv]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e] at hC1 ⊢
    exact ⟨_, hC1, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n)
    hΦ C hfin
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro g hg
  obtain ⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩ := hC' g (hG1 hg) (hh g hg)
  obtain ⟨δ, hδT, hγδ, hδc⟩ := hT g (hGL hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm
  obtain ⟨δ₀, rfl⟩ := hTΓ δ hδT
  refine ⟨γ₀ * δ₀, ?_, ?_⟩
  · rw [← diagonal_mem_adelicCentralizer_iff, map_mul]
    exact hγδ
  · refine Set.mem_biUnion hδT ⟨c, hc, ?_⟩
    rw [map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end Anisotropic

end

end GroundTheory.Automorphic
