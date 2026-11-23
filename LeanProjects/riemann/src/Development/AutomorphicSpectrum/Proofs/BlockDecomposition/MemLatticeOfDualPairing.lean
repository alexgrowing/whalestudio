import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_extend {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K))
    (hs : Submodule.span K (L : Set (Fin m → K)) = ⊤) (φ : L →ₗ[𝓞 K] 𝓞 K) :
    ∃ G : (Fin m → K) →ₗ[K] K, ∀ x : L, G x = algebraMap (𝓞 K) K (φ x) := by
  classical
  have hs' : ⊤ ≤ Submodule.span K (L : Set (Fin m → K)) := hs.ge
  obtain ⟨ι, b, hb⟩ : ∃ (ι : Type) (b : Module.Basis ι K (Fin m → K)), ∀ i, b i ∈ L :=
    ⟨_, Module.Basis.ofSpan hs', fun i => Module.Basis.ofSpan_subset hs' ⟨i, rfl⟩⟩
  haveI := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  let G : (Fin m → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩))
  have hGb : ∀ i, G (b i) = algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩) := fun i => b.constr_basis _ _ _
  refine ⟨G, fun x => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun i => b.repr (x : Fin m → K) i) (S := K)
  choose e he using hd
  have hx : ((d : 𝓞 K) • (x : Fin m → K)) = ∑ i, e i • b i := by
    conv_lhs => rw [← b.sum_repr (x : Fin m → K)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), he i, smul_assoc]
  have hxL : (d : 𝓞 K) • x = ∑ i, e i • (⟨b i, hb i⟩ : L) := by
    apply Subtype.ext
    simpa using hx
  have h1 : (d : 𝓞 K) * φ x = ∑ i, e i * φ ⟨b i, hb i⟩ := by
    have h := congrArg φ hxL
    rw [map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h2 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = algebraMap (𝓞 K) K ((d : 𝓞 K) * φ x) := by
    have h3 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = G ((d : 𝓞 K) • (x : Fin m → K)) := by
      rw [← algebraMap_smul K (d : 𝓞 K) (x : Fin m → K), map_smul, smul_eq_mul]
    rw [h3, hx, h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), map_smul, hGb, smul_eq_mul, map_mul]
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero d.2
    simpa using this
  rw [map_mul] at h2
  exact mul_left_cancel₀ hd0 h2

theorem mem_of_dot_integral : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K,
    (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  intro K _ _ m L hL v hv
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (𝓞 K) L := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let φ : Fin n → L →ₗ[𝓞 K] 𝓞 K := fun i => (LinearMap.proj i).comp s
  let l : Fin n → L := fun i => f (fun j => if i = j then 1 else 0)
  have hdual : ∀ x : L, x = ∑ i, φ i x • l i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    have h2 := LinearMap.pi_apply_eq_sum_univ f (s x)
    rw [h1] at h2
    exact h2
  choose G hG using fun i => exists_extend L hspan (φ i)
  let a : Fin n → Fin m → K := fun i j => G i (fun k => if j = k then 1 else 0)
  have ha : ∀ i w, a i ⬝ᵥ w = G i w := by
    intro i w
    rw [LinearMap.pi_apply_eq_sum_univ (G i) w]
    simp [dotProduct, a, mul_comm]
  have hid : ∀ w : Fin m → K, w = ∑ i, G i w • (l i : Fin m → K) := by
    let T : (Fin m → K) →ₗ[K] (Fin m → K) := ∑ i, (G i).smulRight (l i : Fin m → K)
    have hT : T = LinearMap.id := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      have h1 := congrArg (Subtype.val) (hdual ⟨x, hx⟩)
      simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have h2 : ∀ i, G i x • (l i : Fin m → K) = φ i ⟨x, hx⟩ • (l i : Fin m → K) := by
        intro i
        rw [show G i x = algebraMap (𝓞 K) K (φ i ⟨x, hx⟩) from hG i ⟨x, hx⟩, algebraMap_smul]
      simp only [h2]
      simpa using h1.symm
    intro w
    have h := LinearMap.congr_fun hT w
    simpa [T, LinearMap.sum_apply] using h.symm
  have hint : ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = a i ⬝ᵥ v := by
    intro i
    have h := hv (a i) (fun x hx => by
      rw [(ha i x).trans (hG i ⟨x, hx⟩)]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩)
    exact Submodule.mem_one.mp h
  choose o ho using hint
  rw [hid v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h3 : G i v • (l i : Fin m → K) = o i • (l i : Fin m → K) := by
    rw [← ha, ← ho, algebraMap_smul]
  rw [h3]
  exact L.smul_mem _ (l i).2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt
