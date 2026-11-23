import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

open GlobalTheory.CompanionTheory.Ar.Crv

theorem exists_sum_tmul {O k : Type} [CommRing O] [Field k] (z : TensorProduct ℤ k O) :
    ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), z = ∑ j, c j ⊗ₜ[ℤ] a j := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul c a => exact ⟨1, fun _ => c, fun _ => a, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, c, a, rfl⟩ := hx
    obtain ⟨n, d, b, rfl⟩ := hy
    refine ⟨m + n, Fin.append c d, Fin.append a b, ?_⟩
    simp [Fin.sum_univ_add]

def splitMap {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) :
    TensorProduct ℤ k O →ₐ[k] (S → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _)

theorem splitMap_tmul {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) (c : k) (a : O)
    (t : S) : splitMap χ (c ⊗ₜ[ℤ] a) t = c * χ t a := by
  simp [splitMap, Algebra.ofId_apply]

def actMap {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →ₐ[ℤ] Module.End K V :=
  Algebra.TensorProduct.lift
    ((algebraMap K (Module.End K V)).comp (algebraMap k K)).toIntAlgHom ρ.toIntAlgHom
    (fun c a => show Commute (algebraMap K (Module.End K V) (algebraMap k K c)) (ρ a) from
      Algebra.commute_algebraMap_left _ _)

theorem actMap_tmul {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    actMap ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem smul_mem_of_isBun {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] {L : C.I → AddSubgroup V} (hL : IsBun C L) (i : C.I) {c : K}
    (hc : C.v i c ≤ 1) {x : V} (hx : x ∈ L i) : c • x ∈ L i := by
  obtain ⟨b, hb⟩ := hL.1 i
  refine (hb _).2 fun q => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc ((hb _).1 hx q)

theorem split_proj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k]
    [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ →
    (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L →
    (∀ a, IsHom C L L (ρ a)) →
    ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧
      (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧
      (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧
      (∀ x, ∑ s, e s x = x) ∧
      ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O),
        (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧
        e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  intro K _ C V _ _ _ L O k S _ _ _ _ _ χ hχ hk ρ hL hρ
  have hinj : Function.Injective (splitMap χ) := hχ.1
  have hsurj : Function.Surjective (splitMap χ) := hχ.2
  choose z hz using fun s : S => hsurj (Pi.single s 1)
  choose m c a hza using fun s : S => exists_sum_tmul (z s)
  have he : ∀ s, actMap (k := k) ρ (z s) = ∑ j, algebraMap k K (c s j) • ρ (a s j) := by
    intro s
    rw [hza s, map_sum]
    exact Finset.sum_congr rfl fun j _ => actMap_tmul ρ _ _
  have hcoef : ∀ s t, ∑ j, c s j * χ t (a s j) = if t = s then 1 else 0 := by
    intro s t
    have h := congrFun (hz s) t
    rw [hza s, map_sum, Finset.sum_apply] at h
    simp only [splitMap_tmul] at h
    rw [h, Pi.single_apply]
  have hmul : ∀ s b, ρ b * actMap (k := k) ρ (z s) =
      algebraMap k K (χ s b) • actMap (k := k) ρ (z s) := by
    intro s b
    have h : ((1 : k) ⊗ₜ[ℤ] b) * z s = (χ s b ⊗ₜ[ℤ] (1 : O)) * z s := by
      apply hinj
      rw [map_mul, map_mul, hz s]
      funext t
      simp only [Pi.mul_apply, splitMap_tmul, Pi.single_apply]
      by_cases hts : t = s
      · subst hts; simp
      · simp [hts]
    have h' := congrArg (actMap (k := k) ρ) h
    rw [map_mul, map_mul, actMap_tmul, actMap_tmul] at h'
    simpa using h'
  have hsum : ∑ s, actMap (k := k) ρ (z s) = 1 := by
    have h : ∑ s, z s = 1 := by
      apply hinj
      rw [map_sum, map_one]
      simp only [hz]
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← map_sum, h, map_one]
  refine ⟨fun s => actMap (k := k) ρ (z s), ?_, ?_, ?_, ?_, ?_⟩
  · intro s i x hx
    show actMap (k := k) ρ (z s) x ∈ L i
    rw [he s, LinearMap.sum_apply]
    exact sum_mem fun j _ => smul_mem_of_isBun C hL i (hk i _) (hρ _ i x hx)
  · intro s x
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker]
    intro b
    have h := congrArg (fun f : Module.End K V => f x) (hmul s b)
    simpa [sub_eq_zero] using h
  · intro s x hx
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ b, ρ b x = algebraMap k K (χ s b) • x := fun b => by
      simpa [sub_eq_zero] using hx b
    show actMap (k := k) ρ (z s) x = x
    rw [he s, LinearMap.sum_apply]
    have : ∀ j, (algebraMap k K (c s j) • ρ (a s j)) x =
        algebraMap k K (c s j * χ s (a s j)) • x := fun j => by
      rw [LinearMap.smul_apply, hx', smul_smul, map_mul]
    simp only [this]
    rw [← Finset.sum_smul, ← map_sum, hcoef s s]
    simp
  · intro x
    have h := congrArg (fun f : Module.End K V => f x) hsum
    simpa [LinearMap.sum_apply] using h
  · intro s
    exact ⟨m s, c s, a s, hcoef s, he s⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SplitProj
