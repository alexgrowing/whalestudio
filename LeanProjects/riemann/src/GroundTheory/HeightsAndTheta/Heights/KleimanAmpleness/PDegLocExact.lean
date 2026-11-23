import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegLocExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

namespace DegLocExact

theorem decompose_map {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [h0]
  | @homogeneous i m =>
    obtain ⟨m, hm⟩ := m
    by_cases hik : i = k
    · subst hik
      rw [DirectSum.decompose_of_mem_same (ℳ := 𝒜) hm,
        DirectSum.decompose_of_mem_same (ℳ := ℬ) (hφ _ _ hm)]
    · rw [DirectSum.decompose_of_mem_ne (ℳ := 𝒜) hm hik,
        DirectSum.decompose_of_mem_ne (ℳ := ℬ) (hφ _ _ hm) hik, h0]
  | add m m' hm hm' => simp [hadd, DirectSum.decompose_add, hm, hm']

theorem mem_of_map_mem {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by
  have h := decompose_map 𝒜 ℬ φ h0 hadd hφ a k
  rw [DirectSum.decompose_of_mem_same (ℳ := ℬ) ha] at h
  rw [← hinj h]
  exact SetLike.coe_mem _

variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem exists_frac (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) (z : LocMod S N M I.1)
    (hz : z ∈ degLoc 𝓜 c I) :
    ∃ (m : M) (s : monos (S := S) I.1) (e : ℕ), (s : Poly S N).IsHomogeneous e ∧
      m ∈ 𝓜.piece (c + e) ∧ z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, s, a, e, hm, hs, hae, rfl⟩ := hz
    exact ⟨m, s, e, hs, by rwa [← hae, sub_add_cancel], rfl⟩
  | zero => exact ⟨0, 1, 0, isHomogeneous_one _ _, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, s1, e1, hs1, hm1, rfl⟩ := hx
    obtain ⟨m2, s2, e2, hs2, hm2, rfl⟩ := hy
    refine ⟨(s2 : Poly S N) • m1 + (s1 : Poly S N) • m2, s1 * s2, e1 + e2,
      by simpa using hs1.mul hs2, add_mem ?_ ?_, LocalizedModule.mk_add_mk⟩
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e1 + e2 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e2 _ _ m1 hs2 hm1
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e2 + e1 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e1 _ _ m2 hs1 hm2
  | smul r x _ hx =>
    obtain ⟨m, s, e, hs, hm, rfl⟩ := hx
    refine ⟨r • m, s, e, hs, Submodule.smul_mem _ r hm, ?_⟩
    change algebraMap S (Poly S N) r • (LocalizedModule.mk m s : LocalizedModule _ M) = _
    rw [LocalizedModule.smul'_mk, algebraMap_smul]

theorem proof : DegLocExact.Statement := by
  intro S _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c I
  let _ := 𝓜'.isInternal.chooseDecomposition
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := 𝓜''.isInternal.chooseDecomposition
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_⟩
  · obtain ⟨m, s, e, hs, hm, rfl⟩ := exists_frac 𝓜 c I z hz
    rw [locMap_mk] at hz0
    have h0 : (LocalizedModule.mk (g.toLin m) s : LocalizedModule (monos (S := S) I.1) M'') =
        LocalizedModule.mk 0 s := by rw [LocalizedModule.zero_mk]; exact hz0
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h0
    set T : monos (S := S) I.1 := u * s with hT
    obtain ⟨e', he'⟩ := monos_isHomogeneous T.2
    have hgT : g.toLin ((T : Poly S N) • m) = 0 := by
      rw [map_smul, hT, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def,
        hu, smul_zero, smul_zero]
    obtain ⟨m', hm'⟩ := (hfg _).1 hgT
    have hTm : (T : Poly S N) • m ∈ 𝓜.piece (c + e + e') := 𝓜.smul_mem e' _ _ m he' hm
    have hm'd : m' ∈ 𝓜'.piece (c + e + e') :=
      mem_of_map_mem 𝓜'.piece 𝓜.piece f.toLin (map_zero _) (map_add _) f.map_piece hf (hm' ▸ hTm)
    refine ⟨LocalizedModule.mk m' (T * s), Submodule.subset_span
      ⟨m', T * s, c + e + e', e' + e, hm'd, by simpa using he'.mul hs, by push_cast; ring, rfl⟩, ?_⟩
    rw [locMap_mk, hm', ← Submonoid.smul_def, LocalizedModule.mk_cancel_common_left]
  · obtain ⟨m'', s, e, hs, hm'', rfl⟩ := exists_frac 𝓜'' c I z hz
    obtain ⟨m, rfl⟩ := hg m''
    refine ⟨LocalizedModule.mk (DirectSum.decompose 𝓜.piece m (c + e) : M) s, Submodule.subset_span
      ⟨_, s, c + e, e, SetLike.coe_mem _, hs, by ring, rfl⟩, ?_⟩
    rw [locMap_mk, decompose_map 𝓜.piece 𝓜''.piece g.toLin (map_zero _) (map_add _) g.map_piece,
      DirectSum.decompose_of_mem_same (ℳ := 𝓜''.piece) hm'']

end DegLocExact

end

end GroundTheory.Heights₂.Heights.Kleiman
