import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.FinalF
import Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst
import Development.AutomorphicSpectrum.Proofs.JetProofs.GraphExtend

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.ExtHw

theorem inner_word_eq_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (hR : Formalism.REAL.GlRel D)
    (hA : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (Hs : Submodule ℂ H)
    (hs : ∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) {x y : H} (hx : x ∈ Hs) (hy : y ∈ Hs)
    (hxx : ⟪x, x⟫_ℂ = 1) (hyy : ⟪y, y⟫_ℂ = 1) (hxy : ⟪x, y⟫_ℂ = 0)
    (l : List (Fin n × Fin n)) : ⟪x, (l.map fun z => D z.1 z.2).prod y⟫_ℂ = 0 := by
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have vev : ∀ u ∈ Hs, ∀ v ∈ Hs,
      ⟪u, (l.map fun z => D z.1 z.2).prod u⟫_ℂ * ⟪v, v⟫_ℂ =
        ⟪v, (l.map fun z => D z.1 z.2).prod v⟫_ℂ * ⟪u, u⟫_ℂ := fun u hu v hv =>
    GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n (fun _ => true) H H D D μ u v (fun a b c d _ _ => hR a b c d)
      (fun a b c d _ _ => hR a b c d) (fun a b _ => hA a b) (fun a b _ => hA a b)
      (hs u hu) (hs v hv) l (fun _ _ => rfl)
  generalize (l.map fun z => D z.1 z.2).prod = W at vev ⊢
  have h1 := vev x hx y hy
  have h2 := vev (x + y) (Hs.add_mem hx hy) x hx
  have h3 := vev (x + Complex.I • y) (Hs.add_mem hx (Hs.smul_mem _ hy)) x hx
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hxx, hyy, hxy, hyx, Complex.conj_I] at h1 h2 h3
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h4 : ⟪x, W y⟫_ℂ + ⟪y, W x⟫_ℂ = 0 := by linear_combination h2 + h1
  have h5 : Complex.I * (⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ) = 0 := by
    linear_combination h3 + h1 + (⟪y, W y⟫_ℂ - ⟪x, W x⟫_ℂ) * hI
  have h6 : ⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ = 0 :=
    (mul_eq_zero.1 h5).resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * h4 + (1 / 2 : ℂ) * h6

theorem kmap_extend : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  intro n H V _ _ _ _ _ D D' μ hR hR' hA hA' Hs hs f hf
  let ξ := stdOrthonormalBasis ℂ Hs
  have hself : ∀ i, ⟪(ξ i : H), (ξ i : H)⟫_ℂ = 1 := fun i => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i i
    rw [if_pos rfl] at this
    exact this
  have hoff : ∀ i j, i ≠ j → ⟪(ξ i : H), (ξ j : H)⟫_ℂ = 0 := fun i j hij => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i j
    rw [if_neg hij] at this
    exact this
  have hne : ∀ i, (ξ i : H) ≠ 0 := fun i h0 => by
    have := hself i
    rw [h0, inner_zero_left] at this
    exact zero_ne_one this
  have hex : ∀ i, ∃ T : H →ₗ[ℂ] V, T (ξ i : H) = f (ξ i) ∧ GlobalTheory.CompanionTheory.AlgRepEndIrreducible.KMap (fun _ => true) D D' T :=
    fun i => GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.hwmap n (fun _ => true) H V D D' μ (ξ i : H) (f (ξ i))
      (fun a b c d _ _ => hR a b c d) (fun a b c d _ _ => hR' a b c d)
      (fun a b _ => hA a b) (fun a b _ => hA' a b) (hs _ (ξ i).2) (hf _) (hne i)
  choose Ti hTi hTK using hex
  let Z : _ → Submodule ℂ H := fun i => Submodule.span ℂ
    (Set.range fun l : List (Fin n × Fin n) => (l.map fun z => D z.1 z.2).prod (ξ i : H))
  have hst : ∀ i a b, ∀ z ∈ Z i, D a b z ∈ Z i := by
    intro i a b z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact Submodule.subset_span ⟨(a, b) :: l, by simp⟩
  have hperp : ∀ i a b, ∀ z ∈ (Z i)ᗮ, D a b z ∈ (Z i)ᗮ := by
    intro i a b z hz
    rw [Submodule.mem_orthogonal] at hz ⊢
    intro u hu
    rw [← hA b a]
    exact hz _ (hst i b a u hu)
  have hcomm : ∀ i a b w, (Z i).starProjection (D a b w) = D a b ((Z i).starProjection w) := by
    intro i a b w
    obtain ⟨u, hu, z, hz, rfl⟩ := (Z i).exists_add_mem_mem_orthogonal w
    have e1 : (Z i).starProjection u = u := Submodule.starProjection_eq_self_iff.2 hu
    have e2 : (Z i).starProjection z = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2 hz
    have e3 : (Z i).starProjection (D a b u) = D a b u :=
      Submodule.starProjection_eq_self_iff.2 (hst i a b u hu)
    have e4 : (Z i).starProjection (D a b z) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).2 (hperp i a b z hz)
    rw [map_add, map_add, map_add, e1, e2, e3, e4, add_zero, add_zero]
  have hdiag : ∀ i, (Z i).starProjection (ξ i : H) = ξ i := fun i =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span ⟨[], by simp⟩)
  have hzero : ∀ i j, i ≠ j → (Z i).starProjection (ξ j : H) = 0 := by
    intro i j hij
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.word_adj (ε := fun _ => true) (fun a b _ => hA a b) l (fun _ _ => rfl)]
      exact inner_word_eq_zero D μ hR hA Hs hs (ξ i).2 (ξ j).2 (hself i) (hself j) (hoff i j hij) _
  let T : H →ₗ[ℂ] V := ∑ i, (Ti i).comp ((Z i).starProjection : H →L[ℂ] H).toLinearMap
  have hTapp : ∀ w, T w = ∑ i, Ti i ((Z i).starProjection w) := fun w => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, ?_, ?_⟩
  · have hb : T.comp Hs.subtype = f := by
      refine ξ.toBasis.ext fun j => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply, hTapp,
        Finset.sum_eq_single j]
      · rw [hdiag, hTi]
      · intro i _ hij
        rw [hzero i j hij, map_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    intro x
    exact LinearMap.congr_fun hb x
  · intro a b w
    rw [hTapp, hTapp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, hTK i a b rfl]

end GlobalTheory.CompanionTheory.RealCount.ExtHw
