import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul

noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {U : Subgroup G} {v : V} : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro hv u hu
    have := hv ⟨u, hu⟩
    simpa using this
  · intro hv u
    simpa using hv u u.2

theorem actP_eq_sum (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) :
    ∃ (S : Subgroup (GLw a w × GLw b w)) (s : Finset ((GLw a w × GLw b w) ⧸ S)),
      S ≤ U ∧ S ≤ K2 a b w ∧ S.relIndex (K2 a b w) ≠ 0 ∧ (∀ q, q ∉ s → u q.out = 0) ∧
      actP w u G = ((S.relIndex (K2 a b w) : ℕ) : ℂ)⁻¹ • ∑ q ∈ s, u q.out • pairRt a b w q.out G := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w
  set S : Subgroup (GLw a w × GLw b w) := K2 a b w ⊓ U with hSdef
  have hSo : IsOpen (S : Set (GLw a w × GLw b w)) := hKo.inter hUo
  have hidx : S.relIndex (K2 a b w) ≠ 0 :=
    GlobalTheory.FunObj.relIndex_inf_ne_zero (N := K2 a b w) (O := U) (C := K2 a b w) hUo hKc le_rfl le_rfl
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets S hSo u hu
  set s := hfin.toFinset with hsdef
  have hs : ∀ q, q ∉ s → u q.out = 0 := fun q hq => by
    by_contra h0
    exact hq (hfin.mem_toFinset.2 h0)
  have hGf := (mem_fixed_iff'.1 hG)
  refine ⟨S, s, inf_le_right, inf_le_left, hidx, hs, ?_⟩
  funext z
  have hr : S ≤ rStab (fun m => u m * pairRt a b w m G z) := by
    intro k hk g
    show u (g * k) * pairRt a b w (g * k) G z = u g * pairRt a b w g G z
    rw [hur g k (Subgroup.mem_inf.1 hk).2, map_mul, Module.End.mul_apply, hGf k (Subgroup.mem_inf.1 hk).2]
  rw [actP, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ inf_le_left hr hidx]
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem lw_actP (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GLw a w × GLw b w) Y) (Λ : (H E a b → ℂ) →ₗ[ℂ] Y)
    (hΛ : ∀ g, Λ (pairRt a b w g G) = τ g (Λ G)) (lw : Y →ₗ[ℂ] ℂ) :
    lw (Λ (actP w u G)) = hint (K2 a b w) (fun m => u m * lw (τ m (Λ G))) := by
  obtain ⟨S, s, hSU, hSK, hidx, hs, hEq⟩ := actP_eq_sum w U hUo G hG u hu hur
  have hGf := (mem_fixed_iff'.1 hG)
  have hr : S ≤ rStab (fun m => u m * lw (τ m (Λ G))) := by
    intro k hk g
    show u (g * k) * lw (τ (g * k) (Λ G)) = u g * lw (τ g (Λ G))
    rw [hur g k (hSU hk), map_mul, Module.End.mul_apply, ← hΛ k, hGf k (hSU hk)]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ hSK hr hidx, hEq, map_smul, map_smul, map_sum, map_sum,
    smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, map_smul, hΛ, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem extTensor_twRep {G₁ G₂ V₁ V₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂) (χ₁ : G₁ →* ℂˣ) (χ₂ : G₂ →* ℂˣ)
    (g : G₁ × G₂) (x : V₁ ⊗[ℂ] V₂) :
    GlobalTheory.SmGL.extTensor (twRep ρ₁ χ₁) (twRep ρ₂ χ₂) g x = (((χ₁ g.1 : ℂˣ) : ℂ) * ((χ₂ g.2 : ℂˣ) : ℂ)) •
      GlobalTheory.SmGL.extTensor ρ₁ ρ₂ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v₁ v₂ =>
    simp only [GlobalTheory.SmGL.extTensor_tmul, twRep_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
      mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem mu_fac (μ : HChar E) (w : Pl E) (m : GLw a w × GLw b w) :
    ((μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ) : ℂ) =
      ((μ.loc w ((-1) ^ (a * b)) : ℂˣ) : ℂ) *
        ((((((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 : ℂˣ) : ℂ) *
          (((((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 : ℂˣ) : ℂ)) := by
  have hb : ∀ x, (μ ^ b).loc w x = μ.loc w x ^ b := fun x => rfl
  have ha : ∀ x, (μ ^ a).loc w x = μ.loc w x ^ a := fun x => rfl
  simp [map_mul, map_pow, mul_assoc, hb, ha]

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
