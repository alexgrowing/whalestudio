import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairIndProd
open GlobalTheory.SmGL GlobalTheory.PRep

section Transport

variable {G W₁ W₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
  {P Q : Subgroup G} {σ : Representation ℂ P W₁} {τ : Representation ℂ Q W₂}

def indTransport (hQP : Q ≤ P) (T : W₁ →ₗ[ℂ] W₂)
    (hT : ∀ (q : Q) (w : W₁), T (σ ⟨q, hQP q.2⟩ w) = τ q (T w)) :
    (smInd P σ).IntertwiningMap (smInd Q τ) where
  toLinearMap :=
    { toFun := fun φ => ⟨⟨fun g => T (φ.1.1 g), fun q g => by
          show T (φ.1.1 ((⟨q, hQP q.2⟩ : P) * g)) = τ q (T (φ.1.1 g))
          rw [φ.1.2 ⟨q, hQP q.2⟩ g, hT]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds φ.2 (by simp)) fun g hg => by
          have hg' : ind P σ g φ.1 = φ.1 := hg
          apply Subtype.ext
          funext x
          exact congrArg T (congrFun (congrArg Subtype.val hg') x))⟩
      map_add' := fun φ ψ => by ext g; simp
      map_smul' := fun c φ => by ext g; simp }
  isIntertwining' g := by ext φ x; rfl

theorem indTransport_apply (hQP : Q ≤ P) (T : W₁ →ₗ[ℂ] W₂)
    (hT : ∀ (q : Q) (w : W₁), T (σ ⟨q, hQP q.2⟩ w) = τ q (T w)) (φ) (g : G) :
    (indTransport hQP T hT φ).1.1 g = T (φ.1.1 g) := rfl

theorem nonempty_smInd_equiv (hPQ : P = Q) (T : W₁ ≃ₗ[ℂ] W₂)
    (hT : ∀ (p : P) (q : Q), (p : G) = q → ∀ w, T (σ p w) = τ q (T w)) :
    Nonempty ((smInd P σ).Equiv (smInd Q τ)) := by
  subst hPQ
  have h1 : ∀ (q : P) (w : W₁), (T : W₁ →ₗ[ℂ] W₂) (σ ⟨q, le_refl P q.2⟩ w) = τ q (T w) :=
    fun q w => hT _ _ rfl w
  have h2 : ∀ (q : P) (w : W₂), (T.symm : W₂ →ₗ[ℂ] W₁) (τ ⟨q, le_refl P q.2⟩ w) = σ q (T.symm w) := by
    intro q w
    apply T.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hT q q rfl, LinearEquiv.apply_symm_apply]
  let f := indTransport le_rfl (T : W₁ →ₗ[ℂ] W₂) h1
  let f' := indTransport le_rfl (T.symm : W₂ →ₗ[ℂ] W₁) h2
  refine ⟨GlobalTheory.LocGL.equivOfBijective f ⟨fun φ ψ hφψ => ?_, fun ψ => ⟨f' ψ, ?_⟩⟩⟩
  · have := congrArg (fun χ => f' χ) hφψ
    apply Subtype.ext; apply Subtype.ext; funext x
    have hx := congrFun (congrArg (fun χ : smoothPart (ind P σ) => χ.1.1) this) x
    simpa [f, f', indTransport_apply] using hx
  · apply Subtype.ext; apply Subtype.ext; funext x
    show T (T.symm (ψ.1.1 x)) = ψ.1.1 x
    simp

end Transport

section Pair

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (b' : Fin 2 → ℕ)

theorem pairPlace_zero (i : Fin (b' 0)) :
    GlobalTheory.LeviBlockExponent.pairPlace b' (rfl : b' 0 + b' 1 = _) ⟨0, i⟩ = two (stdSum (rfl : b' 0 + b' 1 = _)) ⟨false, i⟩ := by
  ext
  simp [GlobalTheory.LeviBlockExponent.pairPlace, stdSum]

theorem pairPlace_one (j : Fin (b' 1)) :
    GlobalTheory.LeviBlockExponent.pairPlace b' (rfl : b' 0 + b' 1 = _) ⟨1, j⟩ = two (stdSum (rfl : b' 0 + b' 1 = _)) ⟨true, j⟩ := by
  ext
  simp [GlobalTheory.LeviBlockExponent.pairPlace, stdSum]

theorem modExp_pair_zero : modExp (fun j : Fin 2 => Fin (b' j)) 0 = b' 1 := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

theorem modExp_pair_one : modExp (fun j : Fin 2 => Fin (b' j)) 1 = -(b' 0 : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

end Pair

section Pair2

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (b' : Fin 2 → ℕ)

theorem parab_pair_eq :
    parab k (GlobalTheory.LeviBlockExponent.pairPlace b' (rfl : b' 0 + b' 1 = _)) =
      parab k (two (stdSum (rfl : b' 0 + b' 1 = _))) := by
  ext g
  rw [mem_parab_iff, mem_parab_two]
  constructor
  · intro h j i
    have := h 1 0 j i (by decide)
    rwa [pairPlace_one, pairPlace_zero, two_true, two_false] at this
  · intro h a c i j hca
    fin_cases a <;> fin_cases c
    · exact absurd hca (by decide)
    · exact absurd hca (by decide)
    · have := h i j
      rw [← two_true, ← two_false, ← pairPlace_one, ← pairPlace_zero] at this
      exact this
    · exact absurd hca (by decide)

theorem leviProj_pair_zero (p : parab k (GlobalTheory.LeviBlockExponent.pairPlace b' (rfl : b' 0 + b' 1 = _)))
    (q : parab k (two (stdSum (rfl : b' 0 + b' 1 = _)))) (hpq : (p : GL (Fin (b' 0 + b' 1)) k) = q) :
    leviProj k _ p 0 = leviProj k _ q false := by
  ext i j
  rw [leviProj_apply, leviProj_apply, pairPlace_zero, pairPlace_zero, hpq]

theorem leviProj_pair_one (p : parab k (GlobalTheory.LeviBlockExponent.pairPlace b' (rfl : b' 0 + b' 1 = _)))
    (q : parab k (two (stdSum (rfl : b' 0 + b' 1 = _)))) (hpq : (p : GL (Fin (b' 0 + b' 1)) k) = q) :
    leviProj k _ p 1 = leviProj k _ q true := by
  ext i j
  rw [leviProj_apply, leviProj_apply, pairPlace_one, pairPlace_one, hpq]

theorem deltaHalf_pair (g : Levi k (fun j : Fin 2 => Fin (b' j))) :
    deltaHalf k (fun j : Fin 2 => Fin (b' j)) g =
      absPow k ((b' 1 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g 0)) *
        absPow k (-(b' 0 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g 1)) := by
  rw [deltaHalf_apply, Fin.prod_univ_two, modExp_pair_zero, modExp_pair_one]
  push_cast
  rfl

theorem pairChar_apply' (μ : Fin 2 → kˣ →* ℂˣ) (g : Levi k (fun j : Fin 2 => Fin (b' j))) :
    GlobalTheory.LeviBlockExponent.pairChar k b' μ g = μ 0 (Matrix.GeneralLinearGroup.det (g 0)) * μ 1 (Matrix.GeneralLinearGroup.det (g 1)) := by
  simp [GlobalTheory.LeviBlockExponent.pairChar, MonoidHom.finsetProd_apply, Fin.prod_univ_two]

end Pair2

theorem pairInd_equiv_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (b' : Fin 2 → ℕ) (d : ℕ) (h : b' 0 + b' 1 = d) (μ : Fin 2 → kˣ →* ℂˣ),
    Nonempty (Representation.Equiv ((GlobalTheory.LeviBlockExponent.pairInd k b' h μ).comp (GlobalTheory.CuspBlock.glCast h))
      (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin (b' 0)) (μ 0)) (GlobalTheory.SmGL.detRep (Fin (b' 1)) (μ 1)))) := by
  intro k _ _ _ _ b' d h μ
  subst h
  simp only [GlobalTheory.CuspBlock.glCast_rfl, MonoidHom.comp_id]
  unfold GlobalTheory.LeviBlockExponent.pairInd prod₂ ind₂ parInd
  refine nonempty_smInd_equiv (parab_pair_eq k b') (TensorProduct.rid ℂ ℂ).symm fun p q hpq w => ?_
  have hL : leviProj k _ q = leviTwo k _ _ (leviProj k _ p 0, leviProj k _ p 1) := by
    funext x
    cases x
    · exact (leviProj_pair_zero k b' p q hpq).symm
    · exact (leviProj_pair_one k b' p q hpq).symm
  simp only [MonoidHom.comp_apply, twist_apply, ofChar_apply, TensorProduct.rid_symm_apply, hL,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, extTensor_tmul, deltaHalf_two,
    deltaHalf_pair, pairChar_apply']
  simp only [Fintype.card_fin, detRep, ofChar_apply, detChar_apply, Units.val_mul, smul_eq_mul]
  have hc : ∀ x c : ℂ, x ⊗ₜ[ℂ] c = (c * x) ⊗ₜ[ℂ] (1 : ℂ) := fun x c => by
    rw [← smul_eq_mul c x, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  conv_rhs => rw [TensorProduct.smul_tmul', hc]
  congr 1
  ring

end GlobalTheory.PairIndProd
