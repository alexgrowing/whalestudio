import Formalism.LocalRingCardinality.SpanPowerMembership.NZColC

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.ND

section

variable (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev MuN : Type := EuclideanSpace ℂ ι

def eE : MuN ι ≃ₗ[ℂ] FK ι := (EuclideanSpace.equiv ι ℂ).toLinearEquiv.trans (eF ι)

theorem eE_apply (φ : MuN ι) (c : ι) (y : Unit) : eE ι φ c y = φ c := rfl

theorem inner_eE (φ ψ : MuN ι) : inner ℂ φ ψ = ipS ι (eE ι φ) (eE ι ψ) := by
  rw [ipS_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [eE_apply, eE_apply, RCLike.inner_apply]
  exact mul_comm _ _

variable {ι} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (σ : LL →+* ℂ)

def jE : (ι → LL) →ₛₗ[σ] MuN ι where
  toFun x := (eE ι).symm (slK σ x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [LinearMap.map_smulₛₗ, map_smul]

theorem eE_jE (x : ι → LL) : eE ι (jE σ x) = slK σ x := (eE ι).apply_symm_apply _

theorem jE_basis : LinearIndependent ℂ (fun i => jE σ ((stdHLat LL ι).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jE σ ((stdHLat LL ι).b i))) = ⊤ := by
  obtain ⟨h1, h2⟩ := slK_basis (ι := ι) σ
  have h : (fun i => jE σ ((stdHLat LL ι).b i)) = (eE ι).symm ∘ fun i => slK σ ((stdHLat LL ι).b i) := rfl
  rw [h]
  refine ⟨h1.map' _ (LinearEquiv.ker _), ?_⟩
  rw [Set.range_comp]
  have h3 := Submodule.map_span (eE ι).symm.toLinearMap (Set.range fun i => slK σ ((stdHLat LL ι).b i))
  rw [h2, Submodule.map_top, LinearEquiv.range] at h3
  exact h3.symm

theorem norm_jE (x : ι → LL) :
    Formalism.HermitianLatticesTheory.normAt (stdHLat LL ι).b (stdHLat LL ι).X (InfinitePlace.mk σ) x = ‖jE σ x‖ := by
  rw [normAt_std, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  rfl

end

section Rec

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

def eMuN (hT2 : T ≠ 2) : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mram :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop _ (atTN_Mram hc K T Dst hD du hdu Gam hG hT2)).symm

theorem eMuN_coe (hT2 : T ≠ 2) (φ : MuN (K.cls 0)) :
    ((eMuN hc K T Dst hD du hdu Gam hG hT2 φ : (atTN hc K T Dst hD du hdu Gam hG).Mram) : FK (K.cls 0)) =
      eE (K.cls 0) φ := rfl

def eCuN : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mu0 :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop (⊤ : Submodule ℂ (FK (K.cls 0))) rfl).symm

theorem eCuN_coe (φ : MuN (K.cls 0)) :
    ((eCuN hc K T Dst hD du hdu Gam hG φ : (atTN hc K T Dst hD du hdu Gam hG).Mu0) : FK (K.cls 0)) =
      eE (K.cls 0) φ := rfl

end Rec

end Formalism.BasicNotions.Examples₂.NZ
