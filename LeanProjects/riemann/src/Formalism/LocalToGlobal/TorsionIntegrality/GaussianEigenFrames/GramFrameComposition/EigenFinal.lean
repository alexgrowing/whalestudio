import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ

noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.Top (IsLatH phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.L2.Th1.G (betaPair)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

theorem TensorNorm_of (h : TensorBlock) : TensorNorm := by
  intro p _ ι L n _ hm E _ H _ _ emb Ja Jl Jr _ _ _ v hA hl hr N0 N1 Gc P P' A th u hth hform hAeq hG hu hu1 hP hP' t ab ab'
  obtain ⟨e, he, heq⟩ := h ℂ_[p] E H emb Ja Jl Jr hA hl hr N0 N1 Gc P P' th u hth hG hu hu1 hP hP' t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← heq]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hAeq, hAeq, hform]

namespace EigenLocalizationShapes

theorem pair (hE : EigenFrameE) (hI : IotaOK) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ)
    (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ dK) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (hpd : p ∣ dK) (ι : ℂ ≃+* ℂ_[p])
    (hN : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι)
    {J : Type} [Fintype J] (v : J → n → ℂ) {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ}
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ))
    (hF : IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act
      v A u) :
    p = dK ∧ ‖ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))‖ = ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) ∧
    ∃ q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
      IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a₀ b₀ dK ha hdK lam hlam) h Λ v A u
        (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) q := by
  have hp : p = dK := (Nat.prime_dvd_prime_iff_eq Fact.out hcm.2.2.2).1 hpd
  have h4 : dK % 4 = 3 := by
    have := hcm.2.2.1
    omega
  obtain ⟨g₁, ε, hIsom, hidx, -, -, -⟩ := hN
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := hF
  exact ⟨hp, (hI dK h4 p ι).1,
    hE a₀ b₀ c₀ dK ha hdK lam hlam hcm n h Λ g₁ hIsom p ι hidx J v f13 hp E cE s δ f1 f2 f3 f4 f5 f6 H emb f7 f8 f9 f10
      act f11 f12 N0 N1 A u f14 f15 f16⟩

end EigenLocalizationShapes

theorem ShapeEigenLoc_of (hE : EigenFrameE) (hI : IotaOK) (h : ShapeLoc) : ShapeEigenLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ hm Λ hsd hst θ hθ p _ hpd ι hW hN κx _ r t N hr hN0 hpN ht J _ v H _ _ N0 N1
    A u E _ _ _ cE s δ emb act hF
  obtain ⟨-, hth, q, hq⟩ := EigenLocalizationShapes.pair hE hI ha hdK lam hlam hcm hm Λ θ p hpd ι hN v A u E cE s δ emb act hF
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcm n hm Λ hsd hst θ hθ p hpd ι hW hN κx r t N hr hN0 hpN ht J v H N0 N1 A u _ q
    (le_of_eq hth) hq

theorem ThmBEigenLoc_of (hE : EigenFrameE) (hI : IotaOK) (h : ThmBLoc) : ThmBEigenLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ hm Λ hsd hst θ hθ p _ hpd ι hW hN κx _ r t N hr hN0 hpN ht J _ v H _ _ N0 N1
    A u E _ _ _ cE s δ emb act hF
  obtain ⟨-, hth, q, hq⟩ := EigenLocalizationShapes.pair hE hI ha hdK lam hlam hcm hm Λ θ p hpd ι hN v A u E cE s δ emb act hF
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcm n hm Λ hsd hst θ hθ p hpd ι hW hN κx r t N hr hN0 hpN ht J v H N0 N1 A u _ q
    (le_of_eq hth) hq

theorem ThmBGaussEigenLoc_of (hE : EigenFrameE) (hI : IotaOK) (h : ThmBGaussLoc) : ThmBGaussEigenLoc := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ hm Λ hsd hst θ hθ p _ hpd ι hW hN κx _ r t N hr hN0 hpN ht J _ v H _ _ N0 N1
    A u E _ _ _ cE s δ emb act hF
  obtain ⟨hp, hth, q, hq⟩ := EigenLocalizationShapes.pair hE hI ha hdK lam hlam hcm hm Λ θ p hpd ι hN v A u E cE s δ emb act hF
  have hc : (dK : ℂ_[p]) = (p : ℂ_[p]) := congrArg (Nat.cast : ℕ → ℂ_[p]) hp.symm
  rw [hc] at hth
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcm n hm Λ hsd hst θ hθ p hpd ι hW hN κx r t N hr hN0 hpN ht J v H N0 N1 A u _ q
    (le_of_eq hth) hq

theorem ShapeEigenFree_of (hN : LocNormFree) (h : ShapeEigenLoc) : ShapeEigenFree := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ hm Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hκ⟩ := hN a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, ?_⟩
  intro θ hθ hten p _ hd ι hW
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ hLat.2.1 hLat.2.2.1 θ hθ p hd ι hW (hκ θ hθ hten p ι)

theorem ThmBEigenFree_of (hN : LocNormFree) (h : ThmBEigenLoc) : ThmBEigenFree := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ hm Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hκ⟩ := hN a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, ?_⟩
  intro θ hθ hten p _ hd ι hW
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ hLat.2.1 hLat.2.2.1 θ hθ p hd ι hW (hκ θ hθ hten p ι)

theorem ThmBGaussEigenFree_of (hN : LocNormFree) (h : ThmBGaussEigenLoc) : ThmBGaussEigenFree := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcmok n _ _ hm Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hκ⟩ := hN a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, ?_⟩
  intro θ hθ hten p _ hd ι hW
  exact h a₀ b₀ c₀ dK ha hdK lam hlam hcmok n hm Λ hLat.2.1 hLat.2.2.1 θ hθ p hd ι hW (hκ θ hθ hten p ι)

end Formalism.L2.Th1.GD
