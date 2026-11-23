import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewLocalPlaceData
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.UnipShiftEv

open Matrix

theorem ev_rho_unip_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    B.IsGood σ → G.IsGood B → ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ u ∈ unip σ G.V' H, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      e' (G.M'.co.rho B.ψ (mat u * shiftB σ H H' 1) Ψ) = e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) Ψ) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC hB hG e' he u hu Ψ hΨ
  have hH := hC.hH
  have hH' := hC.hH'
  have hY := hG.hV'
  set X := incV F H.x with hX
  set Y := incV F H.y with hYdef
  set X' := incV F H'.x with hX'
  set I := incM F H.ι with hI
  obtain ⟨hux, -⟩ := GlobalTheory.StabNormal.prop_of_mem_unip' H hu

  have hspan : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (w : Fin b → E), v = s • H.x + H.ι *ᵥ w + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (G.V'.L : Set (Fin (b + 2) → E)) := by
      rw [hY.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, w, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, w, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, w, rfl⟩ := hy
      obtain ⟨s', t', w', rfl⟩ := hz
      exact ⟨s + s', t + t', w + w', by rw [Matrix.mulVec_add]; module⟩
    | smul c y _ hy =>
      obtain ⟨s, t, w, rfl⟩ := hy
      exact ⟨c * s, c * t, c • w, by rw [Matrix.mulVec_smul]; module⟩

  set c₀ : Fin (b + 2) → E := G.V'.J *ᵥ fun i => σ (H.x i) with hc₀
  have hιc : ∀ w, (H.ι *ᵥ w) ⬝ᵥ c₀ = 0 := fun w => (hH.orth w).1
  have hxc : H.x ⬝ᵥ c₀ = 0 := hH.xx
  have hyx : H.y ⬝ᵥ c₀ ≠ 0 := by
    intro h0
    have hall : ∀ w : Fin (b + 2) → E, w ⬝ᵥ c₀ = 0 := by
      intro w
      obtain ⟨s, t, v, rfl⟩ := hspan w
      rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hxc, h0, hιc]
      simp
    have hc0 : ∀ i, c₀ i = 0 := fun i => by simpa using hall (Pi.single i 1)
    have hxJ : H.x ᵥ* G.V'.J = 0 := by
      funext i
      have hσinj : Function.Injective σ := σ.toRingHom.injective
      apply hσinj
      rw [Pi.zero_apply, map_zero, ← hc0 i]
      simp only [vecMul, mulVec, dotProduct, map_sum, map_mul, hc₀, Pi.zero_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hY.herm, mul_comm]
    have h1 := hH.xy
    unfold form at h1
    rw [dotProduct_mulVec, hxJ, zero_dotProduct] at h1
    exact zero_ne_one h1

  set C : Fin (b + 2) → AE F E := incM F G.V'.J *ᵥ fun i => cA σ (X i) with hC'
  have hCe : C = incV F c₀ := by
    rw [hC', hc₀, GlobalTheory.StabNormal.incM_mulVec]
    congr 1
  have hIC : ∀ z, (I *ᵥ z) ⬝ᵥ C = 0 := by
    intro z
    have h0 : c₀ ᵥ* H.ι = 0 := by
      funext j
      have := hιc (Pi.single j 1)
      rw [mulVec_single_one, dotProduct_comm] at this
      exact this
    rw [dotProduct_comm, dotProduct_mulVec, hCe, hI, ← GlobalTheory.StabNormal.incV_vecMul, h0]
    simp [incV, dotProduct]
  have hXC : X ⬝ᵥ C = 0 := by rw [hCe, hX, GlobalTheory.StabNormal.incV_dot, hxc, map_zero]
  have hYC : IsUnit (Y ⬝ᵥ C) := by
    rw [hCe, hYdef, GlobalTheory.StabNormal.incV_dot]
    exact (isUnit_iff_ne_zero.2 hyx).map (inclR (F := F) (E := E) (AF F))

  obtain ⟨s, t, w, hv⟩ := GlobalTheory.StabNormal.decompA H.x H.y H.ι hspan (mat u *ᵥ Y)
  rw [← hX, ← hI, ← hYdef] at hv
  have ht : t = 1 := by
    have h0 := GlobalTheory.StabNormal.dot_invariant u X hux Y
    rw [← hC', hv, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hXC, hIC] at h0
    simp only [smul_eq_mul, mul_zero, zero_add] at h0
    have h2 : (t - 1) * (Y ⬝ᵥ C) = 0 := by rw [sub_mul, h0, one_mul, sub_self]
    exact sub_eq_zero.1 ((hYC.mul_left_eq_zero).1 h2)
  rw [ht, one_smul] at hv

  have hww := GlobalTheory.IsoBLoc.pair_zero_of_form (F := F) σ G.W.J H'.x H'.x hH'.xx
  have hiso : ∀ p q : Fin (b + 2) → AE F E,
      symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (vecMulVec p X') (vecMulVec q X') = 0 := by
    intro p q
    rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hww, mul_zero, mul_zero, map_zero]
  have hadd : ∀ (p q : Fin (b + 2) → AE F E) (φ : Fn F (b + 2) (a + (b + 2))),
      G.M'.co.rho B.ψ (vecMulVec p X' + vecMulVec q X') φ =
        G.M'.co.rho B.ψ (vecMulVec p X') (G.M'.co.rho B.ψ (vecMulVec q X') φ) := by
    intro p q φ
    refine GlobalTheory.DblSiegel.rho_add G.M'.co B.ψ ?_ φ
    have := (G.M'.co.form _ _).symm.trans (hiso p q)
    exact sub_eq_zero.1 this
  have hshift : shiftB σ H H' 1 = vecMulVec Y X' := by
    simp [shiftB, hYdef, hX']
  have hmove : mat u * shiftB σ H H' 1 = vecMulVec (s • X) X' + (vecMulVec (I *ᵥ w) X' + vecMulVec Y X') := by
    rw [hshift, Matrix.mul_vecMulVec, hv, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_assoc]
  have hS : ∀ (γ : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) φ, φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) →
      G.M'.co.rho B.ψ γ φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun γ φ hφ => GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hB.std γ φ hφ
  have h1 : vecMulVec (s • X) X' ∈ isoB (F := F) H H' := by
    left
    refine ⟨s • X', ?_⟩
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hX]
    ring
  have h2 : vecMulVec (I *ᵥ w) X' ∈ isoB (F := F) H H' := Or.inr ⟨w, rfl⟩
  rw [hmove, ← Matrix.add_vecMulVec (I *ᵥ w) Y, hadd, he.inv _ h1 _ (hS _ _ hΨ), Matrix.add_vecMulVec, hadd,
    he.inv _ h2 _ (hS _ _ hΨ), hshift]

end GlobalTheory.UnipShiftEv
