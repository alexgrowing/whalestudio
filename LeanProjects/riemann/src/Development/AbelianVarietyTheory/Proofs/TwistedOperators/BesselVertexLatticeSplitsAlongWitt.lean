import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MonoBes

variable {D : D7}

theorem colMul_pX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) = rat (fun k l => d.e k i * d.qX i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, HypDec.pX, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qX i l) * y l * (incA D) (d.e k i) = (incA D) (d.e k i * d.qX i l) * y l
  rw [map_mul]
  ring

theorem colMul_pY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) = rat (fun k l => d.e' k i * d.qY i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jY, HypDec.pY, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qY i l) * y l * (incA D) (d.e' k i) = (incA D) (d.e' k i * d.qY i l) * y l
  rw [map_mul]
  ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) :
    x *ᵥ w = ∑ i, GlobalTheory.FinPl.colMul x i (w i) := by
  funext k
  simp only [mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mulVec_eq_sum_col {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    x *ᵥ w = ∑ i, fun k => x k i * w i := by
  funext k
  simp only [mulVec, dotProduct, Finset.sum_apply]

theorem rank_one_mulVec {m n k : ℕ} (a : Matrix (Fin m) (Fin k) D.host.E) (b : Matrix (Fin k) (Fin n) D.host.E)
    (i : Fin k) (x : Fin n → D.host.E) : (fun r l => a r i * b i l) *ᵥ x = fun r => a r i * (b *ᵥ x) i := by
  funext r
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S)
    (hX : ∀ i, ∀ x ∈ L, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ L)
    (hY : ∀ i, ∀ x ∈ L, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L (L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) v := by
  have h0 : ∀ x ∈ L, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ L := by
    intro x hx
    have e : d.i₀ *ᵥ (d.q0 *ᵥ x) = x - d.e *ᵥ (d.qX *ᵥ x) - d.e' *ᵥ (d.qY *ᵥ x) := by
      have := congrArg (· *ᵥ x) d.sum_eq_one_rat
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      rw [sub_sub, eq_sub_iff_add_eq]
      calc _ = d.e *ᵥ (d.qX *ᵥ x) + d.i₀ *ᵥ (d.q0 *ᵥ x) + d.e' *ᵥ (d.qY *ᵥ x) := by abel
        _ = x := this
    rw [e, mulVec_eq_sum_col d.e, mulVec_eq_sum_col d.e']
    exact L.sub_mem (L.sub_mem hx (L.sum_mem fun i _ => hX i x hx)) (L.sum_mem fun i _ => hY i x hx)
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [colMul_pX]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hX i x hx) hy
    · rw [colMul_pY]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hY i x hx) hy
    · exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.q0 h0 hy
  · rintro ⟨h1, h2, h3⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      have := congrArg (· *ᵥ y) d.sum_eq_one
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      exact this.symm
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (AddSubgroup.sum_mem _ fun i _ => h1 i) ?_) (AddSubgroup.sum_mem _ fun i _ => h2 i)
    exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.i₀ (fun x hx => hx) h3

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem antiDiagonalEpsilonGram_mulVec_of_rev_ne (ε : D.host.E) (u : Fin c → D.host.E) (j : Fin c) (hj : j.rev ≠ j) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) j = u j.rev := by
  simp only [mulVec, dotProduct, antiDiagonalSignGramMatrix]
  rw [Finset.sum_eq_single j.rev]
  · rw [if_pos (by simp only [Fin.val_rev]; omega), if_neg (Ne.symm hj), one_mul]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    ext
    simp only [Fin.val_rev]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (j : Fin n) (x : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single j x) k = M k j * x := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram (a : HermitianOrthogonalExtensionData A B c (-1)) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (a.aᴴ * B.gram) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = antiDiagonalSignGramMatrix c (-1) *ᵥ u := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have h := congrArg Matrix.conjTranspose a.perp
    change ((frameMat B A a.ι)ᴴ * B.gram * a.a)ᴴ = 0ᴴ at h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  have h2 : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]

theorem proj_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ a.lat Λ 𝔟) ∧
      (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ a.lat Λ 𝔟) := by
  obtain ⟨hc, he, s, he'⟩ := hd
  have hrev : ∀ i : Fin ρ, (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
    intro i h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := i.2
    omega
  have qX_eq : ∀ x (i : Fin ρ),
      (d.qX *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c).rev := by
    intro x i
    rw [HypDec.qX, he', ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have qY_eq : ∀ x (i : Fin ρ),
      (d.qY *ᵥ x) i = star ((-D.host.xi0) ^ (i.1 + 1)) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c) := by
    intro x i
    rw [HypDec.qY, he, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have scal : ∀ i : Fin ρ, star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    intro i
    have h1 : (fun k => d.e k i) =
        frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [he, mulVec_zero, zero_add, mulVec_single_apply]
      simp only [colsOf]
      ring
    have h2 : (d.e'ᴴ * B.gram * d.e) i i = (d.qX *ᵥ fun k => d.e k i) i := rfl
    have h3 := congrFun (congrFun d.e'e i) i
    rw [h2, h1, qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, Pi.single_eq_same,
      Matrix.one_apply_eq] at h3
    exact h3
  refine ⟨fun i x hx => ?_, fun i x hx => ?_⟩
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c) (u (Fin.castLE (by omega) i)), fun p => ?_, ?_⟩
    · by_cases hp : p = Fin.castLE (by omega) i
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, mulVec_zero,
        zero_add, mulVec_single_apply, he]
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i) * u (Fin.castLE (by omega) i)) * scal i
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c).rev (u (Fin.castLE (by omega) i : Fin c).rev),
      fun p => ?_, ?_⟩
    · by_cases hp : p = (Fin.castLE (by omega) i : Fin c).rev
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · have hs : s i * star ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
        have := congrArg star (scal i)
        rw [star_mul', star_star, star_one] at this
        exact this
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qY_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (hrev i), mulVec_zero, zero_add, mulVec_single_apply, he']
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i : Fin c).rev * u (Fin.castLE (by omega) i : Fin c).rev) * hs

end SlopeTestRemainingChoices

theorem monoAt_bes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  intro D T L sc G F hF ρ h v
  have hL : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ h
  obtain ⟨hX, hY⟩ := proj_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (G.Λ (.core (2 * ρ + 2)))
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))
  rw [← hL] at hX hY
  exact monoAt_of_proj (F.dB ρ h) _ hX hY v

end GlobalTheory.MonoBes

end
