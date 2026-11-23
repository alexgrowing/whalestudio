import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace PairingSeriesCoefficients

theorem ev_eq {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ K)) (d0 : σ → K) :
    eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P = ∑ n ∈ P.support, (∏ i ∈ n.support, d0 i ^ n i) • coeff n P := by
  rw [coe_eval₂Hom, eval₂_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, map_prod]
  simp only [map_pow]

theorem coeff_of_eval {σ τ K : Type} [Field K] [Infinite K] (P : MvPolynomial σ (MvPolynomial τ K))
    (l : MvPolynomial τ K →ₗ[K] K) (R : MvPolynomial σ K)
    (h : ∀ d0 : σ → K, eval d0 R = l (eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P)) (n : σ →₀ ℕ) :
    coeff n R = l (coeff n P) := by
  classical
  have hR : R = ∑ n ∈ P.support, monomial n (l (coeff n P)) := by
    refine MvPolynomial.funext fun d0 => ?_
    rw [h d0, ev_eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
    rfl
  rw [hR, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' P.support n]
  split_ifs with hn
  · rfl
  · rw [notMem_support_iff.1 hn, map_zero]

end PairingSeriesCoefficients

theorem pairing_series_linear_form_holds : PairingSeriesLinearForm := by
  intro p _ X Kc _ _ _ j P f l R h
  have hc := PairingSeriesCoefficients.coeff_of_eval P l R h
  unfold pairD
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hc]
  classical
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := R.support)),
    Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := R.support))]
  · intro n _ hn
    rw [← hc, notMem_support_iff.1 hn, mul_zero]
  · intro n _ hn
    rw [notMem_support_iff.1 hn, map_zero, mul_zero]

namespace PairingSeriesCoefficients

section GlobalTheory

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (Lk : X.ZA j → X.ZA j → Kc)
  (hne : ∀ x y, Lk x y ≠ 0 → (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩)

include hne

theorem isWeightedHomogeneous_linP (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.ZA j) :
    IsWeightedHomogeneous (wB X j v s)
      (linP (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) x) (wB X j v s x) := by
  unfold linP
  refine IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  beta_reduce
  by_cases h : Lk x y = 0
  · rw [h, map_zero, map_zero, zero_mul]
    exact isWeightedHomogeneous_zero _ _ _
  · have h2 : wB X j v s x = wB X j v s y := by
      unfold wB
      rw [hne x y h]
    rw [h2]
    exact (isWeightedHomogeneous_X _ _ y).C_mul _

theorem mono_wh (v : X.Pl) (s : Fin (X.G.P.n' v)) (m : X.ZA j →₀ ℕ) :
    IsWeightedHomogeneous (wB X j v s)
      (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) (Finsupp.weight (wB X j v s) m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  exact IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linP X Kc j Lk hne v s x).pow _

theorem hGd (m n : X.ZA j →₀ ℕ)
    (h : coeff n (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) ≠ 0) : GoodDeg X j n ↔ GoodDeg X j m := by
  have key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩ := by
    intro v s
    rw [← wt_eq, ← wt_eq]
    by_contra hne'
    exact h ((mono_wh X Kc j Lk hne v s m).coeff_eq_zero n hne')
  unfold GoodDeg
  simp only [key]

theorem pairD_linSub (Q : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j Q (linSub Lk f) =
      pairD X Kc j (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) f := by
  classical
  exact pr_sub Lk (GoodDeg X j) (hGd X Kc j Lk hne) Q f

omit hne in

theorem evD_linT (d0 : X.ZA j → Kc) (Q : DA X Kc j) :
    evD X Kc j d0 (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) =
      evD X Kc j (fun y => ∑ z, Lk z y * d0 z) Q := by
  have h : (evD X Kc j d0).comp
      (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) :
        DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j).toRingHom = evD X Kc j (fun y => ∑ z, Lk z y * d0 z) := by
    refine ringHom_ext (fun r => ?_) fun y => ?_
    · simp [evD]
    · simp only [evD, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, linT, map_sum, map_mul,
        coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, algebraMap_eq]
  exact RingHom.congr_fun h Q

end GlobalTheory

end PairingSeriesCoefficients

theorem frame_change_pairing_holds : XB := by
  intro p _ X Kc _ _ _ _ j La La' φ P f l R h
  rw [PairingSeriesCoefficients.pairD_linSub X Kc j (bc Kc φ) (fun x y hxy => by
    by_contra hne
    exact hxy (bc_ne Kc φ x y fun h' => hne h'.symm)) P f]
  refine pairing_series_linear_form_holds p X Kc j _ f l R fun d0 => ?_
  rw [h d0, PairingSeriesCoefficients.evD_linT]

theorem transposed_frame_image_blockwise_holds : TransposedFrameImageBlockwise := by
  intro p _ X Kc _ _ _ j La La' φ d0 b
  obtain ⟨v, s⟩ := b
  refine Matrix.ext fun a b' => ?_
  show ∑ z, bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z = _
  rw [sum_block X j (fun z => bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z) v s (fun z hz => by
    rw [bc_ne Kc φ z _ hz, zero_mul])]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b'' _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [bc_same]
  ring

namespace PairingSeriesCoefficients

section Ev

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem evD_xd (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc) (b' : Fin (NJ X (j + 1))) (i : ℕ) :
    evD X Kc j d0 (xd X Kc j b.1 b.2 x b' i) =
      C (mulC (dM X Kc j b d0).transpose (fun a i => algebraMap X.G.Kf Kc (x a i)) b' i) := by
  simp only [xd, mulC, map_sum, map_mul, Matrix.transpose_apply, dMat, dM, evD, coe_eval₂Hom, eval₂_X, MvPolynomial.algebraMap_apply,
    eval₂_C, RingHom.id_apply]

theorem evD_yMat (b : BX X) (d0 : X.ZA j → Kc) :
    (yMat X Kc j b.1 b.2).map (evD X Kc j d0) =
      (yV Kc (NJ X (j + 1))).map ((rename (emX X (j + 1) b) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →+* XspC (X.Pj (j + 1)) Kc) := by
  refine Matrix.ext fun b' t => ?_
  simp only [Matrix.map_apply, yMat, yV, evD, coe_eval₂Hom, eval₂_C, RingHom.id_apply, RingHom.coe_coe, rename_X]
  rfl

end Ev

end PairingSeriesCoefficients

theorem frame_change_compatibility_holds : XC := by
  intro p _ X Kc _ _ j b x d0
  unfold tgtD tgtN
  split_ifs with ho
  · rw [map_hvO, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvO]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]
  · rw [map_hvE, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvE]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]

namespace PairingSeriesCoefficients

section Deg

theorem det_wh {σ R : Type} [CommRing R] (w : σ → ℕ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (MvPolynomial σ R)) (d : ℕ)
    (h : ∀ i i', IsWeightedHomogeneous w (M i i') d) : IsWeightedHomogeneous w M.det (m * d) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_
  have h1 : IsWeightedHomogeneous w (∏ i, M (τ i) i) (m * d) := by
    have := IsWeightedHomogeneous.prod (w := w) Finset.univ (fun i => M (τ i) i) (fun _ => d) fun i _ => h (τ i) i
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
  · rw [h2, one_smul]
    exact h1
  · rw [h2, Units.neg_smul, one_smul]
    exact (mem_weightedHomogeneousSubmodule R w _ _).1
      (neg_mem ((mem_weightedHomogeneousSubmodule R w _ _).2 h1))

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ)

theorem colFac_wh (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b : BX X) (c : ℕ) :
    IsWeightedHomogeneous (wB X j v s) (X.colFac j I b.1 b.2 c)
      (X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0) := by
  unfold Sys.colFac
  refine det_wh _ _ _ fun i i' => ?_
  rw [Matrix.of_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_
  exact (isWeightedHomogeneous_X _ (wB X j v s) (⟨b.1, (b.2, a, I b.1 b.2 c i'.val)⟩ : X.ZA j)).C_mul _

theorem PI_wh (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    IsWeightedHomogeneous (wB X j v s) (X.PI j I i0)
      (∑ c ∈ Finset.range (X.nuv v (j + 1) s 1).toNat, X.colHt v (j + 1) s c) := by
  classical
  have h1 : X.PI j I i0 = ∏ b : BX X, ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c := by
    rw [Fintype.prod_sigma]
    rfl
  have h2 := IsWeightedHomogeneous.prod (w := wB X j v s) (Finset.univ : Finset (BX X))
    (fun b => ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c)
    (fun b => ∑ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (0 + X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0))
    (fun b _ => IsWeightedHomogeneous.prod _ _ _ fun c _ => by
      refine IsWeightedHomogeneous.mul ?_ (colFac_wh X j I v s b c)
      have h3 : (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) =
          C ((p : MvPolynomial (X.FrI j) ℤ) ^ (X.colExp j I i0 b.1 b.2 c)) := by
        rw [map_pow, map_natCast]
      rw [h3]
      exact isWeightedHomogeneous_C _ _)
  rw [h1]
  convert h2 using 1
  rw [Finset.sum_eq_single (⟨v, s⟩ : BX X)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem PI_good (I : X.ColCh j) (i0 : X.Pl → ℕ) (n : X.ZA j →₀ ℕ) (hn : coeff n (X.PI j I i0) ≠ 0) : GoodDeg X j n := by
  intro v s
  rw [← wt_eq, PI_wh X j I i0 v s hn, Finset.sum_range]
  exact sum_colHt X v j s

end Deg

end PairingSeriesCoefficients

theorem frame_change_group_action_holds : XG := by
  intro p _ X Kc _ _ j I i0 f x
  classical
  rw [Finset.sum_subset (support_map_subset _ _) (fun n _ hn => by rw [notMem_support_iff.1 hn, mul_zero])]
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [smul_eval, eval_map, coeff_map, coe_eval₂Hom]
  congr 1
  unfold derAt
  rw [if_pos (PairingSeriesCoefficients.PI_good X j I i0 n (mem_support_iff.1 hn))]

theorem frame_change_injective_holds : XInj := by
  intro p _ X j
  constructor
  · rintro ⟨⟨v, s⟩, a⟩ ⟨⟨v', s'⟩, a'⟩ h
    have h1 := congrArg (idxJ X j) h
    simp only [emX, idxJ_idxI] at h1
    cases h1
    rfl
  · rintro ⟨⟨v, s⟩, a, t⟩ ⟨⟨v', s'⟩, a', t'⟩ h
    simp only [xmX] at h
    cases h
    rfl

end Formalism.L2.PairingIndexBounds.Ent
