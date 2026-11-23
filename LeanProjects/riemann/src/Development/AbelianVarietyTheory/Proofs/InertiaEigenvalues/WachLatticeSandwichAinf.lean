import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficientsStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open TensorProduct Module

noncomputable section

namespace GlobalTheory.Sandwich

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_phi {κ : Type} (tb : Basis κ O M) (φ : RW →ₐ[O] RW) (z : RW ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z) k =
      φ ((Algebra.TensorProduct.basis RW tb).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

theorem incl_smul_mem (incl : RA →ₐ[O] RW) (a : RA) (z : RW ⊗[O] M)
    (hz : z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M))) :
    incl a • z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨a • w, ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]

theorem upper {κ ι : Type} [Fintype κ] [Fintype ι] (tb : Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (x ξ : RW) (hx : φ x = x * ξ) (m : ℕ) (nb : ι → RW ⊗[O] M) (P : Matrix ι ι RA)
    (hP : ∀ i, ξ ^ m • TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) (nb i) =
      ∑ j, incl (P i j) • nb j) (i : ι) :
    x ^ m • nb i ∈
      LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  set tt := Algebra.TensorProduct.basis RW tb with htt
  have h := hA ι κ (Matrix.of fun i k => x ^ m * tt.repr (nb i) k) P 1 0 (by
    ext i k
    have h1 := congrArg (fun z => tt.repr z k) (hP i)
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply] at h1
    rw [htt, repr_phi, ← htt] at h1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.map_zero _ (map_zero _),
      add_zero, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, hx]
    rw [mul_pow, mul_assoc, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring)
  choose c hc using h i
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr (nb i)]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [smul_smul, ← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

theorem lower {κ ι : Type} [Fintype κ] [Fintype ι] (tb : Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (x ξ : RW) (hx : φ x = x * ξ) (m : ℕ) (nb : Basis ι RW (RW ⊗[O] M)) (R : Matrix ι ι RA)
    (hR : ∀ i, ξ ^ m • nb i =
      ∑ j, incl (R i j) • TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) (nb j))
    (k : κ) : ∃ c : ι → RA, x ^ m • ((1 : RW) ⊗ₜ[O] tb k) = ∑ j, incl (c j) • nb j := by
  classical
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set Y : Matrix ι κ RW := Matrix.of fun i k => tt.repr (nb i) k with hY
  set U : Matrix κ ι RW := Matrix.of fun k i => nb.repr (tt k) i with hU
  have hYU : Y * U = 1 := by
    ext i j
    have := congrArg (fun z => nb.repr z j) (tt.sum_repr (nb i))
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply] at this
    rw [Matrix.mul_apply]
    simp only [hY, hU, Matrix.of_apply]
    rw [this, nb.repr_self, Matrix.one_apply, Finsupp.single_apply]
  have hUY : U * Y = 1 := by
    ext i j
    have := congrArg (fun z => tt.repr z j) (nb.sum_repr (tt i))
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply] at this
    rw [Matrix.mul_apply]
    simp only [hY, hU, Matrix.of_apply]
    rw [this, tt.repr_self, Matrix.one_apply, Finsupp.single_apply]
  have hφ : Y.map φ * U.map φ = 1 := by
    rw [← Matrix.map_mul, hYU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ξ ^ m • Y = R.map incl * Y.map φ := by
    ext i k
    have h1 := congrArg (fun z => tt.repr z k) (hR i)
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply] at h1
    simp only [htt, repr_phi] at h1
    rw [Matrix.mul_apply]
    simpa [hY, htt] using h1
  have h2 : ξ ^ m • U.map φ = U * R.map incl := by
    calc ξ ^ m • U.map φ = U * (ξ ^ m • Y) * U.map φ := by
          rw [Matrix.mul_smul, hUY, Matrix.smul_mul, Matrix.one_mul]
      _ = U * R.map incl := by
          rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, hφ, Matrix.mul_one]
  have h := hA κ ι (x ^ m • U) 1 R 0 (by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.map_zero _ (map_zero _),
      add_zero, Matrix.smul_mul, ← h2]
    ext i j
    simp [hx, mul_pow, mul_assoc])
  choose c hc using h k
  refine ⟨c, ?_⟩
  have h3 : ((1 : RW) ⊗ₜ[O] tb k) = tt k := by rw [htt, Algebra.TensorProduct.basis_apply]
  rw [h3]
  conv_lhs => rw [← nb.sum_repr (tt k)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc j, smul_smul]
  simp [hU]

end Abstract

section Sit

variable (S : Sit) (E : S.Comparison₂)

theorem jD_smulA (T : LocLat S.G S.Qp S.LL S.O) (a : LetA S.O S.n) (y : S.W.DD T) :
    E.jD T (a • y) = S.inclR (E.io a) • E.jD T y := by
  rw [← algebraMap_smul S.W.EE a y, E.jD_smul, E.ioE_ext]

theorem φD_smulA (T : LocLat S.G S.Qp S.LL S.O) (a : LetA S.O S.n) (y : S.W.DD T) :
    S.W.φD T (a • y) = S.W.φA a • S.W.φD T y := by
  rw [← algebraMap_smul S.W.EE a y, S.W.φD_smul, S.W.φE_ext, algebraMap_smul]
  rfl

theorem φA_one_add_π : S.W.φA (1 + letπ) = (1 + letπ) ^ S.PD.p := by
  rw [map_add, map_one, S.W.φA_π]
  funext i
  have := S.W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q]
  rw [this]; ring

theorem φA_pow_one_add_π (k : ℕ) :
    (S.W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (S.PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add_π, ← pow_mul, pow_succ']

theorem frobenius_inclusion_X_eq_mul_Q (hu : S.φR (S.inclR (1 + S.πA)) = S.inclR (1 + S.πA) ^ S.PD.p) :
    S.φR (S.inclR (E.io S.W.X)) = S.inclR (E.io S.W.X) * S.inclR (E.io S.W.Q) := by
  have hX : S.W.X = (1 + letπ) ^ (S.PD.p ^ (S.W.s - 1)) - 1 := by
    rw [← φA_pow_one_add_π, map_add, map_one, LocWach.X]; ring
  have hXQ : S.W.X * S.W.Q = ((1 + letπ) ^ S.PD.p) ^ (S.PD.p ^ (S.W.s - 1)) - 1 := by
    rw [LocWach.X, LocWach.Q, ← map_mul, ← S.W.φA_π, ← pow_mul, mul_comm S.PD.p, pow_mul,
      ← φA_pow_one_add_π, ← map_pow, ← φA_one_add_π, map_add, map_one, map_add, map_one]
    ring
  have hπ : E.io (1 + letπ) = 1 + S.πA := by rw [map_add, map_one, E.io_π]
  rw [← map_mul, ← map_mul, hXQ, hX]
  simp only [map_sub, map_pow, map_one, hπ, hu]

theorem sandwich_of
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q S.RW) (P : Matrix p p S.RA)
      (P' : Matrix q q S.RA) (Y : Matrix p q S.RA),
      Z.map S.φR = P.map S.inclR * Z * P'.map S.inclR + Y.map S.inclR →
        ∀ a b, Z a b ∈ Set.range S.inclR)
    (hx : S.φR (S.inclR (E.io S.W.X)) = S.inclR (E.io S.W.X) * S.inclR (E.io S.W.Q))
    [Nontrivial S.O]
    (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T))
    (hW : WClauses S E T M0 h0 N) :
    (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧
    ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈
      Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  classical
  obtain ⟨⟨ι, _, b, hli, hsp⟩, h1, h2, -⟩ := hW
  have : Module.Free S.O ↥T.L.T := T.L.free
  have : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.Free.chooseBasis S.O ↥T.L.T
  have hexp : ∀ y ∈ N, ∃ c : ι → LetA S.O S.n, y = ∑ j, c j • (b j : S.W.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg N.subtype (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : ι → LetA S.O S.n) (w : ι → S.W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, S.inclR (E.io (c j)) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA S E T _ _
  constructor
  · choose P hP using fun i => hexp _ (h1 _ (b i).2)
    have hup := upper tb S.inclR S.φR hA _ _ hx M0 (fun i => E.jD T (b i : S.W.DD T))
      (Matrix.of fun i j => E.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    rw [hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact incl_smul_mem S.inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ phiSpan S T N, ∃ c : ι → LetA S.O S.n,
        y = ∑ j, c j • S.W.φD T (b j : S.W.DD T) := by
      intro y hy
      have : phiSpan S T N ≤ Submodule.span (LetA S.O S.n)
          (Set.range fun j => S.W.φD T (b j : S.W.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose R hR using fun i => hexp2 _ (h2 _ (b i).2)
    let nb : Basis ι S.RW (TW S.RW T) := Basis.mk hli hsp.ge
    have hnb : ∀ i, nb i = E.jD T (b i : S.W.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := lower tb S.inclR S.φR hA _ _ hx h0 nb
      (Matrix.of fun i j => E.io (R i j)) (by
        intro i
        have := congrArg (E.jD T) (hR i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    intro t
    rw [← tb.sum_repr t, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [TensorProduct.tmul_smul, smul_comm]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hlow k
    rw [hc]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, b j, (b j).2, ?_⟩
    rw [hnb]

end Sit

theorem φRW_teichmuller {l : ℕ} [Fact l.Prime] (LL : FinExt l) (e : OCb l) :
    φRW LL (inclR LL (1 + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))) =
      inclR LL (1 + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)) ^ l := by
  have h : (1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e : Ainf l) := by
    rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]; abel
  rw [h]
  simp only [inclR, φRW, Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_pow,
    one_pow]
  congr 1
  change WittVector.map (frobenius (Cb l) l) (WittVector.map (algebraMap (OCb l) (Cb l))
    (WittVector.teichmuller l e)) = (WittVector.map (algebraMap (OCb l) (Cb l))
    (WittVector.teichmuller l e)) ^ l
  rw [WittVector.map_teichmuller, WittVector.map_teichmuller, ← map_pow, frobenius_def]

theorem sandwich : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T)), WClauses S E T M0 h0 N → (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧ ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈ Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  intro D HW F l _ K s LL h S E T M0 h0 N hW
  have : Nontrivial S.O := inferInstanceAs (Nontrivial ↥(OL LL))
  refine sandwich_of S E (GlobalTheory.T.frobenius_integrality_tensor_ainf_coefficients l LL) (frobenius_inclusion_X_eq_mul_Q S E ?_) T M0 h0 N hW
  have hp : S.PD.p = l := (D.loc l).PD_p K
  rw [hp]
  exact φRW_teichmuller LL _

end GlobalTheory.Sandwich
