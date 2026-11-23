import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FrobDenom

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_incl {κ : Type} (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW) (u : RA ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M) u) k =
      incl ((Algebra.TensorProduct.basis RA tb).repr u k) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

theorem map_smul_left (f : RW →ₐ[O] RW) (r : RW) (z : RW ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (r • z) =
      f r • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

theorem mem_range_of_frob {κ : Type} [Fintype κ] (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (r : RA) (z w : RW ⊗[O] M)
    (hw : w ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)))
    (h : TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z = incl r • z + w) :
    z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  obtain ⟨w', rfl⟩ := hw
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set ta := Algebra.TensorProduct.basis RA tb with hta
  have key := hA κ Unit (Matrix.of fun k _ => tt.repr z k) (Matrix.diagonal fun _ => r) 1
    (Matrix.of fun k _ => ta.repr w' k) (by
      ext k u
      have h1 := congrArg (fun x => tt.repr x k) h
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [htt, GlobalTheory.Sandwich.repr_phi, repr_incl, ← htt, ← hta] at h1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_map (map_zero _)]
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
      exact h1)
  choose c hc using fun k => key k ()
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

end Abstract

section Alg

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem φ_prod (φ : A →ₐ[O] A) (X Q : A) (hXQ : φ X = X * Q) (m : ℕ) :
    φ (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) =
      (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) * ∏ j ∈ Finset.range (m + 1), (φ ^ j) Q := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hXQ, map_mul]

theorem multiset_dvd (f : ℕ → A) (m : ℕ) (J : Multiset ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    (J.map f).prod ∣ (∏ j ∈ Finset.range (m + 1), f j) ^ Multiset.card J := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons j J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    refine mul_dvd_mul (ih fun i hi => hJ i (Multiset.mem_cons_of_mem hi)) ?_
    exact Finset.dvd_prod_of_mem f
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hJ j (Multiset.mem_cons_self j J))))

theorem X_dvd (φ : A →ₐ[O] A) (X : A) (m : ℕ) : X ∣ ∏ j ∈ Finset.range (m + 1), (φ ^ j) X := by
  have := Finset.dvd_prod_of_mem (fun j => (φ ^ j) X) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa using this

end Alg

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]

set_option maxHeartbeats 1000000 in

theorem of_sand (E : EtTie W RA RW inclR φR gR πA)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = S.map inclR * Z * S'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (T : LocLat G Qp LL O) {κ : Type} [Fintype κ] (tb : Module.Basis κ O ↥T.L.T) (m₀ : ℕ)
    (hm₀ : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR (E.io W.X) ^ m₀)) LinearMap.id (E.jD T x))
    (J : Multiset ℕ) (y : W.DD T) (hy : (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T)
    (b : TW RW T) (hb : TWmap φR T b - b = E.jD T y) (m : ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft O
      (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
        TAinf inclR T := by
  set Y := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X with hY
  set L := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.Q with hL
  set Jp := (J.map fun j => (W.φA ^ j) W.Q).prod with hJp
  have hYL : W.φA Y = Y * L := φ_prod W.φA W.X W.Q W.φA_X m
  refine ⟨m₀ + Multiset.card J, ?_⟩
  rw [GlobalTheory.NL.SandArb.map_mulLeft]
  have hdiv : W.X ^ m₀ * Jp ∣ (Y * L) ^ (m₀ + Multiset.card J) := by
    rw [mul_pow, pow_add, pow_add]
    refine (mul_dvd_mul (pow_dvd_pow_of_dvd (X_dvd W.φA W.X m) m₀) (multiset_dvd _ m J hJ)).trans ?_
    exact ⟨Y ^ Multiset.card J * L ^ m₀, by ring⟩
  obtain ⟨R, hR⟩ := hdiv
  set a := m₀ + Multiset.card J with ha
  have hb' : TWmap φR T b = E.jD T y + b := sub_eq_iff_eq_add.mp hb
  have hφc : TensorProduct.map φR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)
      (inclR (E.io Y) ^ a • b) =
      inclR (E.io (L ^ a)) • (inclR (E.io Y) ^ a • b) + inclR (E.io ((Y * L) ^ a)) • E.jD T y := by
    rw [map_smul_left, map_pow, ← hφ, hYL]
    change inclR (E.io (Y * L)) ^ a • TWmap φR T b = _
    rw [hb', smul_add, add_comm, smul_smul, map_pow, map_pow, map_pow, map_pow, map_mul, map_mul,
      mul_pow, mul_comm]
  have hw : inclR (E.io ((Y * L) ^ a)) • E.jD T y ∈
      LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)) := by
    obtain ⟨y', hy'⟩ := hm₀ _ hy
    rw [GlobalTheory.NL.SandArb.map_mulLeft, jD_smulA] at hy'
    rw [hR, map_mul, map_mul, map_mul, map_mul, mul_comm, mul_smul, mul_smul, map_pow, map_pow]
    refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ ?_
    rw [← hy']
    exact ⟨y', rfl⟩
  have key := mem_range_of_frob tb inclR φR hA (E.io (L ^ a)) _ _ hw hφc
  exact key

end Generic

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈ TAinf (inclR LL) T := by
  intro D HW F l _ K s LL h W E T hT J y hy b hb m hJ
  obtain ⟨m₀, hm₀, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  exact of_sand E (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.1
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) T
    (Module.Free.chooseBasis ↥(OL LL) ↥T.L.T) m₀ hm₀ J y hy b hb m hJ

end GlobalTheory.NL.FrobDenom
