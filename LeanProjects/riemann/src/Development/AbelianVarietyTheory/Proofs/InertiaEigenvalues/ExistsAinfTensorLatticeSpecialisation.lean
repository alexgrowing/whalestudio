import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem specPhi_coord {Z N C : Type} [CommRing Z] [AddCommGroup N] [Module Z N] [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (u : N →ₗ[Z] N)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (u (b j)) i)) (t : N) :
    (fun i => φ (b.repr (u t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  funext i
  conv_lhs => rw [← b.sum_repr t]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_mul, Matrix.mulVec, dotProduct, hU]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem specPhi_coord_smul {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t) [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (a : O)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (a • b j) i)) (t : N) :
    (fun i => φ (b.repr (a • t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  have hlin : ∀ (x : Z) (s : N), a • (x • s) = x • (a • s) := by
    intro x s
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  let u : N →ₗ[Z] N :=
    { toFun := fun s => a • s
      map_add' := fun x y => smul_add a x y
      map_smul' := fun x s => hlin x s }
  exact specPhi_coord φ b u U hU t

theorem specPhi_generic {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (L : R → Matrix (Fin d) (Fin d) C) (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (co : ↥T.L.T →+ (Fin d → C))
    (hco : ∀ (a : O) t, co (a • t) = (L (algebraMap O R a)).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (t : ↥T.L.T), Φ (r ⊗ₜ[O] t) = (L r).mulVec (co t)) ∧
      ∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z) := by
  let f : R →+ ↥T.L.T →+ (Fin d → C) :=
    { toFun := fun r =>
        { toFun := fun t => (L r).mulVec (co t)
          map_zero' := by simp
          map_add' := fun x y => by simp [Matrix.mulVec_add] }
      map_zero' := by ext t : 1; simp [hL0]
      map_add' := fun x y => by ext t : 1; simp [hLa, Matrix.add_mulVec] }
  have hf : ∀ (a : O) (r : R) (t : ↥T.L.T), f (a • r) t = f r (a • t) := by
    intro a r t
    show (L (a • r)).mulVec (co t) = (L r).mulVec (co (a • t))
    rw [Algebra.smul_def, mul_comm, hLm, hco, Matrix.mulVec_mulVec]
  refine ⟨TensorProduct.liftAddHom f hf, fun r t => rfl, fun r z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show (L (r * x)).mulVec (co t) = (L r).mulVec ((L x).mulVec (co t))
    rw [hLm, Matrix.mulVec_mulVec]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, Matrix.mulVec_add]

theorem specPhi_equiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (u : R →ₐ[O] R) (g : G) (U : Matrix (Fin d) (Fin d) C)
    (σ : C ≃+* C)
    (h : ∀ (r : R) (t : ↥T.L.T), Φ (u r ⊗ₜ[O] T.actT g t) =
      U.mulVec (fun i => σ (Φ (r ⊗ₜ[O] t) i))) (z : TW R T) :
    Φ (TWact u T g z) = U.mulVec (fun i => σ (Φ z i)) := by
  unfold TWact
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero U).symm
  | tmul r t => exact h r t
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
    congr 1
    funext i
    simp [map_add]

theorem specPhi_norm {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (S : AddSubmonoid C)
    (h : ∀ (r : R) (t : ↥T.L.T) i, Φ (r ⊗ₜ[O] t) i ∈ S) (z : TW R T) (i : Fin d) :
    Φ z i ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => exact h r t i
  | add x y hx hy => simpa using S.add_mem hx hy

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000 in

theorem specPhi_co (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (h : IsMat K LL T M A)
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act) :
    ∃ co : ↥T.L.T →+ (Fin d → PadicComplex l), (∀ t i, co t i ∈ (PadicComplexInt l).toSubring) ∧
      (∀ (g : ↥(GK K)) t i, act (g : GQ l) (co t i) = co t i) ∧
      (∀ (a : ↥(OL LL)) (t : ↥T.L.T), co (a • t) = (A a).mulVec (co t)) ∧
      (∀ (g : ↥(GK K)) (t : ↥T.L.T), co (T.actT g t) = (M (g : GQ l)).mulVec (co t)) ∧
      ∀ j, ∃ t, co t = Pi.single j 1 := by
  obtain ⟨b, hM, hA⟩ := h
  letI := zlMod LL T
  let φ : ℤ_[l] →+* PadicComplex l :=
    (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  let co : ↥T.L.T →+ (Fin d → PadicComplex l) :=
    { toFun := fun t i => zC (b.repr t i)
      map_zero' := by funext i; simp [zC]
      map_add' := fun x y => by funext i; simp [zC] }
  refine ⟨co, fun t i => ?_, fun g t i => act_zC hact _ _, fun a t => ?_, fun g t => ?_,
    fun j => ⟨b j, ?_⟩⟩
  · exact (mem_OC _).2 ((norm_zC _).le.trans (PadicInt.norm_le_one _))
  · have hs : ∀ (x : ℤ_[l]) (s : ↥T.L.T), x • s = algebraMap ℤ_[l] ↥(OL LL) x • s :=
      fun x s => rfl
    exact specPhi_coord_smul hs φ b a (A a) (fun i j => hA a i j) t
  · exact specPhi_coord φ b (actTZ LL T g) (M g) (fun i j => hM g i j) t
  · funext i
    show zC (b.repr (b j) i) = (Pi.single j (1 : PadicComplex l) : Fin d → PadicComplex l) i
    rw [b.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [zC]
    · simp [zC, hij]

theorem specPhi_abstract {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d f : ℕ}
    (S : Subring C) (A : O → Matrix (Fin d) (Fin d) C) (M : G → Matrix (Fin d) (Fin d) C)
    (σ : G → C ≃+* C) (u : G → R →ₐ[O] R) (o : Fin f → O) (κ : R → Fin f → C)
    (L : R → Matrix (Fin d) (Fin d) C) (hL : ∀ r, L r = ∑ k, κ r k • A (o k))
    (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (hal : ∀ a, L (algebraMap O R a) = A a) (hone : A 1 = 1)
    (hκS : ∀ r k, κ r k ∈ S) (hκ : ∀ g r k, κ (u g r) k = σ g (κ r k))
    (co : ↥T.L.T →+ (Fin d → C)) (hS : ∀ t i, co t i ∈ S) (hσ : ∀ g t i, σ g (co t i) = co t i)
    (hcoA : ∀ (a : O) t, co (a • t) = (A a).mulVec (co t))
    (hcoM : ∀ g t, co (T.actT g t) = (M g).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z)) ∧
      (∀ z i, Φ z i ∈ S) ∧
      (∀ g z, Φ (TWact (u g) T g z) = (M g).mulVec (fun i => σ g (Φ z i))) ∧
      ∀ t : ↥T.L.T, Φ ((1 : R) ⊗ₜ[O] t) = co t := by
  obtain ⟨Φ, hΦt, hΦs⟩ := specPhi_generic T L hL0 hLa hLm co (fun a t => by rw [hcoA, hal])
  have hLco : ∀ r t, (L r).mulVec (co t) = ∑ k, κ r k • co (o k • t) := by
    intro r t
    rw [hL, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, hcoA]
  refine ⟨Φ, hΦs, fun z i => specPhi_norm T Φ S.toAddSubmonoid (fun r t i => ?_) z i,
    fun g z => specPhi_equiv T Φ (u g) g (M g) (σ g) (fun r t => ?_) z, fun t => ?_⟩
  · show _ ∈ S
    rw [hΦt, hLco, Finset.sum_apply]
    refine S.sum_mem fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact S.mul_mem (hκS r k) (hS _ i)
  · rw [hΦt, hΦt, hLco, hLco]
    have h1 : ∀ k, co (o k • T.actT g t) = (M g).mulVec (co (o k • t)) := fun k => by
      rw [← map_smul (T.actT g) (o k) t, hcoM]
    have h2 : (fun i => σ g ((∑ k, κ r k • co (o k • t)) i)) =
        ∑ k, κ (u g r) k • co (o k • t) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, ← hκ]
    rw [h2, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1, Matrix.mulVec_smul]
  · have h1 : L 1 = 1 := by rw [← map_one (algebraMap O R), hal, hone]
    rw [hΦt, h1, Matrix.one_mulVec]

set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_thR_alg (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) :
    thR LL θ (algebraMap ↥(OL LL) (RA LL) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
  rw [Algebra.TensorProduct.algebraMap_apply, thR_tmul, map_one]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_specPhi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  intro l _ P AI K LL T d f n M A o θ hM hθ
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨co, hS, hσ, hcoA, hcoM, hsingle⟩ := specPhi_co K LL T M A hM hact
  have hmul := lam_mul_of_isMat l K LL T d f M A o hM
  have hL : ∀ r : RA LL, lam o A (thR LL θ r) = ∑ k, kap o (thR LL θ r) k • A (o k) :=
    fun r => rfl
  have hL0 : lam o A (thR LL θ 0) = 0 := by rw [map_zero, lamMul_lam_zero]
  have hLa : ∀ x y : RA LL, lam o A (thR LL θ (x + y)) =
      lam o A (thR LL θ x) + lam o A (thR LL θ y) := fun x y => by
    rw [map_add, lamMul_lam_add]
  have hLm : ∀ x y : RA LL, lam o A (thR LL θ (x * y)) =
      lam o A (thR LL θ x) * lam o A (thR LL θ y) := fun x y => by
    rw [map_mul, hmul.2.2.2]
  have hal : ∀ a : ↥(OL LL), lam o A (thR LL θ (algebraMap ↥(OL LL) (RA LL) a)) = A a :=
    fun a => by rw [specPhi_thR_alg, hmul.1]; simp
  have hκS : ∀ (r : RA LL) (k : Fin f), kap o (thR LL θ r) k ∈ (PadicComplexInt l).toSubring :=
    fun r k => (mem_OC _).2 (norm_kap_le o _ k)
  have hκ : ∀ (g : ↥(GK K)) (r : RA LL) (k : Fin f),
      kap o (thR LL θ (gRA AI LL (g : GQ l) r)) k = AI.actC (g : GQ l) (kap o (thR LL θ r) k) :=
    fun g r k => kap_thR_gRA AI o hθ _ r k
  have keyA := specPhi_abstract (R := RA LL) T (PadicComplexInt l).toSubring
    A (fun g => M (g : GQ l)) (fun g => AI.actC (g : GQ l)) (fun g => gRA AI LL (g : GQ l)) o
    (fun r k => kap o (thR LL θ r) k) (fun r => lam o A (thR LL θ r)) hL hL0 hLa hLm hal
    hmul.2.1 hκS hκ co hS hσ hcoA hcoM
  obtain ⟨Φ, hΦs, hΦS, hΦg, hΦ1⟩ := keyA
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact hΦs
  · intro z i
    exact (mem_OC _).1 (hΦS z i)
  · intro g z
    convert hΦg g z using 3
  · intro j
    obtain ⟨t, ht⟩ := hsingle j
    exact ⟨t, (hΦ1 t).trans ht⟩

end GlobalTheory.Cyc.Decomp
