import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionFrameOfMatrixFormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaFrobeniusInverseShiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KapIdemMemInCStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPoweStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtRho1OfMemIdealPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCountStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSuccStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

section Lift

variable (S : Sit) (E : S.Comparison₂) (T : LocLat S.G S.Qp S.LL S.O)
  (N : Submodule (LetA S.O S.n) (S.W.DD T))

theorem jD_smulA (a : LetA S.O S.n) (y : S.W.DD T) :
    E.jD T (a • y) = S.inclR (E.io a) • E.jD T y := by
  rw [← E.ioE_ext, ← E.jD_smul, algebraMap_smul]

theorem γD_smulA (g : S.W.Gam) (a : LetA S.O S.n) (y : S.W.DD T) :
    S.W.γD T g (a • y) = S.W.γA g a • S.W.γD T g y := by
  have := S.W.γD_smul T g (algebraMap (LetA S.O S.n) S.W.EE a) y
  rw [algebraMap_smul, S.W.γE_ext, algebraMap_smul] at this
  exact this

theorem exists_lift (x : S.RA) (M0 h0 : ℕ) (hinj : Function.Injective S.inclR)
    (h1 : ∀ y ∈ N, (S.inclR x) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T))
    (h2 : ∀ t : ↥T.L.T, (S.inclR x) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈
      Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y}) :
    ∃ z : ↥N →+ TW S.RA T, (∀ (a : LetA S.O S.n) (y : ↥N), z (a • y) = E.io a • z y) ∧
      (∀ (g : S.G) (u : S.RA →ₐ[S.O] S.RA), (∀ r, S.inclR (u r) = S.gR g (S.inclR r)) →
        ∀ y y' : ↥N, (y' : S.W.DD T) = S.W.γD T (S.W.resΓ g) y →
          x ^ M0 • TWact u T g (z y) = u x ^ M0 • z y') ∧
      ∀ t : ↥T.L.T, x ^ (M0 + h0) • ((1 : S.RA) ⊗ₜ[S.O] t) ∈
        AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y} := by
  have hi := TWincl_injective S.inclR hinj T
  choose z hz using fun y : ↥N => LinearMap.mem_range.1 (h1 y y.2)
  refine ⟨AddMonoidHom.mk' z (fun y y' => hi ?_), fun a y => hi ?_, fun g u hu y y' hy => hi ?_,
    fun t => ?_⟩
  · rw [map_add, hz, hz, hz, Submodule.coe_add, map_add, smul_add]
  · rw [AddMonoidHom.mk'_apply, TWincl_smul, hz, hz, Submodule.coe_smul,
      jD_smulA, smul_comm]
  · rw [AddMonoidHom.mk'_apply, TWincl_smul, TWincl_smul,
      TWincl_act S.inclR u (S.gR g) hu, hz, hz, TWact_smul, hy, E.jD_act, map_pow, map_pow, map_pow,
      hu, smul_comm]
  · have key : ∀ v ∈ Submodule.span S.O
        {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y}, ∀ r : S.RA,
        ∃ w ∈ AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y},
          TWincl S.inclR T w = S.inclR r • S.inclR x ^ M0 • v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, y, hy, rfl⟩ := hv
        intro r
        refine ⟨(r * a) • z ⟨y, hy⟩, AddSubgroup.subset_closure ⟨_, _, rfl⟩, ?_⟩
        rw [TWincl_smul, hz, map_mul, mul_smul, smul_comm (S.inclR a)]
      | zero => intro r; exact ⟨0, zero_mem _, by simp⟩
      | add v v' _ _ ih ih' =>
        intro r
        obtain ⟨w, hw, e⟩ := ih r
        obtain ⟨w', hw', e'⟩ := ih' r
        exact ⟨w + w', add_mem hw hw', by rw [map_add, e, e', smul_add, smul_add]⟩
      | smul c v _ ih =>
        intro r
        obtain ⟨w, hw, e⟩ := ih (r * algebraMap S.O S.RA c)
        refine ⟨w, hw, ?_⟩
        rw [e, map_mul, AlgHom.commutes, mul_smul, ← algebraMap_smul S.RW c v,
          smul_comm (S.inclR x ^ M0)]
    obtain ⟨w, hw, e⟩ := key _ (h2 t) 1
    have : x ^ (M0 + h0) • ((1 : S.RA) ⊗ₜ[S.O] t) = w := by
      apply hi
      rw [e, TWincl_smul, TWincl_one_tmul, map_one, one_smul, map_pow, pow_add, mul_smul]
    rw [this]
    exact hw

theorem γD_iterate (g : S.W.Gam) (k : ℕ) (y : S.W.DD T) :
    (S.W.γD T g)^[k] y = S.W.γD T (g ^ k) y := by
  induction k with
  | zero => simp [S.W.γD_one]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', S.W.γD_mul]

theorem γD_pow_sub (l : ℕ) [Fact l.Prime] (g : S.W.Gam)
    (hN : ∀ x ∈ N, S.W.γD T g x ∈ N)
    (hπ : ∀ x ∈ N, S.W.γD T g x - x ∈ (Ideal.span {(letπ : LetA S.O S.n)}) • N)
    (hA : ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ k,
      S.W.γA g a - a ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (k + 1))
    (j : ℕ) (y : ↥N) :
    ∃ y' : ↥N, (y' : S.W.DD T) = S.W.γD T (g ^ l ^ (j + 1)) y ∧
      y' - y ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n) ^ 2} ⊔
        (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (l ^ j)) • (⊤ : Submodule (LetA S.O S.n) ↥N) := by
  let Y : ↥N →+ ↥N := AddMonoidHom.mk' (fun x => ⟨S.W.γD T g x, hN x x.2⟩)
    (fun x x' => Subtype.ext (by simp))
  have hY : ∀ k (x : ↥N), ((Y^[k] x : ↥N) : S.W.DD T) = (S.W.γD T g)^[k] x := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  refine ⟨Y^[l ^ (j + 1)] y, by rw [hY, γD_iterate], ?_⟩
  refine GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration l (LetA S.O S.n) ↥N _ (S.W.γA g).toRingHom Y
    (fun a x => Subtype.ext (γD_smulA S T g a x)) hA (fun x => ?_) (j + 1) (by omega) y
  rw [Submodule.mem_smul_top_iff]
  exact Submodule.smul_mono_left (Ideal.span_mono (by simp)) (hπ x x.2)

theorem one_add_X : 1 + S.W.X = (1 + letπ) ^ (S.PD.p ^ (S.W.s - 1)) := by
  have h1 : S.W.φA (1 + letπ) = (1 + letπ) ^ S.PD.p := by
    rw [map_add, map_one, S.W.φA_π]
    funext i
    simp [letπ, LocWach.q, S.W.q₀_def]
  have h2 : ∀ k, (S.W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (S.PD.p ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgHom.mul_apply, h1, map_pow, ih, ← pow_mul, pow_succ]
  rw [← h2, map_add, map_one]
  rfl

theorem γA_letE (g : S.W.Gam) (i : ZMod S.n) : S.W.γA g (letE i) = letE i := by
  funext j
  change S.W.γ₀ g (letE (O := S.O) i j) = letE (O := S.O) i j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

end Lift

section Assemble

variable {l : ℕ} [Fact l.Prime]

theorem assemble (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (K LL : FinExt l) (m d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l))
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (R N ι : Type) [CommRing R] [AddCommGroup N]
    [Module R N] [Fintype ι] (b : Module.Basis ι R N) (e : Fin d ≃ Fin f × ι) (α : ↥(OL LL) → R)
    (φ : R →+* OCO LL) (Ψ : N →+ (Fin d → PadicComplex l)) (J : Ideal R) (g : GQ l)
    (hact : IsActC act) (hgen : IsGen χ K m g)
    (hM1 : ∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m))
    (hM2 : ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ)
    (hM3 : ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ)
    (hΨ : ∀ a y, Ψ (a • y) = (lam o A (φ a)).mulVec (Ψ y))
    (hα : ∀ a, lam o A (φ (α a)) = A a)
    (hc : ∀ a k, kap o (φ a) k ∈ intC (Ks K m))
    (hs : ∀ a ∈ J, ∀ k, ‖kap o (φ a) k‖ < rho1 l)
    (hn : ∀ y i, ‖Ψ y i‖ ≤ 1)
    (hσ : ∀ σ ∈ Gj K m, ∀ y, ∃ y', Ψ y' = (M σ).mulVec (fun i => act σ (Ψ y i)))
    (hH : ∀ σ ∈ Hinf K, ∀ y, Ψ y = (M σ).mulVec (fun i => act σ (Ψ y i)))
    (hg : ∀ y, ∃ y', y' - y ∈ J • (⊤ : Submodule R N) ∧
      Ψ y' = (M g).mulVec (fun i => act g (Ψ y i)))
    (c u : PadicComplex l) (hu : ‖u‖ ≤ 1) (hcu : (l : PadicComplex l) = u * c)
    (hl : ∀ j, c • (Pi.single j 1 : Fin d → PadicComplex l) ∈
      AddSubgroup.closure {v | ∃ (x : OCO LL) (y : N), v = (lam o A x).mulVec (Ψ y)}) :
    ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l))
      (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec act χ K m M Dm U g ∧
      ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K m) := by
  classical
  let y₀ : Fin d → N := fun j => α (o (e j).1) • b (e j).2
  let D : Matrix (Fin d) (Fin d) (PadicComplex l) := Matrix.of fun i j => Ψ (y₀ j) i
  let co : N → Fin d → PadicComplex l := fun y j => kap o (φ (b.repr y (e j).2)) (e j).1
  have hA : ∀ a y, Ψ (α a • y) = (A a).mulVec (Ψ y) := fun a y => by rw [hΨ, hα]
  have core : ∀ y, Ψ y = D.mulVec (co y) := by
    intro y
    conv_lhs => rw [← b.sum_repr y, map_sum]
    have h1 : D.mulVec (co y) = ∑ j, co y j • Ψ (y₀ j) := by
      funext i
      simp [D, Matrix.mulVec, dotProduct, mul_comm]
    have h2 : ∑ j, co y j • Ψ (y₀ j) = ∑ p : Fin f × ι,
        kap o (φ (b.repr y p.2)) p.1 • Ψ (α (o p.1) • b p.2) :=
      Equiv.sum_comp e (fun p : Fin f × ι => kap o (φ (b.repr y p.2)) p.1 • Ψ (α (o p.1) • b p.2))
    rw [h1, h2, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΨ, lam, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, Matrix.smul_mulVec]
  have cols : ∀ (B : Matrix (Fin d) (Fin d) (PadicComplex l)) (v : Fin d → Fin d → PadicComplex l),
      (∀ j, (fun i => B i j) = D.mulVec (v j)) → B = D * Matrix.of fun i j => v j i := by
    intro B v h
    ext i j
    exact congrFun (h j) i
  have hball : ∀ v ∈ AddSubgroup.closure
      {v | ∃ (x : OCO LL) (y : N), v = (lam o A x).mulVec (Ψ y)},
      ∃ w : Fin d → PadicComplex l, (∀ i, ‖w i‖ ≤ 1) ∧ v = D.mulVec w := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨x, y, rfl⟩ := hv
      refine ⟨∑ k, kap o x k • co (α (o k) • y), fun i => ?_, ?_⟩
      · rw [Finset.sum_apply]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_one₀ (norm_kap_le _ _ _) (norm_nonneg _) (norm_kap_le _ _ _)
      · rw [lam, Matrix.sum_mulVec, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← core, hA]
    | zero => exact ⟨0, by simp, by simp⟩
    | add v v' _ _ ih ih' =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨w', hw', rfl⟩ := ih'
      exact ⟨w + w', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hw i) (hw' i)),
        (Matrix.mulVec_add _ _ _).symm⟩
    | neg v _ ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      exact ⟨-w, fun i => by simpa using hw i, (Matrix.mulVec_neg _ _).symm⟩
  have hcol : ∀ σ j, (fun i => (M σ * D.map (act σ)) i j) =
      (M σ).mulVec (fun i => act σ (Ψ (y₀ j) i)) := fun σ j => rfl
  obtain ⟨U, hU⟩ := GlobalTheory.T.decompletion_frame_of_matrix_form l act χ K m d M D g hact hgen hM1 hM2 hM3 (fun i j => hn _ _)
    (by
      choose w hw hw' using fun j => hball _ (hl j)
      refine ⟨Matrix.of fun i j => (u • w j) i, fun i j => ?_, (cols _ _ fun j => ?_).symm⟩
      · rw [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_one₀ hu (norm_nonneg _) (hw j i)
      · rw [Matrix.mulVec_smul, ← hw', smul_smul, ← hcu]
        funext i
        simp [Matrix.one_apply, Pi.single_apply])
    (fun σ hσ' => by
      choose y' hy' using fun j => hσ σ hσ' (y₀ j)
      exact ⟨Matrix.of fun i j => co (y' j) i, fun i j => hc _ _,
        cols _ _ fun j => by rw [hcol, ← hy', core]⟩)
    (fun σ hσ' => by
      ext i j
      exact (congrFun (hcol σ j) i).trans (congrFun (hH σ hσ' (y₀ j)).symm i))
    (by
      choose y' hy hy' using fun j => hg (y₀ j)
      refine ⟨Matrix.of fun i j => co (y' j - y₀ j) i, fun i j => hs _ ?_ _, cols _ _ fun j => ?_⟩
      · have := hy j
        generalize y' j - y₀ j = x at this
        refine Submodule.smul_induction_on this (fun r hr n _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
          exact J.mul_mem_right _ hr
        · rw [map_add, Finsupp.add_apply]
          exact J.add_mem hx hy
      · rw [← core, map_sub, hy', ← hcol]
        rfl)
  refine ⟨D, U, g, hU, fun a i j => ?_⟩
  have h1 : A a * D = D * Matrix.of fun i j => co (α a • y₀ j) i :=
    cols _ _ fun j => by rw [← core, hA]; rfl
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU.1, Matrix.one_mul]
  exact hc _ _

end Assemble

section Roots

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem zeta_pow (j k : ℕ) : AI.ζ (j + k) ^ l ^ k = AI.ζ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem zeta_prim (j : ℕ) (hj : 1 ≤ j) :
    IsPrimitiveRoot ((AI.ζ j : OC l) : PadicComplex l) (l ^ j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hnot : ¬ AI.ζ (1 + i) ^ l ^ i = 1 := by rw [zeta_pow]; exact AI.ζ_one
  have hfin : AI.ζ (1 + i) ^ l ^ (i + 1) = 1 := by
    rw [pow_succ, pow_mul, zeta_pow, AI.ζ_succ 0, AI.ζ_zero]
  have h := IsPrimitiveRoot.orderOf (AI.ζ (1 + i))
  rw [orderOf_eq_prime_pow hnot hfin, add_comm i 1] at h
  exact h.map_of_injective (f := (PadicComplexInt l).subtype) Subtype.val_injective

include AI in
theorem zetaQ_mem (K : FinExt l) {j m : ℕ} (hj : j ≤ m) : P.ζQ j ∈ Ks K m := by
  refine AlmostTrace.Ks_mono K hj ?_
  refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
  change P.ζQ j ^ l ^ j = 1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  have h := congrArg (fun x : OC l => (x : PadicComplex l)) (zeta_pow AI 0 j)
  rw [map_pow, map_one, ← PadicComplex.coe_eq, ← AI.ζ_eq]
  simpa [AI.ζ_zero] using h

theorem act_zeta (K : FinExt l) {j m : ℕ} (hj : j ≤ m) (σ : GQ l) (hσ : σ ∈ Gj K m) :
    AI.actC σ ((AI.ζ j : OC l) : PadicComplex l) = ((AI.ζ j : OC l) : PadicComplex l) := by
  rw [AI.ζ_eq, AI.actC_ext]
  exact congrArg _ (hσ ⟨_, zetaQ_mem AI K hj⟩)

theorem zeta_sub_one_mem (K : FinExt l) {j m : ℕ} (hj : j ≤ m) :
    ((AI.ζ j - 1 : OC l) : PadicComplex l) ∈ inC (Ks K m) := by
  refine ⟨P.ζQ j - 1, sub_mem (zetaQ_mem AI K hj) (one_mem _), ?_⟩
  change algebraMap (Om l) (PadicComplex l) (P.ζQ j - 1) = ((AI.ζ j : OC l) : PadicComplex l) - 1
  rw [map_sub, map_one, AI.ζ_eq]
  rfl

theorem norm_zeta_sub_one_lt (j : ℕ) (hj : 1 ≤ j) :
    ‖((AI.ζ j - 1 : OC l) : PadicComplex l)‖ < 1 := by
  change ‖((AI.ζ j : OC l) : PadicComplex l) - 1‖ < 1
  rw [GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj _ (zeta_prim AI j hj)]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  apply Real.rpow_lt_one_of_one_lt_of_neg hl
  apply div_neg_of_neg_of_pos (by norm_num)
  exact mul_pos (pow_pos (by linarith) _) (by linarith)

theorem tmul_one_pow (LL : FinExt l) (c : OC l) (k : ℕ) :
    (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) : OCO LL) ^ k = (c ^ k) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow]

theorem one_add_pow_sub (LL : FinExt l) (w : Ainf l) (k : ℕ) :
    (1 + ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w - 1) : RA LL)) ^ k =
      1 + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ k - 1) := by
  have h : ∀ v : Ainf l, (1 + ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (v - 1) : RA LL)) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] v := fun v => by
    rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel]
  rw [h, h, Algebra.TensorProduct.tmul_pow, one_pow]

end Roots

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem exists_decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec (D.locA l).actC (D.loc l).χQ K (mN l s (M0 + h0)) M Dm U g ∧ ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K (mN l s (M0 + h0))) := by
  intro D HW F l _ K s LL h S E T M0 h0 hW d M A hM
  obtain ⟨-, -, N, hN⟩ := hW
  obtain ⟨hsw1, hsw2⟩ := GlobalTheory.T.wach_lattice_sandwich_Ainf D HW F l K s LL h T M0 h0 N hN
  obtain ⟨⟨ι, _, b, hli, hsp⟩, -, -, hW2, hW3, -⟩ := hN
  obtain ⟨f, o, ⟨e⟩⟩ := GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis l K LL T d M A ι _ hM hli hsp
  generalize hn : n0 l (M0 + h0) = n
  have hm : mN l s (M0 + h0) = s + (s + n + 1) := by rw [mN, hn]; ring
  generalize mN l s (M0 + h0) = m at hm ⊢
  have hs1 : 1 ≤ s := h.1
  let AI := D.locA l
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hcyc : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_fontaineTheta_frobeniusInverse_shift l (D.loc l) AI n
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := GlobalTheory.T.exists_ainf_tensor_lattice_specialisation l (D.loc l) AI K LL T d f n M A o θ hM hθ
  obtain ⟨hl1, hA1, -, -⟩ := GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative l K LL T d f M A o hM
  obtain ⟨hM1, hM2, -, -⟩ := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).2 d M A hM
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_lift S E T N (E.io S.W.X) M0 h0 (inclR_injective LL) hsw1 hsw2
  have hgrp := GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups l (D.loc l) AI K s LL h ((HW l).W K s LL h) ((HW l).W_s K s LL h)
  have hGs : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_antitone h.2.2.1
  have hms : Gj K m ≤ Gj K s :=
    IntermediateField.fixingSubgroup_antitone (AlmostTrace.Ks_mono K (by omega))
  obtain ⟨⟨g₀, hg₀⟩, hgen⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l AI.actC (D.loc l).χQ hact hcyc K s ⟨h.1, h.2.1⟩
  have hg := (hgen g₀ hg₀).1 (s + n + 1)
  rw [← hm] at hg
  let φ : LetA S.O S.n →+* OCO LL := (thR LL θ).comp E.io.toRingHom
  have hφ : ∀ a, φ a = thR LL θ (E.io a) := fun a => rfl
  have hφa : ∀ a : ↥(OL LL), φ (algebraMap S.O (LetA S.O S.n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
    intro a
    exact (congrArg (thR LL θ) (E.io.commutes a)).trans ((thR_tmul LL θ a 1).trans (by rw [map_one]))
  have hφπ : φ letπ = (AI.ζ (s + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [hφ, E.io_π]
    exact (thR_tmul LL θ 1 _).trans (by rw [map_sub, map_one, hθ.2])
  let w : Ainf l := WittVector.teichmuller l (AI.εroot s) ^ l ^ (s - 1) - 1
  have hx : E.io S.W.X = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL) := by
    have h1 := congrArg E.io (one_add_X S)
    have h2 : S.PD.p = l := (D.loc l).PD_p K
    have h3 : S.W.s = s := (HW l).W_s K s LL h
    rw [map_add, map_one, map_pow, map_add, map_one, E.io_π, h2, h3] at h1
    exact add_left_cancel (h1.trans (one_add_pow_sub LL _ _))
  have hθw : θ w = AI.ζ (1 + n) - 1 := by
    rw [map_sub, map_one, map_pow, hθ.2, show s + n = (1 + n) + (s - 1) by omega, zeta_pow]
  let c : PadicComplex l := ((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1
  have hprim := zeta_prim AI (1 + n) (by omega)
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' l (M0 + h0) _ (by rw [hn]; exact hprim)
  have hc0 : c ≠ 0 := sub_ne_zero.2 (hprim.ne_one
    (Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt))
  have hsc : ∀ (r : RA LL) (k : ℕ) (v : TW (RA LL) (show LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) from T)),
      thR LL θ r = (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → Φ (r ^ k • v) = c ^ k • Φ v := by
    intro r k v hr
    rw [hΦ1, map_pow, hr, tmul_one_pow, hl1, hA1, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  let x : RA LL := E.io S.W.X
  have hx' : x = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w := hx
  have hx1 : thR LL θ x = (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [hx', thR_tmul, hθw]
  have hx2 : ∀ σ ∈ Gj K m, thR LL θ (gRA AI LL σ x) =
      (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    intro σ hσ
    have h1 : θ (AI.actWHom σ w) = AI.ζ (1 + n) - 1 := by
      apply Subtype.ext
      rw [hθ.1, hθw]
      change AI.actC σ (((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1) =
        ((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1
      rw [map_sub, map_one, act_zeta AI K (by omega) σ hσ]
    rw [hx', ← h1]
    rfl
  let Ψ : ↥N →+ (Fin d → PadicComplex l) := Φ.comp z
  have hΨ : ∀ y, Ψ y = Φ (z y) := fun y => rfl
  have hmain : ∀ (σ : ↥(GK K)), (σ : GQ l) ∈ Gj K m → ∀ y y' : ↥N,
      (y' : S.W.DD T) = S.W.γD T (S.W.resΓ σ) y →
      Ψ y' = (M σ).mulVec (fun i => AI.actC σ (Ψ y i)) := by
    intro σ hσ y y' hy
    have h1 := congrArg Φ (hz2 σ (gRA AI LL σ) (inclR_gRA AI LL σ) y y' hy)
    have h2 := (hsc _ M0 _ hx1).symm.trans (h1.trans (hsc _ M0 _ (hx2 σ hσ)))
    have h3 := smul_right_injective (Fin d → PadicComplex l) (pow_ne_zero M0 hc0) h2
    exact h3.symm.trans (hΦ3 σ (z y))
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    haveI := K.2
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hidem : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m) := by
    intro i k
    have h1 : IsIdempotentElem (letE i : LetA S.O S.n) := by
      change letE i * letE i = letE i
      rw [letE, ← Pi.single_mul, mul_one]
    have h2 := GlobalTheory.T.kap_mem_inC_of_invariant l AI.actC K LL f o (φ (letE i)) hact (h1.map φ) (fun σ hσ k => by
      have h3 := GlobalTheory.T.io_equivariant_alt l (D.loc l) AI K s LL h _ ((F l).E K s LL h) ⟨σ, hσ⟩ (letE i)
      let r : RA LL := E.io (letE i)
      have h4 : gRA AI LL σ r = r := by
        apply inclR_injective LL
        rw [inclR_gRA]
        exact h3.symm.trans (congrArg (fun a => inclR LL (E.io a)) (γA_letE S _ i))
      exact (kap_thR_gRA AI o hθ σ _ k).symm.trans
        (congrArg (fun r => kap o (thR LL θ r) k) h4)) k
    exact Set.image_mono (h.2.2.1.trans (AlmostTrace.Ks_mono K (show s ≤ m by omega))) h2
  refine assemble AI.actC (D.loc l).χQ K LL m d f M A o (LetA S.O S.n) ↥N ι b e
    (algebraMap S.O (LetA S.O S.n)) φ Ψ
    (Ideal.span {((l : ℕ) : LetA S.O S.n) ^ 2} ⊔
      (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (l ^ (s + n))) (g₀ ^ l ^ (s + n + 1)) hact hg
    (fun i j => (hM1 i j).mono fun σ hσ => hGs (hms hσ))
    (fun σ hσ τ hτ => hM2 σ (hGs (hms hσ)) τ (hGs (hms hτ))) (fun σ _ τ hτ => ?_)
    (fun a y => ?_) (fun a => ?_)
    (GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries l K LL m (Module.finrank ℚ_[l] ↥(K0 K)) f o φ _ hφa hφπ (norm_zeta_sub_one_lt AI _ (by omega))
      (zeta_sub_one_mem AI K (by omega)) hidem)
    (GlobalTheory.T.norm_lt_rho1_of_mem_ideal_power l LL (s + n) _ f o φ _ (by omega) (zeta_prim AI _ (by omega)) hφπ)
    (fun y i => hΦ2 _ i) (fun σ hσ y => ?_) (fun σ hσ y => ?_) (fun y => ?_)
    (c ^ (M0 + h0)) u hu hlu (fun j => ?_)
  · obtain ⟨b', hb', -⟩ := hM
    ext i j
    have := hb' ⟨τ, hGs (hms hτ)⟩ i j
    rw [Matrix.map_apply]
    exact (congrArg _ this).trans ((act_zC hact σ _).trans this.symm)
  · exact (congrArg Φ (hz1 a y)).trans (hΦ1 _ _)
  · rw [hφa, hl1]
    exact one_smul _ _
  · exact ⟨⟨_, hW2 ⟨σ, hGs (hms hσ)⟩ ((hgrp _).1 (hms hσ)) y y.2⟩, hmain ⟨σ, hGs (hms hσ)⟩ hσ y _ rfl⟩
  · have hσ' := AlmostTrace.Hinf_le_Gj K m hσ
    refine hmain ⟨σ, hGs (hms hσ')⟩ hσ' y y ?_
    have h1 : S.W.resΓ ⟨σ, hGs (hms hσ')⟩ = 1 := (hgrp _).2 hσ
    rw [h1, S.W.γD_one]
  · have h1 : (⟨g₀, hGs hg₀.1⟩ : ↥(GK K)) ∈ S.W.GKs := (hgrp _).1 hg₀.1
    obtain ⟨y', hy', hy''⟩ := γD_pow_sub S T N l (S.W.resΓ ⟨g₀, hGs hg₀.1⟩) (hW2 _ h1) (hW3 _ h1)
      (GlobalTheory.T.gammaAction_sub_mem_span_pow_succ D HW l K s LL h _ h1) (s + n) y
    refine ⟨y', hy'', hmain ((⟨g₀, hGs hg₀.1⟩ : ↥(GK K)) ^ l ^ (s + n + 1)) hg.1 y y' ?_⟩
    exact hy'.trans (congrArg (fun γ => S.W.γD T γ y) (S.W.resΓ.map_pow _ _).symm)
  · obtain ⟨t, ht⟩ := hΦ4 j
    rw [← ht, ← hsc _ _ _ hx1]
    have h1 : ∀ v ∈ AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y},
        Φ v ∈ AddSubgroup.closure
          {v | ∃ (x : OCO LL) (y : ↥N), v = (lam o A x).mulVec (Ψ y)} := by
      intro v hv
      induction hv using AddSubgroup.closure_induction with
      | mem v hv =>
        obtain ⟨r, y, rfl⟩ := hv
        exact AddSubgroup.subset_closure ⟨thR LL θ r, y, hΦ1 r (z y)⟩
      | zero => exact (Φ.map_zero).symm ▸ zero_mem _
      | add v v' _ _ ih ih' => exact (Φ.map_add v v').symm ▸ add_mem ih ih'
      | neg v _ ih => exact (Φ.map_neg v).symm ▸ neg_mem ih
    exact h1 _ (hz3 t)

end GlobalTheory.Cyc.Decomp
