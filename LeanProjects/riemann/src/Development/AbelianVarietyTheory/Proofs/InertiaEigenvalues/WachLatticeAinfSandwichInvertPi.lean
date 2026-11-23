import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystallineStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL Module

noncomputable section

namespace GlobalTheory.HWL.SandProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA} {Zl : Type} [CommRing Zl] {zl : PowerSeries Zl →+* LetA O n}

theorem jD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.jD T (a • y) = inclR (I.io a) • E.jD T y := by
  rw [← algebraMap_smul R.EE a y, E.jD_smul, I.ioE_ext]

theorem φD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.φD T (a • y) = letφ R.φ₀ a • E.φD T y := by
  rw [← algebraMap_smul R.EE a y, E.φD_smul, R.φE_ext, algebraMap_smul]

theorem φA_π (R : WSer Γ) : letφ (n := n) R.φ₀ letπ = letπ * (fun _ => R.q₀) := by
  funext i
  exact R.φ₀_X

theorem φA_one_add_π (R : WSer Γ) : letφ (n := n) R.φ₀ (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add, map_one, φA_π]
  funext i
  have := R.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ]
  rw [this]; ring

theorem φA_pow_one_add_π (R : WSer Γ) (k : ℕ) :
    (letφ (n := n) R.φ₀ ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add_π, ← pow_mul, pow_succ']

theorem frobenius_inclusion_X_eq_mul_Q (I : WIo R RA RW inclR φR gR πA)
    (hu : φR (inclR (1 + πA)) = inclR (1 + πA) ^ PD.p) :
    φR (inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1)) =
      inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1) * inclR (I.io R.Q) := by
  have hX : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ = (1 + letπ) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [← φA_pow_one_add_π R, map_add, map_one]; ring
  have hXQ : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ * R.Q =
      ((1 + letπ) ^ PD.p) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [WSer.Q, ← map_mul, ← φA_π, ← pow_mul, mul_comm PD.p, pow_mul,
      ← φA_pow_one_add_π R, ← map_pow, ← φA_one_add_π R, map_add, map_one, map_add, map_one]
    ring
  have hπ : I.io (1 + letπ) = 1 + πA := by rw [map_add, map_one, I.io_π]
  have h1 : (1 + πA) ^ (PD.p ^ (s - 1)) - 1 = I.io ((letφ (n := n) R.φ₀ ^ (s - 1)) letπ) := by
    rw [hX, map_sub, map_pow, map_one, hπ]
  conv_rhs => rw [h1, ← map_mul, ← map_mul, hXQ]
  simp only [map_sub, map_pow, map_one, hπ, hu]

theorem uniform {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (q : A)
    (S : Submodule A M) (w : ι → M) (h : ∀ i, ∃ k : ℕ, q ^ k • w i ∈ S) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i, q ^ k • w i ∈ S := by
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun m hm i => ?_⟩
  have : k i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le this
  rw [add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk i)

theorem sand_of {E : WEt I} (Mo : WN E zl)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (x : RA) (hx : φR (inclR x) = inclR x * inclR (I.io R.Q)) [Nontrivial O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(Mo.N T)) :
    ∃ m : ℕ, Sand Mo T (x ^ m) := by
  classical
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ Mo.N T, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : E.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg (Mo.N T).subtype (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → E.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (I.io (c j)) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : E.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine (Mo.N_base T hT).inductionOn y
      (fun y => E.jD T y ∈ Submodule.span RW (Set.range fun i => E.jD T (b i : E.DD T))) ?_ ?_ ?_ ?_
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro z
      obtain ⟨c, hc⟩ := hexp z.1 z.2
      change E.jD T z.1 ∈ _
      rw [hc, hj]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro e z hz
      rw [E.jD_smul]
      exact Submodule.smul_mem _ _ hz
    · intro z z' hz hz'
      rw [map_add]
      exact Submodule.add_mem _ hz hz'
  have hli : LinearIndependent RW fun i => E.jD T (b i : E.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  obtain ⟨k₁, h1⟩ := uniform R.Q (Mo.N T) (fun i => E.φD T (b i : E.DD T))
    (fun i => Mo.N_φ T _ (b i).2)
  obtain ⟨k₂, h2⟩ := uniform R.Q (Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))))
    (fun i => (b i : E.DD T)) (fun i => Mo.N_φinv T _ (b i).2)
  replace h1 := h1 (max k₁ k₂) (le_max_left _ _)
  replace h2 := h2 (max k₁ k₂) (le_max_right _ _)
  refine ⟨max k₁ k₂, ?_⟩
  generalize max k₁ k₂ = m at h1 h2
  unfold Sand
  rw [map_pow]
  constructor
  · choose P hP using fun i => hexp _ (h1 i)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx m (fun i => E.jD T (b i : E.DD T))
      (Matrix.of fun i j => I.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    change _ ∈ LinearMap.range (TWincl inclR T)
    rw [hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))),
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • E.φD T (b j : E.DD T) := by
      intro y hy
      have : Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))) ≤ Submodule.span (LetA O n)
          (Set.range fun j => E.φD T (b j : E.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (h2 i)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : E.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx m nb
      (Matrix.of fun i j => I.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
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

end Generic

theorem εroot_pow_pred {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) :
    AI.εroot (k + 1) ^ l ^ k = AI.ε1 := by
  induction k with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem x_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ)
    (hs : 1 ≤ s) :
    ((1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ (l ^ (s - 1)) - 1 =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have h : (1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) - 1) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) : Ainf l) := by
    rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]; abel
  rw [h, Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, Nat.add_sub_cancel, εroot_pow_pred,
    LocAinf.π₁, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]

set_option maxHeartbeats 1600000 in

theorem sandwich : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  intro l _ P AI K s LL hg Γ R I hI E Mo T hT
  obtain ⟨b⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hg Γ R I hI E Mo T hT
  have hp : (P.PD K).p = l := P.PD_p K
  have hx := frobenius_inclusion_X_eq_mul_Q I (by rw [hp]; exact GlobalTheory.Sandwich.φRW_teichmuller LL _)
  rw [hp, x_eq AI LL s Γ.s_pos] at hx
  obtain ⟨m, hm⟩ := sand_of Mo (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) _ hx T hT b
  refine ⟨m, ?_⟩
  have e : ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ : RA LL) ^ m := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e]
  exact hm

end GlobalTheory.HWL.SandProof
