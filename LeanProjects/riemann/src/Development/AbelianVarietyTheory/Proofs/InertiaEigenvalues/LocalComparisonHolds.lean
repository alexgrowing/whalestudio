import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices Module

noncomputable section

namespace GlobalTheory.NL.SandJumps

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
    (y : W.DD T) : E.jD T (a • y) = inclR (E.io a) • E.jD T y := by
  rw [← algebraMap_smul W.EE a y, E.jD_smul, E.ioE_ext]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = letφ W.φ₀ a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem NAinf_smul (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : RA)
    (z : TW RW T) (hz : z ∈ NAinf W E T) : inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨a * a', y, hy, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add z z' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul c z _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1

set_option maxHeartbeats 1000000 in

theorem sand_exps [Nontrivial O] (E : EtTie W RA RW inclR φR gR πA)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hx : φR (inclR (E.io W.X)) = inclR (E.io W.X) * inclR (E.io W.Q))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) (M h : ℕ)
    (hM : ∀ x ∈ W.N T, W.Q ^ M • W.φD T x ∈ W.N T)
    (hh : ∀ y ∈ W.N T, W.Q ^ h • y ∈
      Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    wachInfiniteLevelJumpBound W E T M h := by
  classical
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ W.N T, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg (W.N T).subtype (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (E.io (c j)) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine (W.N_base T hT).inductionOn y
      (fun y => E.jD T y ∈ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T))) ?_ ?_ ?_ ?_
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
  have hli : LinearIndependent RW fun i => E.jD T (b i : W.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  constructor
  ·
    have hexp2 : ∀ y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • W.φD T (b j : W.DD T) := by
      intro y hy
      have : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ Submodule.span (LetA O n)
          (Set.range fun j => W.φD T (b j : W.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (hh _ (b i).2)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : W.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx h nb
      (Matrix.of fun i j => E.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    have h1t : ∀ t : ↥T.L.T, inclR (E.io W.X) ^ h • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈ NAinf W E T := by
      intro t
      rw [← tb.sum_repr t, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [TensorProduct.tmul_smul, smul_comm]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨c, hc⟩ := hlow k
      rw [hc]
      refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, b j, (b j).2, ?_⟩
      rw [hnb]
    rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | tmul a t =>
      have e : TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (a ⊗ₜ[O] t) =
          inclR a • ((1 : RW) ⊗ₜ[O] t : TW RW T) := by
        rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
      change _ • TensorProduct.map inclR.toLinearMap LinearMap.id (a ⊗ₜ[O] t) ∈ _
      rw [e, smul_comm]
      exact NAinf_smul E T a _ (h1t t)
    | add w w' h1 h2 =>
      rw [map_add, smul_add]; exact Submodule.add_mem _ h1 h2
  ·
    choose P hP using fun i => hexp _ (hM _ (b i).2)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx M (fun i => E.jD T (b i : W.DD T))
      (Matrix.of fun i j => E.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, hy, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := hexp y hy
      rw [smul_comm, hj, Finset.smul_sum]
      refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (Submodule.sum_mem _ fun j _ => ?_)
      rw [smul_comm]
      exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add z z' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul c z _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem smul_mem_Nl (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i :=
  ⟨x, hx, rfl⟩

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨y, hy, rfl⟩
  exact (W.N T).smul_mem (letE i : LetA O n) hy

theorem decomp [NeZero n] (T : LocLat G Qp LL O) (x : W.DD T) :
    x = ∑ j : ZMod n, (letE j : LetA O n) • x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem le_mx [NeZero n] (M : ZMod n → ℕ) (i : ZMod n) : M i ≤ mx M :=
  le_ciSup (Set.finite_range M).bddAbove i

theorem upper_exp [NeZero n] (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hp : p5 W T M h) :
    ∀ x ∈ W.N T, W.Q ^ mx M • W.φD T x ∈ W.N T := by
  intro x hx
  rw [decomp T x, map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := hp.1 (j + 1) _ (by rw [add_sub_cancel_right]; exact smul_mem_Nl T j x hx)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_mx M (j + 1))
  rw [hd, add_comm, pow_add, mul_smul]
  exact (W.N T).smul_mem _ h1

theorem lower_exp [NeZero n] (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hp : p5 W T M h) :
    ∀ y ∈ W.N T, W.Q ^ mx h • y ∈
      Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) := by
  intro y hy
  rw [decomp T y, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := hp.2.1 j _ (smul_mem_Nl T j y hy)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_mx h j)
  rw [hd, add_comm, pow_add, mul_smul]
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.span_mono (Set.image_mono (Nl_le T (j - 1))) h1

theorem φA_X (W : LocWach PD LL O v n) : W.φA W.X = W.X * W.Q := by
  have h1 : W.φA letπ = letπ * W.q := by
    funext i
    exact W.φ₀_X
  have h2 := DFunLike.congr_fun ((Commute.refl W.φA).pow_right (W.s - 1)).eq letπ
  simp only [AlgHom.mul_apply] at h2
  unfold LocWach.X LocWach.Q
  rw [h2, h1, map_mul]

end Generic

end GlobalTheory.NL.SandJumps

namespace GlobalTheory.NL.SandJumps

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hJ
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp : p5 ((HW l).W K s LL h) T M hh := GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h T M hh hT hJ
  obtain ⟨b⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hio := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  obtain ⟨-, -, -, -, hφ, -⟩ := hio
  have hx : φRW LL (inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X)) =
      inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X) *
        inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).Q) := by
    rw [← hφ, φA_X, map_mul, map_mul]
  exact sand_exps _ (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) hx T hT b _ _
    (upper_exp T M hh hp) (lower_exp T M hh hp)

end GlobalTheory.NL.SandJumps
