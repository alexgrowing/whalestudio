import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensityStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.GamModX

theorem full_of_std {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem shift_mem {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) (e y : ℤ → M) (he : e ∈ Λ) (u : L)
    (hy : ∀ k : ℤ, y k = u ^ k • e k - e k) :
    ∃ f ∈ Λ, ∀ j : ℤ, y j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h e).1 he
  refine ⟨fun k => y (k + 1), (h _).2 ⟨fun k => ?_, fun k hk => ?_⟩, fun j => by simp⟩
  · rw [hy]; exact D.sub_mem (D.smul_mem _ (h1 _)) (h1 _)
  · rw [hy]
    rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
    · simp [h2 _ h3]
    · simp [h3]

theorem conv_one {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : ℤ → M) :
    conv (1 : PowerSeries L) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem exists_smul_of_dvd_repr {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Fintype ι] (N : Submodule A M) (nb : Module.Basis ι A ↥N) (a : A) (z : ↥N)
    (hz : ∀ j, a ^ 1 ∣ nb.repr z j) : ∃ y ∈ N, (z : M) = a • y := by
  choose c hc using hz
  refine ⟨((∑ j, c j • nb j : ↥N) : M), Subtype.property _, ?_⟩
  have key : z = a • ∑ j, c j • nb j := by
    conv_lhs => rw [← nb.sum_repr z]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j, pow_one, mul_smul]
  exact congrArg Subtype.val key

set_option maxHeartbeats 1000000 in

theorem ex_of_val {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (m : ℕ)
    (hζ : ζ ^ (l ^ m) = 1) (g : (H.W K s LL h).Gam)
    (hg : (m : WithTop ℚ) ≤
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL)) - 1))
    (x : ↥((H.W K s LL h).N T)) (k : ℤ) :
    ex C h T i ζ ⟨_, (H.W K s LL h).N_Γ T g x x.2⟩ k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL))) ^ k • ex C h T i ζ x k := by
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
  have hjs : (j : WithTop ℚ) ≤ (m : WithTop ℚ) := by exact_mod_cast hj
  exact (C.C K s LL h).tie.levB_Γ T hT g i ζ ζ j 1
    (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ)
    (by rw [Nat.cast_one]; exact hjs.trans hg) (pow_one ζ).symm x
    ((H.W K s LL h).N_Γ T g x x.2) k

set_option maxHeartbeats 1000000 in

theorem sub_mem_X_of_val : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ g : W.Gam,
      ((s - 1 : ℕ) : WithTop ℚ) ≤
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) →
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT g hg x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  let x' : ↥(W.N T) := ⟨x, hx⟩
  let g' : ↥(W.N T) := ⟨_, W.N_Γ T g x hx⟩
  refine exists_smul_of_dvd_repr (W.N T) nb W.X (g' - x') fun j => ?_
  refine (GlobalTheory.T.wachWeierstrass_test_and_density D HW l K s LL h).2.1 1 _ fun i ζ hζ => ?_
  have hS := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT i ζ hζ
  have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    obtain ⟨j, -, hord⟩ :=
      (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
    exact ⟨j, hord ▸ IsPrimitiveRoot.orderOf ζ⟩
  have hI := (GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ hprim (full_of_std hS)).2 _ nb
  refine (hI.2.2 (g' - x') 1).1 ?_ j
  refine shift_mem hS (ex (Cm l) h T i ζ x') _ ?_
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) fun k => ?_
  · exact Submodule.subset_span ⟨1, x', (conv_one _).symm⟩
  · rw [← ex_of_val (Cm l) h T hT i ζ (s - 1) hζ g hg x' k]
    unfold ex
    rw [map_sub]
    rfl

set_option maxHeartbeats 1000000 in

theorem gam_mod_π_mod_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
      (∀ g : W.Gam, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
      (∀ g : W.Gam, ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = (letπ : AA K LL) • y) ∧
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T W.gam x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT
  refine ⟨W.N_Γ T, W.N_π T, sub_mem_X_of_val D HW F Cm l K s LL h T hT W.gam ?_⟩
  have hg := W.gam_gen
  rw [(HW l).W_s] at hg
  have hs : ((s - 1 : ℕ) : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast Nat.sub_le s 1
  exact hs.trans hg.ge

end GlobalTheory.NL.GamModX
