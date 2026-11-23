import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.NL.LevInj

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_C (s : L) (f : ℤ → M) : conv (PowerSeries.C s) f = s • f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_C, if_neg hj, zero_smul]

theorem conv_X_pow (n : ℕ) (f : ℤ → M) (k : ℤ) :
    conv ((PowerSeries.X : PowerSeries L) ^ n) f k = f (k - n) := by
  unfold conv
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_X_pow, if_neg hj, zero_smul]

theorem conv_single (e : PowerSeries L) (m : ℤ) (d : M) (n : ℕ) :
    conv e (Pi.single m d) (m + n) = PowerSeries.coeff n e • d := by
  unfold conv
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rw [Pi.single_eq_of_ne (by omega), smul_zero]

theorem coeff_smul_hahn (e : PowerSeries L) (y : HahnModule ℤ L M) :
    ((HahnModule.of L).symm ((HahnSeries.ofPowerSeries ℤ L e) • y)).coeff =
      conv e ((HahnModule.of L).symm y).coeff := by
  classical
  funext k
  unfold conv
  rw [HahnModule.coeff_smul]
  set S := Finset.VAddAntidiagonal k (Set.VAddAntidiagonal.finite_of_isPWO
    (HahnSeries.ofPowerSeries ℤ L e).isPWO_support ((HahnModule.of L).symm y).isPWO_support k) with hS
  have hneg : ∀ a : ℤ, (HahnSeries.ofPowerSeries ℤ L e).coeff a ≠ 0 → ∃ n : ℕ, a = n := by
    intro a ha
    by_contra hc
    apply ha
    rw [PowerSeries.coeff_coe, if_pos]
    by_contra h
    exact hc ⟨a.toNat, by omega⟩
  have hco : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℤ L e).coeff (n : ℤ) = PowerSeries.coeff n e :=
    fun n => LaurentSeries.coeff_coe_powerSeries e n
  rw [finsum_eq_sum_of_support_subset (s := S.image fun ij => ij.1.toNat), Finset.sum_image]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [hS, Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, -, h3⟩ := hij
    obtain ⟨n, hn⟩ := hneg _ h1
    have : ij.2 = k - n := by rw [← h3, hn]; simp
    rw [hn, this, hco, Int.toNat_natCast]
  · intro a ha b hb hab
    rw [hS, Finset.mem_coe, Finset.mem_vaddAntidiagonal] at ha hb
    obtain ⟨n, hn⟩ := hneg _ ha.1
    obtain ⟨n', hn'⟩ := hneg _ hb.1
    have h1 := ha.2.2
    have h2 := hb.2.2
    simp only [vadd_eq_add] at h1 h2 hab
    exact Prod.ext (by omega) (by omega)
  · intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_image]
    refine ⟨((j : ℤ), k - j), ?_, by simp⟩
    rw [hS, Finset.mem_coe, Finset.mem_vaddAntidiagonal]
    refine ⟨?_, ?_, by simp⟩
    · rw [HahnSeries.mem_support, hco]
      exact left_ne_zero_of_smul hj
    · rw [HahnSeries.mem_support]
      exact right_ne_zero_of_smul hj

theorem indep_of_span {R H : Type} [CommRing R] [Nontrivial R] [AddCommGroup H] [Module R H] {r : ℕ}
    (u y : Fin r → H) (hy : LinearIndependent R y) (hm : ∀ a, y a ∈ Submodule.span R (Set.range u)) :
    LinearIndependent R u := by
  rw [linearIndependent_iff_card_le_finrank_span]
  haveI : Module.Finite R ↥(Submodule.span R (Set.range u)) :=
    Module.Finite.span_of_finite R (Set.finite_range u)
  have : LinearIndependent R (fun a => (⟨y a, hm a⟩ : ↥(Submodule.span R (Set.range u)))) :=
    LinearIndependent.of_comp (Submodule.subtype _) hy
  exact this.fintype_card_le_finrank

theorem core {H A N : Type} [AddCommGroup H] [Module (PowerSeries L) H] [CommRing A] [AddCommGroup N]
    [Module A N] (c : H →+ (ℤ → M)) (hinj : Function.Injective c)
    (hc : ∀ (e : PowerSeries L) (y : H), c (e • y) = conv e (c y))
    (lev : A →+* PowerSeries L) (ex : N →+ (ℤ → M)) (Ex : N → H) (hEx : ∀ x, c (Ex x) = ex x)
    (hsm : ∀ a x, ex (a • x) = conv (lev a) (ex x))
    (D : Submodule L M) (hF : Full D (latSpan ex)) (r : ℕ) (hr : r ≤ Module.finrank L D)
    (nb : Module.Basis (Fin r) A N) :
    (∀ e : Fin r → PowerSeries L, ∑ j, conv (e j) (ex (nb j)) = 0 → e = 0) ∧
    (∀ f ∈ (latSpan ex : Submodule L (ℤ → M)), ∃ e : Fin r → PowerSeries L, f = ∑ j, conv (e j) (ex (nb j))) ∧
    ∀ (y : N) (k : ℕ), (∃ f ∈ (latSpan ex : Submodule L (ℤ → M)), ∀ j : ℤ, ex y j = f (j - k)) ↔
      ∀ j, nb.repr y j ∈ (Ideal.span {(PowerSeries.X : PowerSeries L) ^ k}).comap lev := by
  set u : Fin r → H := fun j => Ex (nb j) with hu
  have hsum : ∀ e : Fin r → PowerSeries L, c (∑ j, e j • u j) = ∑ j, conv (e j) (ex (nb j)) := by
    intro e
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hc, hEx]
  have hy : ∀ y, Ex y = ∑ j, lev (nb.repr y j) • u j := by
    intro y
    apply hinj
    rw [hsum, hEx]
    conv_lhs => rw [← nb.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsm _ _
  have h2 : ∀ f ∈ (latSpan ex : Submodule L (ℤ → M)), ∃ e : Fin r → PowerSeries L,
      f = c (∑ j, e j • u j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      refine ⟨fun j => e * lev (nb.repr x j), ?_⟩
      rw [← hEx, ← hc, hy, Finset.smul_sum]
      simp only [mul_smul]
    | zero => exact ⟨0, by simp⟩
    | add f g _ _ hf hg =>
      obtain ⟨e, rfl⟩ := hf
      obtain ⟨e', rfl⟩ := hg
      exact ⟨e + e', by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]⟩
    | smul s f _ hf =>
      obtain ⟨e, rfl⟩ := hf
      refine ⟨fun j => PowerSeries.C s * e j, ?_⟩
      rw [← conv_C, ← hc, Finset.smul_sum]
      simp only [mul_smul]
  have hli : LinearIndependent (PowerSeries L) u := by
    obtain ⟨d, hd⟩ := exists_linearIndependent_of_le_finrank hr
    have hd' : LinearIndependent L (fun a => (d a : M)) := hd.map' D.subtype (Submodule.ker_subtype _)
    obtain ⟨m, hm⟩ := hF
    have hw : ∀ a, (Pi.single (m : ℤ) (d a : M) : ℤ → M) ∈ (latSpan ex : Submodule L (ℤ → M)) := by
      intro a
      refine hm _ (fun k => ?_) (fun k hk => Pi.single_eq_of_ne hk.ne _)
      by_cases hk : k = m
      · subst hk
        simp
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    choose E hE using fun a => h2 _ (hw a)
    refine indep_of_span u (fun a => ∑ j, E a j • u j) ?_ fun a =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    ext n
    have h1 := congrFun (congrArg c hg) ((m : ℤ) + n)
    rw [map_sum, map_zero, Finset.sum_apply] at h1
    simp only [hc, ← hE, conv_single, Pi.zero_apply] at h1
    simpa using Fintype.linearIndependent_iff.1 hd' _ h1 a
  refine ⟨fun e he => ?_, fun f hf => ?_, fun y k => ⟨?_, fun h => ?_⟩⟩
  · rw [← hsum] at he
    funext j
    exact Fintype.linearIndependent_iff.1 hli e (hinj (he.trans (map_zero c).symm)) j
  · obtain ⟨e, rfl⟩ := h2 f hf
    exact ⟨e, hsum e⟩
  · rintro ⟨f, hf, hk⟩ j
    obtain ⟨e, rfl⟩ := h2 f hf
    have h3 : Ex y = (PowerSeries.X : PowerSeries L) ^ k • ∑ j, e j • u j := by
      apply hinj
      funext j
      rw [hc, conv_X_pow, hEx, hk]
    rw [hy, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h3
    simp only [← mul_smul, ← sub_smul] at h3
    have h4 := Fintype.linearIndependent_iff.1 hli _ h3 j
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    exact ⟨e j, sub_eq_zero.1 h4⟩
  · simp only [Ideal.mem_comap, Ideal.mem_span_singleton] at h
    choose e he using h
    refine ⟨c (∑ j, e j • u j), ?_, fun j => ?_⟩
    · rw [hsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨e j, nb j, rfl⟩
    · refine Eq.trans ?_ (conv_X_pow (L := L) k _ j)
      rw [← hc, ← hEx, hy, Finset.smul_sum]
      simp only [he, mul_smul]

theorem core' {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (lev : A →+* PowerSeries L) (ex : N →+ (ℤ → M)) (hb : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (hsm : ∀ a x, ex (a • x) = conv (lev a) (ex x))
    (D : Submodule L M) (hF : Full D (latSpan ex)) (r : ℕ) (hr : r ≤ Module.finrank L D)
    (nb : Module.Basis (Fin r) A N) :
    (∀ e : Fin r → PowerSeries L, ∑ j, conv (e j) (ex (nb j)) = 0 → e = 0) ∧
    (∀ f ∈ (latSpan ex : Submodule L (ℤ → M)), ∃ e : Fin r → PowerSeries L, f = ∑ j, conv (e j) (ex (nb j))) ∧
    ∀ (y : N) (k : ℕ), (∃ f ∈ (latSpan ex : Submodule L (ℤ → M)), ∀ j : ℤ, ex y j = f (j - k)) ↔
      ∀ j, nb.repr y j ∈ (Ideal.span {(PowerSeries.X : PowerSeries L) ^ k}).comap lev := by
  letI : Module (PowerSeries L) (HahnModule ℤ L M) := Module.compHom _ (HahnSeries.ofPowerSeries ℤ L)
  let c : HahnModule ℤ L M →+ (ℤ → M) :=
    AddMonoidHom.mk' (fun y => ((HahnModule.of L).symm y).coeff) (fun _ _ => rfl)
  have hbd : ∀ x, BddBelow (Function.support (ex x)) := fun x => by
    obtain ⟨m, hm⟩ := hb x
    exact ⟨m, fun k hk => not_lt.1 fun h => hk (hm k h)⟩
  exact core c (fun a b h => (HahnModule.of L).symm.injective (HahnSeries.ext h))
    (fun e y => coeff_smul_hahn e y) lev ex
    (fun x => HahnModule.of L (HahnSeries.ofSuppBddBelow (ex x) (hbd x))) (fun _ => rfl) hsm D hF r hr nb

end Series

section Rank

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem card_eq_rank [Nontrivial O] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) : r = Module.finrank O ↥T.L.T := by
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  rw [← (W.DD_free T).2,
    Module.finrank_eq_card_basis ((nb.baseChange W.EE).map (W.N_base T hT).equiv), Fintype.card_fin]

theorem rank_le [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    Module.finrank O ↥T.L.T ≤ Module.finrank LL T.V := by
  obtain ⟨d, hd⟩ := exists_linearIndependent_of_le_finrank (le_refl (Module.finrank O ↥T.L.T))
  have hd' : LinearIndependent O (fun a => (d a : T.V)) := hd.map' T.L.T.subtype (Submodule.ker_subtype _)
  have := ((LinearIndependent.iff_fractionRing O LL).1 hd').fintype_card_le_finrank
  simpa using this

theorem card_emb (W : LocWach PD LL O v n) : Nat.card (K₀ →ₐ[Qp] LL) = Module.finrank Qp K₀ := by
  rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  exact W.n_eq

theorem ιV_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lift_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (f : ↥(W.N T) → ℤ → T.V ⊗[Qp] B)
    (hf : ∀ x k, W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (f x k)) (a : LetA O n) (x : ↥(W.N T)) :
    f (a • x) = conv (W.lev i ζ a) (f x) := by
  funext k
  apply ιV_inj (PD := PD) (LL := LL) (V := T.V)
  unfold conv
  rw [← hf, W.levN_smul]
  refine Eq.trans ?_ (AddMonoidHom.map_finsum_of_injective
    (ιV PD (LL := LL) (V := T.V)).toAddMonoidHom (ιV_inj (PD := PD) (LL := LL) (V := T.V)) _).symm
  refine finsum_congr fun j => ?_
  rw [hf]
  exact (map_smul _ _ _).symm

def levRing (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) : LetA O n →+* PowerSeries LL :=
  (W.lev i ζ).toRingHom

end Rank

theorem expansion_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → (∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x)) ∧ ∀ (r : ℕ) (nb : Module.Basis (Fin r) (AA K LL) ↥(W.N T)), (∀ e : Fin r → PowerSeries ↥LL.1, ∑ j, conv (e j) (ex C h T i ζ (nb j)) = 0 → e = 0) ∧ (∀ f ∈ Lat C h T i ζ, ∃ e : Fin r → PowerSeries ↥LL.1, f = ∑ j, conv (e j) (ex C h T i ζ (nb j))) ∧ ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ y j = f (j - k)) ↔ ∀ j, nb.repr y j ∈ van W i ζ k := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ _ hF
  have hsm : ∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x) :=
    lift_smul W T i ζ _ ((C.C K s LL h).tie.levN_eq T i ζ)
  refine ⟨hsm, fun r nb => ?_⟩
  haveI := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  have hr : r ≤ Module.finrank ↥LL.1 ↥(Di (HW l) h T i) := by
    rw [card_eq_rank W T hT r nb,
      (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _ (D.locT l) K LL T.V T.ρ).1 (card_emb W) hT]
    exact rank_le T
  exact core' (levRing W i ζ) ((C.C K s LL h).tie.levB T i ζ) ((C.C K s LL h).tie.levB_supp T i ζ)
    hsm _ hF r hr nb

end GlobalTheory.NL.LevInj
