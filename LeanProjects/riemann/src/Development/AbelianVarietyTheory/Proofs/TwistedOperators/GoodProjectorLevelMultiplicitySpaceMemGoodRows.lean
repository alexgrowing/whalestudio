import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ProjectiveLiftExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelMultiplicityStableUnderActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvIdempotentAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct Pointwise

namespace GlobalTheory.ProjLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ActPreservesMult : Prop :=
  ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r),
    ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)),
      ∃ T' ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ v, T' v = actG0 V β L g0 (T v)

def FiniteGroupLifts : Prop :=
  ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ),
    IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L

theorem not_isConjPl_of_div {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : Pl D.host.E}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ IsConjPl w w' := by
  intro hc
  have hov : ∀ {j : Fin 2} {u : Pl D.host.E}, P.Div j u → ((D.host.g j : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
    intro j u hu
    have h1 := P.pb_over j
    rw [← hu] at h1
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g j : ℕ) : 𝓞 D.host.K) ∈ u.asIdeal := h1
    rwa [map_natCast] at this
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext (hzv.trans ((bridge_star_holds D.R D.host _).trans
      (D.host.conj.apply_symm_apply (y : D.host.E))))
    exact e ▸ hz
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • w.asIdeal = w'.asIdeal := hmax.eq_of_le w'.isPrime.ne_top hle
  have hm := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w (hov hw)).2.2.2
    (P.pb k) (P.pb_over k) w' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w w').2 heq)
  have hg : D.host.g k = D.host.g k' :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w' hm.1).1.symm.trans
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k') (D.host.g_prime k') (D.nd.g_split k') w' (hov hw')).1
  obtain rfl : k = k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
  exact hm.2.1 hw hw'

theorem mult_congr {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hJ : J = J') (hχ : ∀ k ∈ J, χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  subst hJ
  exact Submodule.span_mono fun T h => ⟨h.aut, h.cusp, fun v k hk g => hχ k hk ▸ h.lev v k hk g, h.equiv, h.cont⟩

theorem conv_coeff_of_idem {H : Type} [Group H] [Fintype H] {e : MonoidAlgebra ℂ H} (he : e * e = e) (g : H) :
    ∑ a, e.coeff a * e.coeff (a⁻¹ * g) = e.coeff g := by
  conv_rhs => rw [← he]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

theorem sum_act_idem {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hL : LiftsExist V β L)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    ∑ g, c g • actG0 V β L (eG g) (∑ g', c g' • actG0 V β L (eG g') F) = ∑ g, c g • actG0 V β L (eG g) F := by
  letI I : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F', ∑ g, c g • actG0 V β L (eG g) F' = ∑ g ∈ @Finset.univ _ I, c (eG.symm g) • actG0 V β L g F' := fun F' =>
    @Fintype.sum_equiv _ _ _ _ I _ eG.toEquiv _ _ fun g => by simp
  rw [e, e]
  refine @GlobalTheory.FlagAction.convIdempotent_act D V β L I hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc (eG.symm g)]
  exact @Fintype.sum_equiv _ _ _ I _ _ eG.symm.toEquiv _ _ fun a => by simp

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem eC_conv (h : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) = RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, -, -, h, -⟩ := h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h, map_mul, map_inv]
  rw [← conv_coeff_of_idem (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  exact Fintype.sum_equiv eR.toEquiv _ _ fun _ => rfl

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 := by
  unfold RealDat.thDn
  rw [LinearMap.comp_apply]
  exact Submodule.coe_mem _

theorem mult_datYt_le (t : T) :
    Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) ≤
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  obtain ⟨h2, h3⟩ := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv R.chi (R.xiR t)
  exact mult_congr R.θ (R.MY 0) (congrArg SetLike.coe h2) h3

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)) (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
  mult_datYt_le R t ((mem_multT R.θ (R.MY 0) _ _ _).1 (thDn_mem_CC R t x))

theorem goodRowsProjector_apply_eq_sum (F : GA D (Yc D 0) → ℂ) :
    R.e0 F = ∑ g, RealDat.eC (A := A) D.what₂.embLL g • actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) F := by
  unfold RealDat.e0 gaL
  rw [LinearMap.sum_apply]
  rfl

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hA : ActPreservesMult) {U : MMap (R.MY 0)}
    (hU : U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv))) :
    postOn (R.MY 0) R.e0 U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  choose U' hU' hv using fun g => hA R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) U hU
  have e : postOn (R.MY 0) R.e0 U = ∑ g, RealDat.eC (A := A) D.what₂.embLL g • U' g := by
    refine MultilinearMap.ext fun v => ?_
    rw [MultilinearMap.sum_apply]
    refine (goodRowsProjector_apply_eq_sum R (U v)).trans (Finset.sum_congr rfl fun g _ => ?_)
    rw [MultilinearMap.smul_apply, hv]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hU' g)

theorem lifts_exist_at_base_level (hL : FiniteGroupLifts) (h : R.toLevCh.Is A.μ0) :
    LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine hL _ _ _ _ _ hc rfl fun w hw w' hw' => ?_
  obtain ⟨k, hk⟩ := (h.Pg w).1 hw
  obtain ⟨k', hk'⟩ := (h.Pg w').1 hw'
  exact not_isConjPl_of_div _ hk hk'

theorem heckeProjector_idempotent_compositeLift (hL : FiniteGroupLifts) (h : R.toLevCh.Is A.μ0) (hr : R.grp_record) {F : GA D (Yc D 0) → ℂ}
    (hF : HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F) : R.e0 (R.e0 F) = R.e0 F := by
  rw [goodRowsProjector_apply_eq_sum, goodRowsProjector_apply_eq_sum]
  exact sum_act_idem _ _ _ (lifts_exist_at_base_level R hL h) R.eG _ (eC_conv R hr) hF

end

theorem projLiftExists_of (hA : ActPreservesMult) (hL : FiniteGroupLifts) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.ProjLiftExists := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hE t
  refine (GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.exists_represents_iff hE t).2 fun x => ?_
  have h1 := thDn_mem R t x
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.projLift_apply]
  refine (mem_goodPart _ _ _ _ _ _).2 ⟨goodProjector_levelMultiplicitySpace_mem_goodRows R hA h1, fun v => ?_⟩
  exact heckeProjector_idempotent_compositeLift R hL h hr (GlobalTheory.hasType_of_mem_mult R.θ (R.MY 0) (R.βY 0) _ _ h1 v)

theorem projLiftExists : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence.ProjLiftExists :=
  projLiftExists_of GlobalTheory.T.levelMultiplicity_stable_under_action GlobalTheory.T.finite_group_lifts_to_parahoric_level

end GlobalTheory.ProjLift

end
