import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoordField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitHalf

section Gen
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_inv (Φ : SB X) (A : AddSubgroup X) (hA : IsCompact (A : Set X)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ A, ∀ x, Φ.1 (x + N • a) = Φ.1 x := by
  let V : AddSubgroup X :=
    { carrier := {v | ∀ x, Φ.1 (x + v) = Φ.1 x}
      zero_mem' := fun x => by rw [add_zero]
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a), neg_add_cancel_right] }
  have key : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + v) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually Φ.2.2 fun x _ => ?_
    have h1 : IsLocallyConstant fun p : X × X => (Φ.1 (p.2 + p.1), Φ.1 p.2) :=
      (Φ.2.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk (Φ.2.1.comp_continuous continuous_snd)
    filter_upwards [h1.eventually_eq (0, x)] with p hp
    rw [Prod.mk.injEq, add_zero] at hp
    rw [hp.1, hp.2]
  have key' : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + -v) = Φ.1 x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually key
  have hV : IsOpen (V : Set X) := by
    refine V.isOpen_of_mem_nhds (g := 0) ?_
    filter_upwards [key, key'] with v h1 h2 x
    by_cases hx : x ∈ tsupport Φ.1
    · exact h1 x hx
    · by_cases hv : x + v ∈ tsupport Φ.1
      · rw [← h2 _ hv, add_neg_cancel_right]
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hv]
  haveI : DiscreteTopology (X ⧸ V) := QuotientAddGroup.discreteTopology hV
  have hfin : ((A.map (QuotientAddGroup.mk' V) : AddSubgroup (X ⧸ V)) : Set (X ⧸ V)).Finite := by
    rw [AddSubgroup.coe_map]
    exact (hA.image QuotientAddGroup.continuous_mk).finite_of_discrete
  haveI : Finite (A.map (QuotientAddGroup.mk' V)) := hfin
  refine ⟨Nat.card (A.map (QuotientAddGroup.mk' V)), Nat.card_pos, fun a ha => ?_⟩
  have h := card_nsmul_eq_zero' (x := (⟨QuotientAddGroup.mk' V a, a, ha, rfl⟩ : A.map (QuotientAddGroup.mk' V)))
  have h2 := congrArg Subtype.val h
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero, ← map_nsmul] at h2
  exact (QuotientAddGroup.eq_zero_iff _).1 h2

theorem exists_supp {K : Set X} (hK : IsCompact K) (A : AddSubgroup X) (hA : IsOpen (A : Set X))
    (h : ∀ x, ∃ n : ℕ, 0 < n ∧ n • x ∈ A) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ A := by
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n : ℕ+ => {x | (n : ℕ) • x ∈ A})
    (fun n => hA.preimage (continuous_nsmul _)) fun x _ => by
      obtain ⟨n, hn, hx⟩ := h x
      exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hx⟩
  refine ⟨∏ n ∈ s, (n : ℕ), Finset.prod_pos fun n _ => n.pos, fun x hx => ?_⟩
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.1 (hs hx)
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun n : ℕ+ => (n : ℕ)) hn
  rw [hm, mul_nsmul]
  exact nsmul_mem hx _

end Gen

variable {D : D7}

theorem chart_one {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) : π e = 1 := by
  have : π (e - 1) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, h1, mul_one, sub_self])
  rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this

theorem chart_cont {e : AE D} (he : IsSplitIdem D e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) : Continuous π := by
  obtain ⟨h1, h2, -⟩ := he
  have tA : ∀ z : AE D, algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
    GlobalTheory.FockCompare.SymplVal.trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e)
    (fun e he => (D.sp.cm.fixed e).1 he) (AF D.host.F)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun x : AE D => Algebra.trace (AF D.host.F) (AE D) (e * x) :=
    ht.comp (continuous_const.mul continuous_id)
  have hev : Continuous fun y : AF D.host.F => evalV D.host.F v (sndA D.host.F y) :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine (hev.comp hc).congr fun x => ?_
  have h4 : π (cA D (e * x)) = 0 := (hπ.2.1 _).2 (by rw [RingHom.map_mul, ← mul_assoc, h2, zero_mul])
  have h5 := hπ.2.2.1 (Algebra.trace (AF D.host.F) (AE D) (e * x))
  rw [tA, RingHom.map_add, h4, add_zero, RingHom.map_mul, chart_one h1 hπ, one_mul] at h5
  exact h5.symm

theorem single_add {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    singleV F v (a + b) = singleV F v a + singleV F v b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (a + b)) = evalV F w (singleV F v a + singleV F v b)
  by_cases hw : w = v
  · subst hw
    rw [map_add, GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single]
  · rw [map_add, GlobalTheory.SplitCoord.evalV_single_ne hw, GlobalTheory.SplitCoord.evalV_single_ne hw,
      GlobalTheory.SplitCoord.evalV_single_ne hw, add_zero]

def sec (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) fun a b => by
    rw [← mul_add, ← RingHom.map_add, single_add]
    congr 2
    exact Prod.ext (add_zero _).symm rfl

theorem sec_cont (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Continuous (sec e v) := by
  have ha : Continuous (Algebra.linearMap (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hb : Continuous fun a => pairA D.host.F 0 (singleV D.host.F v a) :=
    Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)
  exact continuous_const.mul (ha.comp hb)

theorem chart_sec {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (a) : π (sec e v a) = a := by
  change π (e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) = a
  rw [RingHom.map_mul, chart_one h1 hπ, one_mul, hπ.2.2.1]
  exact GlobalTheory.SplitCoord.evalV_single v a

theorem sec_chart {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (x) : sec e v (π x) = e * x := by
  have := (hπ.2.1 (sec e v (π x) - x)).1 (by rw [RingHom.map_sub, chart_sec h1 hπ, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  rw [← this]
  change e * _ = e * (e * _)
  rw [← mul_assoc, h1]

theorem exists_idem (D : D7) : ∃ e, IsSplitIdem D e := by
  have h2 : ¬ IsUnit (2 : 𝓞 D.host.F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 D.host.F))
    rw [show (2 : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) 2 by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at hn
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 D.host.F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hm : (2 : 𝓞 D.host.F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact two_ne_zero ((Submodule.mem_bot _).mp hm)
  obtain ⟨e, a, b, c, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D ⟨M, hM.isPrime, hM0⟩ hm
  exact ⟨e, a, b, _, _, ⟨_, rfl, GlobalTheory.SplitCoord.evalV_single _ 1, fun w hw => GlobalTheory.SplitCoord.evalV_single_ne hw 1⟩, c⟩

theorem isCompact_half {e : AE D} (he : IsSplitIdem D e) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    IsCompact {t : WO S T | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t} := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  have h := (GlobalTheory.PlaceCoord.isOpen_isCompact_map (S := S) (T := T) hS.1 hT.1 hπ he.1 (chart_one he.1 hπ)
    (GlobalTheory.PlaceCoord.infPart_split he)).2
  have hc : Continuous fun y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) => (y.map (sec e v) : WO S T) :=
    continuous_id.matrix_map (sec_cont e v)
  have h2 := h.image hc
  rw [Set.image_image] at h2
  convert h2 using 1
  refine (Set.EqOn.image_eq_self fun t ht => ?_).symm
  ext i j
  exact (sec_chart he.1 hπ _).trans (ht.2 i j)

variable {S : HSp D}

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {n : ℕ} (e e' f : R) (G Gi a a' b b' : Matrix (Fin n) (Fin n) R) (h1 : e * e = e)
    (h1' : e' * e' = e') (h2 : e * e' = 0) (hf : f = 1 - e - e') (hba : b * a = e • (1 : Matrix (Fin n) (Fin n) R))
    (hab' : a' * b' = e' • (1 : Matrix (Fin n) (Fin n) R)) (g1 : ∀ x : Matrix (Fin n) (Fin n) R, Gi * (G * x) = x)
    (g2 : ∀ x : Matrix (Fin n) (Fin n) R, G * (Gi * x) = x) :
    (e' • a' + e • (G * b * Gi) + f • 1) * (G * (e • a + e' • (Gi * (b' * G)) + f • 1)) = G := by
  have z1 : e' * e = 0 := by rw [mul_comm, h2]
  have z2 : e' * f = 0 := by rw [hf]; linear_combination -h1' - h2
  have z3 : e * f = 0 := by rw [hf]; linear_combination -h1 - h2
  have z4 : f * e = 0 := by rw [mul_comm, z3]
  have z5 : f * e' = 0 := by rw [mul_comm, z2]
  have z6 : f * f = f := by rw [hf]; linear_combination h1 + h1' + 2 * h2
  simp only [Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, z1, z2, z3, z4, z5, z6, h1, h1', h2, zero_smul, add_zero, zero_add,
    Matrix.mul_assoc, g1, g2, Matrix.one_mul, Matrix.mul_one, hba, smul_add]
  rw [← Matrix.mul_assoc, hab', Matrix.smul_mul, smul_smul, h1', Matrix.one_mul, ← add_smul, ← add_smul,
    show e + e' + f = 1 by rw [hf]; ring, one_smul]

theorem reflectionBoost_matrix_conjTranspose_mul_self (e e' f : AE D) (a b : Mx D S.rank S.rank) (h1 : e * e = e) (h2 : e * e' = 0) (c1 : cA D e = e')
    (hf : f = 1 - e - e') (hba : b * a = e • (1 : Mx D S.rank S.rank)) :
    adj (e • a + e' • (giA S * (adj b * gA S)) + f • 1) * (gA S * (e • a + e' • (giA S * (adj b * gA S)) + f • 1)) = gA S := by
  have h1' : e' * e' = e' := by rw [← c1, ← RingHom.map_mul, h1]
  have hab' : adj a * adj b = e' • (1 : Mx D S.rank S.rank) := by rw [← adj_mul, hba, adj_smul, adj_one, c1]
  have hcc : cA D e' = e := by rw [← c1]; exact GlobalTheory.DualPairCheck.cA_cA _
  have cf : cA D f = f := by rw [hf, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hcc, c1]; exact sub_right_comm _ _ _
  have q : adj (giA S * (adj b * gA S)) = gA S * b * giA S := by
    rw [adj_mul (giA S), adj_mul (adj b), adj_adj, adj_gA, adj_giA]
  have q2 : adj (e • a + e' • (giA S * (adj b * gA S)) + f • (1 : Mx D S.rank S.rank)) =
      e' • adj a + e • (gA S * b * giA S) + f • (1 : Mx D S.rank S.rank) := by
    rw [adj_add, adj_add, adj_smul e, adj_smul e', adj_smul f, q, hcc, cf, c1, adj_one (n := S.rank)]
  rw [q2]
  exact units_mul_relation_rearrange_commRing e e' f _ _ a _ b _ h1 h1' h2 hf hba hab' (giA_gA_cancel S) (gA_giA_cancel S)

end GlobalTheory.SplitHalf
end
