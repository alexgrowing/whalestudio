import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvIdempotentAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

open Formalism.IndefR.Lev

open scoped Pointwise in

theorem not_isConjPl {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ Lev.IsConjPl w w' := by
  intro hc
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hz
  obtain ⟨v, hv, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv w
  have hv' := (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w v).1 hv
  have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
  subst hvw
  obtain ⟨ho, hiff⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w
    (P.overP hw)).2.2.2 (P.pb k) (P.pb_over k) v hv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k'
      · exact absurd rfl hne
      · exact D.host.g_ne
      · exact D.host.g_ne.symm
      · exact absurd rfl hne
    obtain ⟨s, t, hst⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hst]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ho) (v.asIdeal.mul_mem_left _ (P.overP hw'))
  subst hk
  exact hiff.1 hw hw'

theorem conv_of_idem {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra ℂ H) (hz : z * z = z) (g : H) :
    ∑ a, z.coeff a * z.coeff (a⁻¹ * g) = z.coeff g := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) :
    Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun X hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem postOn_gaL_mem (hθ : IsInfFam θ) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
    ext v h
    simp [gaL, postOn_apply]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L (eG g) X hX _ fun _ => rfl)

theorem gaL_gaL (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : gaL V β L eG c (gaL V β L eG c F) = gaL V β L eG c F := by
  letI : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F, gaL V β L eG c F = ∑ g, c (eG.symm g) • actG0 V β L g F := fun F => by
    unfold gaL
    rw [LinearMap.sum_apply]
    refine Fintype.sum_equiv eG.toEquiv _ _ fun g => ?_
    show c g • actG0 V β L (eG g) F = c (eG.symm (eG g)) • actG0 V β L (eG g) F
    rw [MulEquiv.symm_apply_apply]
  rw [e, e]
  refine GlobalTheory.FlagAction.convIdempotent_act V β L hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc]
  refine Fintype.sum_equiv eG.symm.toEquiv _ _ fun a => ?_
  show c (eG.symm a) * c (eG.symm (a⁻¹ * g)) = c (eG.symm a) * c ((eG.symm a)⁻¹ * eG.symm g)
  rw [map_mul, map_inv]

theorem postOn_gaL_mem_goodPart (hθ : IsInfFam θ) (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) (gaL V β L eG c) := by
  refine ⟨postOn_gaL_mem hθ eG c hX, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  ext1 v
  exact gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)

end Act

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem liftsExist_rows (h : R.toLevCh.Is A.μ0) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl R.C.P hk hk'

theorem eC_conv (hr : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h]
  rw [← conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  refine Fintype.sum_equiv eR.toEquiv _ _ fun a => ?_
  show _ = D.ntypes.e0.coeff (eR a) * D.ntypes.e0.coeff ((eR a)⁻¹ * eR g)
  rw [map_mul, map_inv]

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 :=
  (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x))).2

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    PiTensorProduct.lift.symm (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e0 := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv
    R.chi (R.xiR t)
  have e1 := e0.1
  have e2 := e0.2
  have h1 : R.thDn t x ∈ MultT R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) :=
    thDn_mem_CC R t x
  have h2 := (mem_multT R.θ (R.MY 0) _ _ _).1 h1
  have e1' : levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levG (Yc D 0) (R.βY 0) (R.dat0 R.triv) := e1
  have e2' : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := e2
  have h3 : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 R.triv), k ∈ levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) ∧
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := fun k hk => by
    have hk' : k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) := by rw [e1']; exact hk
    exact ⟨hk', e2' k hk'⟩
  exact mult_mono h3 h2

theorem proj_thDn_mem (h : R.toLevCh.Is A.μ0) (hθ : R.models_inf) (hr : R.grp_record) (t : T) (x : (R.HX t).H) :
    postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) ∈ R.EEat R.triv :=
  postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hθ (liftsExist_rows R h) R.eG _ (eC_conv R hr) (thDn_mem R t x)

end Real

theorem exists_chain_Th : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → ∃ Th, ({ R with Th := Th } : RealDat D A Ks).chain_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h _ hM hr
  have key : ∀ t, ∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H,
      ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) := fun t =>
    GlobalTheory.HilbertModel.exists_lift hM.HE
      (postOn (R.MY 0) R.e0 ∘ₗ
        (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t)
      (proj_thDn_mem R h hM.inf hr t)
  choose Th hTh using key
  exact ⟨Th, hTh⟩

end GlobalTheory.ProjectedLift

end
