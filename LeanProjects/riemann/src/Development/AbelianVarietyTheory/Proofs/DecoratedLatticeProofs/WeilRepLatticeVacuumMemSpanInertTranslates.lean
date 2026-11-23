import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_compFin (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D)
    (ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) * a = a) :
    secW hw h (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)) = a := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h _)) = a
  rw [RingEquiv.symm_apply_apply]
  conv_rhs => rw [← ha]
  rw [show algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 from rfl,
    GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

theorem exists_uPt_eq (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} (hk0 : k ≠ 0) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) {u : WO S T}
    (hu : IsHalf (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) u) :
    ∃ y, uPt hw h k aS aT y = u := by
  let U : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    u.map fun a => GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)
  refine ⟨k⁻¹ • ((aT⁻¹).1 * U * aS.1), ?_⟩
  have e1 : k • (aT.1 * (k⁻¹ • ((aT⁻¹).1 * U * aS.1)) * (aS⁻¹).1) = U := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk0, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply]
  exact secW_compFin hw h _ (hu i j)

open GlobalTheory.Hk3 GlobalTheory.InertLoc GlobalTheory.SplitScalar GlobalTheory.FinWeilO in
set_option maxHeartbeats 1600000 in

theorem om_mem_span_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  intro D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gaS gaT f hf gS gT
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hP : Formalism.DivisionValues.conjPl w = w := by
    by_contra hne
    exact GlobalTheory.LFun.not_isSplit_of_isInertAt hw (dict.1.2 hne)
  have he : IsPrimeIdem w (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v))
      (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) :=
    GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert hw (GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v)
  set e := algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) with he_def
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  obtain ⟨ϖ0, σ, q, π, hU0, h2, hc0, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS'⟩ := hV S
  obtain ⟨βT, ιT, hT, gT'⟩ := hV T
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU0 h2 (th ψ hc0 k) (th_conj hc0 hU0.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ hc0 hU0.2.1 hβ ⟨0, ?_⟩ hk
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D w) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap hc0 βS βT k x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (hc0.half_fin (kap_half hc0 x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap hc0 βS βT k x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D w)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D w)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g g' (m : thetaSub ψ S T), (ω (g, g') m : WO S T → ℂ) = om (ιS g, ιT g') m := fun _ _ _ => rfl
  have hlat := kap_mem_iff hc0 hU0.2.1 hS hT hk
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half hc0 x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T w m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 w e e he).2.2.2.1 e' f' he'
    rwa [hc0.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V w ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D w)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D w)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D w)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  have hLP : LocPair ϖ0 σ q δ (1 : GL (Fin S.rank) (LP D w)) (1 : GL (Fin T.rank) (LP D w)) ψ' ρ ω := by
    refine ⟨hU0, odd_of_v_two hU0 h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_,
      fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap hc0 hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ,
        kap_add, locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    · refine span_vacua hψ hc0.1.1 hc0.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        refine ⟨kap hc0 βS βT k ((2⁻¹ : LP D w) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
        · rw [map_inv₀, h2, inv_one]
        · rw [← kap_add, half_add_half]
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      show om (ιS g, ιT g') (heisO ψ S T (kap hc0 βS βT k x) m) = heisO ψ S T (kap hc0 βS βT k _) (om (ιS g, ιT g') m)
      rw [hW.om_heis _ _ _ _ m.2, actO_kap hc0 gS' gT']
    · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS' g).2 hg) _ ((hhyp gT' g').2 hg'))
  obtain ⟨r1, hr1⟩ := gS'.2.2.1 (embV S v gS) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem S he h _).2 ⟨gS, rfl⟩)
  obtain ⟨r2, hr2⟩ := gT'.2.2.1 (embV T v gT) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem T he h _).2 ⟨gT, rfl⟩)
  let fM : thetaSub ψ S T := ⟨f, hf.1⟩
  have hvf : LocVac ρ fM := (hvac fM).2 (dict.2.2.2.1 ψ S T f hf)
  haveI : CharZero (LP D w) := algebraRat.charZero _
  obtain ⟨cc, hcc⟩ := locPair_act_vac_comb (LP D w) ϖ0 σ q δ S.rank T.rank 1 1 ψ' (thetaSub ψ S T) ρ ω hLP (r1, r2)
  have e1 : om (embV S v gS, embV T v gT) f = ((ω (r1, r2) fM : thetaSub ψ S T) : WO S T → ℂ) := by
    rw [hω, hr1, hr2]
  rw [e1, hcc fM hvf, Finsupp.sum, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [Submodule.coe_smul, hρ]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨y, hy⟩ := exists_uPt_eq hw h hk.1 aS aT (kap_half hc0 x)
  rw [← hy]
  exact Submodule.subset_span ⟨y, rfl⟩

end GlobalTheory.InertFrameLoc
