import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEqFockVarsCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCoreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLettersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelFinitePointMemSpanRationalFormLiftsStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ClassSumSpanCore

section Point

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
open GlobalTheory.BasePoint
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem exists_point_phiIs_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (I : Ideal (𝓞 D.host.E)), LatEmb (Wc D i) ι → HalfIs R A.μ0 l.Mb I → ∃ x1 : Fin (Vc D i).rank → LevQc Dw l, Submodule.span (𝓞 D.host.E) (Set.range x1) = ⊤ ∧ PhiIs R i c.F.val.toRingHom A.μ0 ι (Mfr l • ⊤) (indPhi c x1) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw l c ι I hι hh
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP =>
    (hR.lev.Q_ram A.μ0 PP).2 (Or.inl hP) (by rw [hR.lev.xi_base]; exact fun _ _ => rfl)
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i A.μ0
  have he' : IsIdemSum e R.Pg := by rwa [hQ, Finset.union_empty] at he
  have hP := fun PP (h : PP ∈ R.Pg) => hh.2.2 PP (Or.inl h)
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hR.lev.βV i)
  have hβ' := isIntM_frame i hV (hR.lev.βV i)
  have hi : ∀ x a, LevelDatum.rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    LevelDatum.rowP_int _ _ _ (hR.lev.βW i) e _ he' hP _ (hι.2.le (LinearMap.mem_range_self ι x)) a
  have hτ : ∀ c, ((H.bar c : 𝓞 D.host.E) : D.host.E) = D.sp.cm.sig (c : D.host.E) := fun c => H.bar_eq c
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := (rank_Wc i).le.trans (r_le_V i)
  obtain ⟨x1, h1, h2⟩ := exists_point R.Pg (fun PP => Formalism.L2.DIV.kP PP)
    (fun PP c => Ideal.Quotient.mk PP.asIdeal (H.bar c))
    (fun t => by
      obtain ⟨c, hc⟩ := crt_places R.Pg t
      exact ⟨H.bar.symm c, fun PP h => by rw [RingEquiv.apply_symm_apply]; exact hc PP h⟩)
    (rho (Wc D i) (R.βW i) e ι hi) (fun PP a c x => rho_smul _ _ _ _ hi PP a c _ (hτ c) x) (Mfr l • ⊤)
    (fun x => ⟨fun hx PP hPP a => LevelDatum.residue_rowPairing_eq_zero _ _ e ι a (fun x => hi x a) (Mfr l) PP (fun c hc => by
        obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hc
        rw [hh.1] at hb
        refine ⟨b, Ideal.prod_le_inf.trans (Finset.inf_le hPP) hb, ?_⟩
        change _ = star ((H.bar b : 𝓞 D.host.E) : D.host.E)
        rw [H.bar_eq]
        exact (star_star _).symm) x hx,
      fun hx => by
        rw [Mfr, hh.1]
        exact rho_ker _ _ _ _ hi (hR.lev.βW i) hι he' hP _ hτ x hx⟩)
    (rho_onto _ _ _ _ hi (hR.lev.βW i) hι he' fun PP h h' =>
      hP PP h (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h'))
    (fun PP => Matrix.of fun a b => Formalism.L2.DIV.resS D.host.F PP ⟨_, hβ' a b⟩)
    (fun PP => Matrix.of fun a b => Formalism.L2.DIV.resS D.host.F PP ⟨_, hβ a b⟩)
    (fun PP => by
      ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, ← RingHom.map_mul, ← map_sum]
      have : (∑ j, ⟨_, hβ a j⟩ * ⟨_, hβ' j b⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = if a = b then 1 else 0 := by
        refine Subtype.ext ?_
        rw [AddSubmonoidClass.coe_finsetSum]
        refine (congrFun (congrFun (R.βV i).inv_mul a) b).trans ?_
        rw [Matrix.one_apply]
        split_ifs <;> rfl
      rw [this, Matrix.one_apply]
      split_ifs
      exacts [map_one _, map_zero _]) hrn
  refine ⟨x1, h1, e, he, fun x => ?_⟩
  obtain ⟨h3, h4⟩ := LevelDatum.redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a
  refine ⟨h3, ?_⟩
  have h5 : ((fun b => Submodule.Quotient.mk (x b)) = x1) ↔ ∀ PP ∈ R.Pg,
      LowZero (Wc D i).rank (redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) ∧
      topL (Wc D i).rank (redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) = 1 :=
    (h2 x).trans (forall₂_congr fun PP _ => by
      rw [low_top_iff hrn]
      exact Eq.congr_left (Matrix.ext fun b a => (h4 PP b a).symm))
  rw [hQ, omegaQ, dif_pos (by simp), Finset.attach_empty, Finset.prod_empty, mul_one, omegaK, indPhi]
  by_cases h6 : (fun b => Submodule.Quotient.mk (x b)) = x1
  · rw [if_pos h6, if_pos (h5.1 h6), map_one]
  · rw [if_neg h6, if_neg (mt h5.2 h6), map_zero]

end Point

section Kernel

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
open GlobalTheory.ClassScalarValue GlobalTheory.PtId
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 800000 in

theorem lattice_scalar_value (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (t : Tp) (h : GA D (Vc D i)) (e : AE D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e (Vc D i) h) (hy : IsDetAt e (Vc D i) h y)
    (hbad : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (Λ : GenLat D.host.E (Vc D i).rank) (N M : ℕ)
    (hcj : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (g : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad t) (Bridge.hLat (Vc D i) (fin (Vc D i) h))) (r4 : Λ.LevOK N M) :
    inC O.c' (O.epF t (Bridge.hLat (Vc D i) (fin (Vc D i) h)) * ((Λ.mIdx N D.R.r : O.c'.F))⁻¹ * (Λ.zCard N D.R.r : O.c'.F)) =
      (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ *
        (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf
          Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  have hL := hC.lev
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  generalize Bridge.hLat (Vc D i) (fin (Vc D i) h) = L at *
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 L cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero Λ D.R.r (fun h0 : N = 0 => by simpa [h0] using r4.1)) q1
  rw [q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      ((L ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

set_option maxHeartbeats 2000000 in

theorem kernel_eq_shortVal (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) T.Q.l) → O.c'.F)
    (hφ : PhiIs R i (inC O.c') A.μ0 (iotaW T i) (Mfr T.Q.l • ⊤) φ) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo ((i : ℕ) + 1)) O.c') (hnab : IsNab (T.Q.Xo ((i : ℕ) + 1)) O.c' nab)
    (h : GA D (Vc D i)) (La : GenLat D.host.E (Vc D i).rank) (N : ℕ) (hsp : SplitOffBad (Vc D i) (O.bad ()) h)
    (hla : ∀ v, v ∈ La.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) (hN : La.LevOK N T.Q.l.M)
    (hg : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad ()) (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hw : ∀ ρ, (w ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ)
    (xs : VsV D i O.c'.F) (g' : GA D (Wc D i)) (hx : (O.dict g').2 ∈ ((unfO O).X (O.dict g').1).dom) (t : ℂ)
    (ht : letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
      ShortValAt (T.Q.Xo ((i : ℕ) + 1)) O.c' nab (phiHat O.c' φ) La 1 N (O.io xs)
        (unC (Formalism.L2.PjFree.Unf.ofPj (unfO O)) (O.dict g').1 ⟨(O.dict g').2, hx⟩) t) :
    thetaKO (R.ωP i A.μ0) h g' (R.ptP i A.μ0 (R.ioP i (PiTensorProduct.tprod ℂ w) (O.c0' xs))) =
      cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cst (O.dict g').1 * O.mu g' *
        inC O.c' (O.epF () (Bridge.hLat (Vc D i) (fin (Vc D i) h))) * t := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs
  obtain ⟨hemb, -, -, hmk⟩ := dict_cast T hT.laws _ (inR i) O.s0 hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨hX, hon, hinv, hp, hrk, hpq, h1, hrt, -, hbas, hD, -⟩ := hmod (O.dict g').1
  have hU : IsUnf (unfO O) := GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.laws.unf _ (inR i) O.s0 hσ)
  obtain ⟨hx', g, Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    exists_point (unfO O) hσ hU h1 hT.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) O.dict (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) O.s0)
      (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, Wt.isom, Wt.pt⟩ k)
      (wtA (κ i)) hD O.mu (R.ωP i A.μ0) (R.vacP i) cst (CcIs.unfBC _ _ _ _ O.hle _ (inC O.c') _ _ _ _ _ _ hcc) g'
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  have hM : 0 < T.Q.l.M := T.Q.l.odd.pos
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking _ _ _ T.Q.l _ _ _ mk _ hsd hm
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hN.1.pos
  have hcj : La = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) :=
    congrArg GenLat.mk (Submodule.ext hla)
  have hg' := GlobalTheory.ClassScalarCompare.guard_conjLat hg
  rw [← hcj] at hg'
  have hMb : T.Q.l.M ∣ O.bad () := by
    rw [level_M T.toCore hT.laws.toLawsM]
    exact (hP.bad ()).2.2.2.2
  have hTr : La.TrivAt T.Q.l.M := by
    obtain ⟨k, hk, h2⟩ := hg'.2.1
    exact ⟨k, hk.coprime_dvd_right hMb, h2⟩
  obtain ⟨-, cga, hio⟩ := hP.io
  have hH := mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self O.io xs)
  have hgeo := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ g _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd
    _ _ Dc.hr Dc.eL hrk hD.2 Dc.dir_eq nab hnab ϑ v κ' hϑ hv hκ mk hm hBm La.La
    ((GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ La.La).2.1 _ N hM hg'.1 hTr hN) N hN Y hY _ _ hH _ 1 t ht
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hlt := letters_eq_fockVars_core D G Pl0 T0 A T R F κ v₀ hC hT i _ _ O hP _ g Dc vr hX hp hvr
  have hω := hC.thP.ωP i A.μ0
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      thetaKO (R.ωP i A.μ0) h g' f = thetaKO (R.ωP i A.μ0) h (γ * g') f := fun f hf => by
    have e1 : ((h, γ * g') : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g') := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  rw [hmove _ (hC.thP.pt_theta i A.μ0 _), hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 xs]
  obtain ⟨hfin, e, Ps, he, hPs, hsupp⟩ := hsp
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs))).IsHomogeneous
      (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have hhalf : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → T.Q.l.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP => by
    obtain ⟨k1, -, k3⟩ := (hP.tuple ()).half
    refine ⟨?_, k3 PP hPP⟩
    rcases hPP with hPP | hPP
    · exact k1.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h₀, J', hR, -⟩ := (hP.tuple ()).reps
  have hcl := hδ A.μ0 T.Q.l (fun x => inC O.c' (φ x)) hφ hhalf hrt g _ _ Dc.hr Dc.bas Dc.idx _ vr hX
    Dc.sympl hon hinv (hbas _) hvr (O.bad ()) N h (γ * g') La mk e Ps yd hR.2.1 he hPs hfin hsupp hyd hla
    hTr hN hma Y (hΛ ▸ hY) v _ (hΛ ▸ hv) (hfr ▸ hrd) _ _ hhom
  have hep := lattice_scalar_value hC hT O hP () h e Ps yd he hPs hsupp hyd hR.2.1 La N _ hcj hg hN
  have hw' : hatC T.Q.l (fun x => inC O.c' (φ x)) = fun q => inC O.c' (phiHat O.c' φ q) := funext fun q =>
    (PairModel.hatC_phiHat O.c' φ q).symm
  rw [← hep, hw', hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i A.μ0) h (γ * g') (ka • f) = ka * thetaKO (R.ωP i A.μ0) h (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => ka * z) hcl).trans ?_
  have e1 := congrArg (thP ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx (gphi ((unfO O).X (O.dict g').1) Dc.bas
    (T.Q.H.w0 : D.host.E) La.La ((unfO O).X (O.dict g').1).Λ v (fun q => inC O.c' (phiHat O.c' φ q)) Y)
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs)))) hfr
  refine Eq.trans (congrArg (fun z => ka * (_ * z)) e1.symm) ?_
  refine Eq.trans ?_ (congrArg (fun z => _ * z) hgeo.symm)
  have halg : ∀ s : O.c'.F, algebraMap O.c'.F ℂ s = inC O.c' s := fun _ => rfl
  simp only [cmpConst, halg, map_mul, map_inv₀, map_natCast, map_one, inv_one, one_mul]
  have key : ∀ s c m k e a z n th : ℂ, ka * (s * (c * m * k) * (e * a * z) * n * th) =
      ka * s * c * m * e * (a * n * z * k * th) := fun s c m k e a z n th => by ring
  exact key _ _ _ _ _ _ _ _ _

end Kernel

section Main

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
open GlobalTheory.ClassSumSpan
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

set_option maxHeartbeats 2000000 in

theorem classSumsSpan_of_pins_core (hR : GlobalTheory.Hk3.Core R F) (ht : TieIn T R κ v₀) (hio : IoExt R) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (i : Fin D.R.m) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) : GlobalTheory.OneMapAll.ClassSumsSpan O (κ i) := by
  intro f hf
  have hT := ht.laws
  have hCI := GlobalTheory.chartIndependence_unconditional
  have hrk : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hn : (κ i).n = (Vc D i).rank := (ht.kap i (D.eTau.symm 1)).2.2.trans hrk.symm
  have hV := hP.lift.std
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.exists_frameConstants_of_characterisationCore hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ O hP
  obtain ⟨u, hu, -, -, hser⟩ := GlobalTheory.T.exists_adelicLift_eq_geometric_classSum_all_tuples hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i _ _ O hP cc hcc
  obtain ⟨h1', h2', -⟩ := GlobalTheory.PtId.dict_cast T hT _ (inR i) O.s0 (goodEmbedding_baseEmbedding_coreData O) (Wc D i) O.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.thetaKernel_oneClass_eq_classicalShortSeries D G Pl0 T0 A _ R F hR i hV _ _ (iotaW T i) h1' h2'
  obtain ⟨ka, hka, hio'⟩ := GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hR ht hio i _ _ O hP
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ O hP ()
  obtain ⟨w₀, -, hw₀, -⟩ := (ht.hv₀ i (sg0 D A)).2 rfl (hio i)
  have hw₁ : (fun ρ => (w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) := funext hw₀
  obtain ⟨x1, hx1, hφ⟩ := exists_point_phiIs_core D G Pl0 T0 A _ R F hR i hV T.Q.H _ T.Q.l O.c' (iotaW T i) _
    (GlobalTheory.PinnedData.latEmb_iotaW T hT i) (hP.tuple ()).half
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) O.c'
  obtain ⟨hb, h2, -, -, hM⟩ := hP.bad ()
  rw [← level_M T.toCore hT.toLawsM] at hM
  obtain ⟨h, J', hrep, hpe, -, hpl⟩ := (hP.tuple ()).reps
  have h1 : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (isUnf_unfO hT O).1 ▸ ((GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins).2.2.2.2.2.2 _ (inR i)).2.1
  have hev : Even (Vc D i).rank := hn ▸ (dom_wtA (κ i)).2
  have hr := hP.io.2.choose_spec.2.2.1
  have ha : ∀ g, cc (O.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.mu g ≠ 0 := fun g =>
    mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.1 (by rw [hcc.1]; exact one_ne_zero)) (by exact_mod_cast (lieFac_pos _ _ _).ne'))
      (norm_ne_zero_iff.1 (((hT.muUnit _ (inR i) _ (goodEmbedding_baseEmbedding_coreData O)).2.1 _).trans_ne one_ne_zero))
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (hu.trans_ne one_ne_zero)
  have hu0' := GlobalTheory.PtId.cmpConst_ne_zero (D := D) (norm_ne_zero_iff.1 (hka.trans_ne one_ne_zero)) δ
    (GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)))
  have hl0 : (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine mem_span_of_map_mem ((atDict O).comp (rdU (unfO O))) _ (atDict_indep hT O (κ i)) (fun _ hg => hg.1) hf ?_
  have hraw := Submodule.apply_mem_span_image_of_mem_span (atDict O)
    (rdU_mem_span_raw hT O (κ i) hn (hrk ▸ hsz) nab hnab hb x1 hx1 hf)
  refine Submodule.span_le.2 ?_ hraw
  rintro _ ⟨_, ⟨s, ⟨hs, Λ, N, P, c1, c2, c3, c4, c5, c6⟩, rfl⟩, rfl⟩
  obtain ⟨h', Λ', N', P', z, d1, d2, d3, d4, d5, d6⟩ := exists_split_move (Vc D i) hV.1 hV.2 nab h1 hnab hev hb h2 hM
    c1 c2 c3 c4 c5 (phiHat O.c' (indPhi O.c' x1))
  obtain ⟨v, rfl⟩ := hr.ge (Submodule.subset_span d5.1)
  have hep := ep_ne_zero (Vc D i) hV.1 hV.2 O.c' (hP.ep ()).2 (fun cc c0 c2 h0 => by
    have := (hP.tuple ()).B cc c0 c2
    rw [h0, map_zero] at this
    refine mul_ne_zero (Units.ne_zero _) ?_ this.symm
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h =>
      c0 (Ideal.absNorm_eq_zero_iff.1 h)))).ne') d1 d4
  let _ : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  choose t t1 t2 using fun g => d6 ℂ _ _ (raw_at_point nab hnab c1 c3 c4 c5 _ hs c6 ℂ
    (GlobalTheory.Dict.unC (Formalism.L2.PjFree.Unf.ofPj (unfO O)) (O.dict g).1 ⟨(O.dict g).2, dict_mem hT O g⟩))
  have e : atDict O (rdU (unfO O) s) = inC O.c' z • t := funext fun g => (dif_pos (dict_mem hT O g)).trans (t2 g)
  rw [SetLike.mem_coe, e]
  refine Submodule.smul_mem _ _ (mem_of_mul ha (mul_ne_zero (mul_ne_zero hu0' (inv_ne_zero hl0)) ((map_ne_zero (inC O.c')).2 hep))
    (GlobalTheory.T.thetaKernel_finitePoint_mem_span_rationalFormLifts D G Pl0 T0 A _ R F hR i A.μ0 hV h' d1.1 (O.c0' v) w₀) (fun x₀ => ?_) fun g => ?_)
  · obtain ⟨x, hx⟩ := hpe x₀
    obtain ⟨f', hf', hcl⟩ := hex x
    refine ⟨u • atDict O (rdU (unfO O) f'), Submodule.smul_mem _ _
      (Submodule.subset_span ⟨f', ⟨hf', x, (hpl x).2 ⟨x₀, hx⟩, hcl⟩, rfl⟩), fun g => ?_⟩
    have := hser () h J' hrep _ x hx f' hf'.1 hcl g
    rw [one_mul, ← hw₁] at this
    have key : ∀ a b c d : ℂ, u * a * b * c * d = a * b * c * (u * d) := fun a b c d => by ring
    exact this.trans (key _ _ _ _)
  · refine (kernel_eq_shortVal hR ht O hP hio' hδ hcc _ hφ nab hnab h' Λ' N' d1 d2 d3 d4 w₀ hw₀ v g (dict_mem hT O g)
      (t g) (t1 g)).trans ?_
    have key : ∀ c a l m e t : ℂ, l ≠ 0 → c * a * m * e * t = c * l⁻¹ * e * (a * l * m) * t := fun c a l m e t hl => by
      field_simp
    exact key _ _ _ _ _ _ hl0

end Main

section Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem classSumsSpan_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O hsz hR ⟨fw⟩ hio i hpins _
  exact classSumsSpan_of_pins_core T R F κ v₀ hR ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩ hio hsz i (O i) hpins.2

end Top

end GlobalTheory.ClassSumSpanCore
