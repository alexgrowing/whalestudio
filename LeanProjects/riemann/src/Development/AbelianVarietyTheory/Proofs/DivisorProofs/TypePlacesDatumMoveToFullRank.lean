import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryLiftDetOneStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeMove

theorem isThetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0)
    {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    {f₀ Φ f : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (h0 : om (g, h) f₀ = f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) a
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) a
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀
      (fun x => Φ (actO S T g⁻¹ h⁻¹ x)) (om (g, h) f) := by
  have hΛ' : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g⁻¹ h⁻¹ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    fun u => by
      rw [hΛ (actO S T g⁻¹ h⁻¹ u), GlobalTheory.AdelicLatMove.actO_actO_inv]
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  have h0' : om (g⁻¹, h⁻¹) f₀ = (1 : ℂ) • f₀ := by
    rw [one_smul]
    conv_lhs => rw [← h0]
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hS hT a ha hinf f₀ hf₀ T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ' hT' th1 one_ne_zero h0'
  have hf' : f = (1 : ℂ)⁻¹ • om (g⁻¹, h⁻¹) (T' fun t => Φ (actO S T g⁻¹ h⁻¹ t)) := hall _ pm
  rw [hf', inv_one, one_smul, omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.TypeMove

namespace GlobalTheory.TypeMove

theorem om_vac_fix {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) {e : AE D} (he : IsSplitIdem D e)
    {g : GA D S} (hg : SuppAt e S g) (hst : finE S g ∈ St βS) (hdet : IsDetAt e S g 1) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f) :
    om (g, 1) f = f := by
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS hT hfS hfT g 1 hst
    (by rw [map_one]; exact one_mem _)
  have h1 : IsDetAt e T 1 1 := by
    unfold IsDetAt
    rw [show Formalism.L2.Theta.mt T 1 = 1 from rfl, Matrix.det_one, Units.val_one]
    ring
  have := GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he g 1 hg (fun a b => by rw [show Formalism.L2.Theta.mt T 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]) hL
    1 1 hdet h1 f hf hvac
  rw [this]
  simp [splitFacO]

theorem om_vac_fix_prod {D : D7} {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ} (l : List (GA D S))
    (h : ∀ g ∈ l, om (g, 1) f = f) : om (l.prod, 1) f = f := by
  induction l with
  | nil => rw [List.prod_nil, Prod.mk_one_one, map_one]; rfl
  | cons a l ih =>
    rw [List.prod_cons, show ((a * l.prod, 1) : GA D S × GA D T) = (a, 1) * (l.prod, 1) by simp, map_mul,
      Module.End.mul_apply, ih fun g hg => h g (List.mem_cons_of_mem _ hg), h a List.mem_cons_self]

end GlobalTheory.TypeMove

namespace GlobalTheory.TypeMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

theorem omegaFree_move (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP))
    (M : ∀ PP : Pl D.host.E, GL (Fin (Vc D i).rank) (kP PP)) (hQ : ∀ PP ∈ Q, M PP = 1)
    (hM : ∀ PP ∈ R.Pg, ((M PP)⁻¹).val * (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) PP = y₀ PP)
    (u : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) (fun PP => (M PP).val * u PP) = omegaFree R i Q ξR y₀ u := by
  have hv : ∀ PP ∈ Q, (M PP).val * u PP = u PP := fun PP hP => by rw [hQ PP hP, Units.val_one, Matrix.one_mul]
  have hiff : (∀ PP ∈ R.Pg, (M PP).val * u PP = (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) PP) ↔ ∀ PP ∈ R.Pg, u PP = y₀ PP := by
    refine forall₂_congr fun PP hP => ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hM PP hP, ← h, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    · rw [h, ← hM PP hP, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  unfold omegaFree
  rw [if_congr hiff rfl rfl]
  congr 1
  by_cases h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (u PP)).det
  · have h' : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank ((M PP).val * u PP)).det := fun PP hP => by
      rw [hv PP hP]; exact h PP hP
    rw [dif_pos h', dif_pos h]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h' PP.1 PP.2).unit = (h PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, hv PP.1 PP.2])
    rw [e]
  · have h' : ¬ ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank ((M PP).val * u PP)).det := fun h' =>
      h fun PP hP => by rw [← hv PP hP]; exact h' PP hP
    rw [dif_neg h', dif_neg h]

end GlobalTheory.TypeMove

namespace GlobalTheory.TypeMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

theorem datum_move (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (e : AE D)
    {m : GA D (Vc D i)} (hm : finE (Vc D i) m ∈ St (R.βV i))
    (hQ : ∀ PP ∈ Q, redFn (R.βV i) PP (finE (Vc D i) m) = 1)
    (hM : ∀ PP ∈ R.Pg, ((redFn (R.βV i) PP (finE (Vc D i) m))⁻¹).val * (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) PP = y₀ PP) (x : WO (Vc D i) (Wc D i)) :
    (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (actO (Vc D i) (Wc D i) m 1 x) = (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFree R i Q ξR y₀ (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) x := by
  have hh1 : finE (Wc D i) 1 ∈ St (R.βW i) := by rw [map_one]; exact one_mem _
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)
  · obtain ⟨i1, i2⟩ := GlobalTheory.AdjDatumMove.red_actO _ _ (R.βV i) (R.βW i) hm hh1 hx.2
    simp only
    rw [if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff m 1 x).2 hx.1, i1⟩, if_pos hx, funext i2]
    simp only [map_one, Formalism.L2.DIV.redFn_one, inv_one, Units.val_one, Matrix.mul_one]
    exact omegaFree_move R i Q ξR y₀ (fun PP => redFn (R.βV i) PP (finE (Vc D i) m)) hQ hM _
  · simp only
    rw [if_neg hx, if_neg]
    rintro ⟨h1, h2⟩
    refine hx ⟨(GlobalTheory.SchrMove.isHalf_actO_iff m 1 x).1 h1, ?_⟩
    have h4 := (GlobalTheory.AdjDatumMove.red_actO _ _ (R.βV i) (R.βW i) (g := m⁻¹) (h := (1 : GA D (Wc D i))⁻¹)
      (by rw [map_inv]; exact inv_mem hm) (by rw [map_inv]; exact inv_mem hh1) h2).1
    rwa [GlobalTheory.SplitHecke.actO_inv_actO] at h4

end GlobalTheory.TypeMove

namespace GlobalTheory.TypeMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inCoefLat_mul (R : RealDat D A Ks) (i : Fin D.R.m) (hΛ : IsSDFrame (Vc D i) (R.βV i) (R.ΛV i) 1)
    {k : GA D (Vc D i)} (hk : finE (Vc D i) k ∈ St (R.βV i)) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (hw : InCoefLat R i h w) : InCoefLat R i (h * k) w := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, P, ?_, rfl⟩
  have e : Formalism.IndefR.FWT.fin (Vc D i) (h * k) =
      1 * Formalism.IndefR.FWT.fin (Vc D i) h * Formalism.IndefR.FWT.fin (Vc D i) k := by
    rw [one_mul]; exact map_mul _ _ _
  rw [e, GlobalTheory.HLatMove.hLat_mul hΛ 1 (Formalism.IndefR.FWT.fin (Vc D i) h) (Formalism.IndefR.FWT.fin (Vc D i) k) 1 (by simp) hk]
  convert hP using 2
  rw [Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem typePrime_mem (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (h : PP ∈ R.Pg) :
    ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (hC.lev.Pg PP).1 h
  refine ⟨k, ?_⟩
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h2 := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h2
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
  simpa using h2

theorem typePrime_not_mem {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E} (h : PP ∈ Q)
    (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro hmemE
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hQ PP h
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

theorem typePlace_off_twist (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) {Q : Finset (Pl D.host.E)}
    (hQ : IsTwistPlaces D.host.g Q) {PP PP' : Pl D.host.E} (hP : PP ∈ R.Pg) (hP' : PP' ∈ Q) :
    PP' ≠ PP ∧ ¬ Lev.IsConjPl PP PP' := by
  obtain ⟨k, hk⟩ := typePrime_mem R F hC hP
  refine ⟨fun e => typePrime_not_mem hQ hP' k (e ▸ hk), fun hc => ?_⟩
  obtain ⟨c', hc', hcc⟩ := hc _ hk
  have h1 : (c' : D.host.E) = (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) := hcc.trans (by simp)
  have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.coe_injective h1
  exact typePrime_not_mem hQ hP' k (this ▸ hc')

end GlobalTheory.TypeMove

namespace GlobalTheory.TypeMove

theorem exists_detOne_mul_std {K : Type} [Field K] {n r : ℕ} (hrn : r < n) (y : Matrix (Fin n) (Fin r) K)
    (hy : y.rank = r) :
    ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧
      g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y :=
  GlobalTheory.T.exists_det_one_mul_stdBlock' hrn y hy

theorem exists_local_lift_detOne {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hB : IsBaseFrame V β Λ N)
    {P : Pl D.host.E} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) (k : GL (Fin V.rank) (kP P))
    (hk : Matrix.GeneralLinearGroup.det k = 1) :
    ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧
      (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 :=
  GlobalTheory.T.exists_split_supported_unitary_lift_detOne hB he k hk

end GlobalTheory.TypeMove

open GlobalTheory.TypeMove in

theorem GlobalTheory.TypeMove.vecFree_typeMove : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ c : D.what₂.LL, φ' = D.what₂.embLL c • ω (k, 1) φ₁ ∧ IsIntegral ℤ c ∧ IsIntegral ℤ c⁻¹ ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK y₀ hy₀ φ₁ hφ₁
  classical
  obtain ⟨hvac, e, hIS, hth⟩ := hφ₁
  obtain ⟨⟨es, hes, -⟩, -⟩ := id hIS
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) _ _ ω := hK.weil
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hlt : (Wc D i).rank < (Vc D i).rank := by
    rw [rV, rW]; have := D.R.t_odd.pos; omega
  have hg : ∀ PP ∈ R.Pg, ∃ g : GL (Fin (Vc D i).rank) (kP PP), Matrix.GeneralLinearGroup.det g = 1 ∧
      g.val * (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) PP = y₀ PP := fun PP hPP => exists_detOne_mul_std hlt (y₀ PP) (hy₀ PP hPP)
  choose! gm hgdet hgmul using hg
  have hκ : ∀ PP : ↥R.Pg, ∃ κ : GA D (Vc D i), SuppAt (es PP.1) (Vc D i) κ ∧ κ ∈ GfC (Vc D i) ∧
      finE (Vc D i) κ ∈ St (R.βV i) ∧ redFn (R.βV i) PP.1 (finE (Vc D i) κ) = (gm PP.1)⁻¹ ∧
      (∀ P', P' ≠ PP.1 → ¬ Lev.IsConjPl PP.1 P' → redFn (R.βV i) P' (finE (Vc D i) κ) = 1) ∧
      IsDetAt (es PP.1) (Vc D i) κ 1 := fun PP =>
    exists_local_lift_detOne hBV (hes PP.1 (Finset.mem_union_left _ PP.2)) (gm PP.1)⁻¹
      (by rw [map_inv, hgdet PP.1 PP.2, inv_one])
  choose κ h1 h2 h3 h4 h5 h6 using hκ
  have hnd : (Finset.univ : Finset ↥R.Pg).toList.Nodup := Finset.nodup_toList _
  have hmem : ∀ PP, PP ∈ (Finset.univ : Finset ↥R.Pg).toList := fun PP => Finset.mem_toList.2 (Finset.mem_univ _)
  have hlSt : ∀ g ∈ (Finset.univ : Finset ↥R.Pg).toList.map κ, finE (Vc D i) g ∈ St (R.βV i) := by
    intro g hg
    obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h3 PP
  obtain ⟨hmSt, hmred⟩ := GlobalTheory.ParahoricLift.redFn_list_prod (Vc D i) (R.βV i) _ hlSt
  have hmG : ((Finset.univ : Finset ↥R.Pg).toList.map κ).prod ∈ GfC (Vc D i) :=
    (GfC (Vc D i)).list_prod_mem fun g hg => by
      obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
      exact h2 PP
  set m := ((Finset.univ : Finset ↥R.Pg).toList.map κ).prod with hm
  have hnc := GlobalTheory.SeeConjPlaces.pg_not_isConjPl R F hC.lev hC.grp
  have hredPg : ∀ PP ∈ R.Pg, redFn (R.βV i) PP (finE (Vc D i) m) = (gm PP)⁻¹ := by
    intro PP hPP
    rw [hmred PP, List.map_map, GlobalTheory.ParahoricLift.prod_map_single hnd (hmem ⟨PP, hPP⟩) _ fun PP' hne => ?_]
    · exact h4 ⟨PP, hPP⟩
    · exact h5 PP' PP (fun h => hne (Subtype.ext h.symm)) (hnc PP'.1 PP'.2 PP hPP)
  have hredQ : ∀ PP ∈ Q, redFn (R.βV i) PP (finE (Vc D i) m) = 1 := by
    intro PP hPP
    rw [hmred PP, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨PP', -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a1, a2⟩ := typePlace_off_twist R F hC hK.pl PP'.2 hPP
    exact h5 PP' PP a1 a2
  have hvfix : ω (m, 1) (R.vacP i) = R.vacP i := by
    refine om_vac_fix_prod _ fun g hg => ?_
    obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact om_vac_fix hW hSV hSW hFV hFW (hes PP.1 (Finset.mem_union_left _ PP.2)).1 (h1 PP) (h3 PP) (h6 PP)
      hvac.2.theta hvac.2.lat
  have hvfix' : ω (m⁻¹, 1) (R.vacP i) = R.vacP i := by
    conv_lhs => rw [← hvfix]
    rw [show ω (m⁻¹, 1) (ω (m, 1) (R.vacP i)) = (ω (m⁻¹, 1) * ω (m, 1)) (R.vacP i) from rfl, ← map_mul,
      Prod.mk_mul_mk, inv_mul_cancel, one_mul, Prod.mk_one_one, map_one]
    rfl
  have hmSt' : finE (Vc D i) m⁻¹ ∈ St (R.βV i) := by rw [map_inv]; exact inv_mem hmSt
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) hSV hSW
    hFV hFW m⁻¹ 1 hmSt' (by rw [map_one]; exact one_mem _)
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hth' := isThetaAt_move hW hSV hSW hos.idem hos.infPart_eq hL hvac.2.theta hvfix' hth
  have hΦ : (fun x => (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (actO (Vc D i) (Wc D i) m⁻¹⁻¹ (1 : GA D (Wc D i))⁻¹ x)) = (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFree R i Q ξR y₀ (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) := by
    funext x
    rw [inv_inv, inv_one]
    exact datum_move R i Q ξR y₀ e hmSt hredQ (fun PP hPP => by rw [hredPg PP hPP, inv_inv]; exact hgmul PP hPP) x
  rw [hΦ] at hth'
  refine ⟨ω (m⁻¹, 1) φ₁, ⟨hvac, e, hIS, hth'⟩, m⁻¹, inv_mem hmG, 1, by rw [map_one, one_smul], isIntegral_one,
    by rw [inv_one]; exact isIntegral_one, one_ne_zero, fun h _ w hw => inCoefLat_mul R i (hC.lev.βV i) hmSt' h w hw⟩

end
