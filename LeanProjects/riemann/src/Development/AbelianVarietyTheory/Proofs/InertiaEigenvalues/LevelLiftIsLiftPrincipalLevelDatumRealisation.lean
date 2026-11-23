import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (Vc Wc RealDat Face)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatVecSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType GlobalTheory.ExportType GlobalTheory.ConjTwist

variable {D : D7} {S T : HSp D}

theorem finite_H {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) : Finite P.H := inferInstance

def princG {r : ℕ} (G : TypeDat D r) : TypeDat D r := ⟨G.Pg, LevelP.triv _ _ _, G.mu⟩

def princ (B : Base S T) : Base S T := { B with G := princG B.G }

theorem princ_good {B : Base S T} (h : B.Good) : (princ B).Good :=
  ⟨h.even, h.odd, h.frame, h.de, h.places, h.wt, h.sig, h.sigOK, h.eta, h.hecke, h.real, h.unram, h.tame, h.inf⟩

open Classical in

theorem omegaG_princ {n r : ℕ} (G : TypeDat D r) (y : Reds D n r) :
    omegaG (princG G).levT (princG G).muC y = omegaK G.Pg y := by
  unfold omegaK
  split_ifs with h
  · rw [omegaG_levT_of (princG G) (fun PP hP => (h PP hP).1) 1 (fun PP => (h PP.1 PP.2).2.symm) (one_mem _)]
    have e : ((princG G).P.chi ⟨1, one_mem _⟩) = 1 := rfl
    rw [e, Finset.prod_eq_one fun PP _ => by rw [Pi.one_apply, map_one, map_one, Units.val_one, inv_one]]
    simp
  · refine omegaG_levT_zero _ fun ⟨h0, g, hg, hH⟩ => h fun PP hP => ⟨h0 PP hP, ?_⟩
    obtain rfl : g = 1 := Subgroup.mem_bot.1 hH
    exact (hg ⟨PP, hP⟩).symm

theorem low_top {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (K : GL (Fin r) κ) (u : Matrix (Fin n) (Fin r) κ) :
    LowZero r (u * K.val) ∧ topL r (u * K.val) = 1 ↔ LowZero r u ∧ (K⁻¹).val = topL r u := by
  have eK : u * K.val = ((1 : GL (Fin n) κ)).val * u * K.val := by rw [Units.val_one, Matrix.one_mul]
  rw [eK, GlobalTheory.AdjDatumMove.lowZero_mul_iff (one_mem _)]
  refine and_congr_right fun hu => ?_
  rw [GlobalTheory.AdjDatumMove.topL_mul hr (one_mem _) _ hu, show upperLeftBlock hr (1 : GL (Fin n) κ) = 1 from blockDiagonalExtendByOnePrimeField_one _ _,
    Units.val_one, Matrix.one_mul]
  exact ⟨fun h => (Units.eq_inv_of_mul_eq_one_right h).symm, fun h => by rw [← h]; exact K.inv_mul⟩

open Classical in

theorem omegaG_eq_sum {n r : ℕ} (hr : r ≤ n) (G : TypeDat D r) [Fintype G.P.H]
    (K : G.P.H → ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (hK : ∀ (p : G.P.H) (PP : ↥G.Pg), p.1 PP = K p PP.1) (y : Reds D n r) :
    omegaG G.levT G.muC y = ∑ p : G.P.H, (((G.P.chi p)⁻¹ * ∏ PP ∈ G.Pg, G.muC PP (GeneralLinearGroup.det (K p PP)) : ℂˣ) : ℂ) *
      omegaK G.Pg fun PP => y PP * (K p PP).val := by
  have key : ∀ p : G.P.H, (∀ PP ∈ G.Pg, LowZero r (y PP * (K p PP).val) ∧ topL r (y PP * (K p PP).val) = 1) ↔
      (∀ PP ∈ G.Pg, LowZero r (y PP)) ∧ ∀ PP : ↥G.Pg, ((p⁻¹ : G.P.H).1 PP).val = topL r (y PP.1) := fun p => by
    simp only [low_top hr]
    constructor
    · exact fun h => ⟨fun PP hP => (h PP hP).1, fun PP => by rw [← (h PP.1 PP.2).2, ← hK]; rfl⟩
    · exact fun h PP hP => ⟨h.1 PP hP, by rw [← h.2 ⟨PP, hP⟩, ← hK p ⟨PP, hP⟩]; rfl⟩
  by_cases hy : (∀ PP ∈ G.Pg, LowZero r (y PP)) ∧ ∃ g : G0 G.Pg r, (∀ PP : ↥G.Pg, (g PP).val = topL r (y PP.1)) ∧ g ∈ G.P.H
  · obtain ⟨h0, g, hg, hgH⟩ := hy
    rw [omegaG_levT_of G h0 g hg hgH, Finset.sum_eq_single (⟨g, hgH⟩ : G.P.H)⁻¹]
    · rw [omegaK, if_pos ((key _).2 ⟨h0, fun PP => by rw [inv_inv]; exact hg PP⟩), mul_one, map_inv, inv_inv, Units.val_mul,
        Units.coe_prod, ← Finset.prod_coe_sort G.Pg]
      congr 1
      refine Finset.prod_congr rfl fun PP _ => ?_
      rw [← hK, ← Units.val_inv_eq_inv_val, ← map_inv, ← map_inv]
      rfl
    · intro p _ hp
      rw [omegaK, if_neg, mul_zero]
      intro h
      refine hp (inv_eq_iff_eq_inv.1 (Subtype.ext (funext fun PP => Units.ext ?_)))
      exact (((key p).1 h).2 PP).trans (hg PP).symm
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [omegaG_levT_zero G hy, Finset.sum_eq_zero]
    intro p _
    rw [omegaK, if_neg, mul_zero]
    exact fun h => hy ⟨((key p).1 h).1, _, ((key p).1 h).2, (p⁻¹).2⟩

open Classical in
theorem vacC_one (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) (κ : GA D T) :
    vacC B ψ 1 κ = (∏ PP ∈ B.G.Pg, B.G.muC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ)))) *
      ((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ)))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ)))) := by
  unfold vacC
  simp only [map_one, redFn_one, inv_one, one_mul]
  rw [prod_allP hQ]
  congr 1
  · exact Finset.prod_congr rfl fun PP hP => by rw [resP_g hQ hP]
  congr 1
  · exact Finset.prod_congr rfl fun PP hP => by rw [resP_d hQ hP]
  · exact Finset.prod_congr rfl fun PP hP => by rw [resP_q hQ hP]

theorem locFn_mul (B : Base S T) (ψ : Twist D Circle) (K : ∀ PP : Pl D.host.E, GL (Fin T.rank) (kP PP))
    (y : Reds D T.rank S.rank) :
    B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) (fun PP => (K PP).val * y PP) =
      (((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (K PP))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (K PP)) : ℂˣ) : ℂ) * B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y := by
  unfold Base.locFn
  rw [Finset.prod_congr rfl fun PP _ => flat_mul B.hr _ _ (y PP),
    Finset.prod_congr (s₁ := Finset.univ) rfl fun (PP : ↥ψ.Q) _ => flat_mul B.hr _ _ (y PP.1),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_coe_sort ψ.Q]
  simp only [Units.val_mul, Units.coe_prod]
  ring

open Classical in

theorem datumFn_eq_sum (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) [Fintype B.G.P.H] (k : B.G.P.H → GA D T)
    (hk : ∀ p, Lifts B p.1 (k p)) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) x =
      ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ * vacC B ψ 1 (k p) : ℂˣ) : ℂ) *
        B.F.datumFn (princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) (actO S T 1 (k p)⁻¹ x) := by
  have st : ∀ p, Lev.finE T (k p)⁻¹ ∈ St B.F.βT := fun p => by rw [map_inv]; exact inv_mem (hk p).st
  have hO := fun p => frMapO_act B.F (one_mem_St S _) (st p) x
  have hJ := fun p => frMapAdj_act B.F (one_mem_St S _) (st p) x
  have hH : ∀ p, IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) (actO S T 1 (k p)⁻¹ x) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x :=
    fun p => ⟨GlobalTheory.ThetaMove.isHalf_of_act _ _, GlobalTheory.AdjDatumMove.isHalf_actO' _ _⟩
  have ri : ∀ p PP, redFn B.F.βT PP (Lev.finE T (k p)⁻¹) = (redFn B.F.βT PP (Lev.finE T (k p)))⁻¹ := fun p PP => by
    rw [map_inv, redFn_inv (hk p).st]
  unfold Frame.datumFn
  simp only [omegaG_princ, show (princG B.G).Pg = B.G.Pg from rfl, hH, fun p => (hO p).1, fun p => (hJ p).1]
  by_cases c1 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapAdj S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c1, zero_mul, mul_zero, Finset.sum_const_zero]
  by_cases c2 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapO S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c2, mul_zero, Finset.sum_const_zero]
  simp only [if_pos c1, if_pos c2]
  rw [omegaG_eq_sum B.hr B.G (fun p PP => redFn B.F.βT PP (Lev.finE T (k p))) (fun p => (hk p).red), Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [funext ((hO p).2 c2.2), funext ((hJ p).2 c1.2)]
  simp only [finE_one, ri, inv_inv, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rw [locFn_mul B ψ fun PP => (redFn B.F.βT PP (Lev.finE T (k p)))⁻¹, vacC_one B hQ]
  simp only [map_inv, Finset.prod_inv_distrib]
  generalize (∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T (k p))))) = a
  generalize (∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T (k p))))) = b
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  have := a.ne_zero
  have := b.ne_zero
  field_simp

open Classical in

theorem vecFlat_eq_sum_princ {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) [Fintype B.G.P.H] (k : B.G.P.H → GA D T) (hk : ∀ p, Lifts B p.1 (k p)) :
    B.vecFlat ψ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • ω (1, k p) ((princ B).vecFlat ψ) := by
  have hF := hB.frame
  have hsq := hQ.1.isOrthSum.1.idem
  have hinf := hQ.1.isOrthSum.1.infPart_eq
  have hM := Frame.isPlaceModel_placeMap hF hQ.1
  have hΛ : ∀ κ : GA D T, Lev.finE T κ ∈ St B.F.βT → ∀ u, u ∈ B.F.lat ↔ actO S T 1 κ u ∈ B.F.lat := fun κ hκ =>
    GlobalTheory.VecInv.mem_latO_iff hF.frS hF.frT (one_mem_St S _) hκ
  have hω' : ∀ y y', (∀ PP ∈ B.de.Q ∪ ψ.Q, y PP = y' PP) →
      B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hsb := Frame.isSBHalf_datumFn (G := princG B.G) hF hQ.1 hω'
  have hθ := Frame.isThetaAt_vec (G := princG B.G) hF hQ.1 hω'
  set Φ := B.F.datumFn (princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) with hΦ
  have mv : ∀ p, ω (1, k p) ((princ B).vecFlat ψ) = (((vacC B ψ 1 (k p) : ℂˣ) : ℂ) * 1) •
      B.F.placeMap (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) fun x => Φ (actO S T 1 (k p)⁻¹ x) := fun p => by
    have s := GlobalTheory.ThetaMove.isSBHalf_comp _ _ (hΛ (k p)⁻¹ (by rw [map_inv]; exact inv_mem (hk p).st)) hsb
    refine om_theta_move hω (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D _ hF.vac.1 S T _ _ hF.sdS hF.sdT _ hsq hinf _
      hF.vac.2.theta Tm hT Ψ hΨ) ⟨⟨_, hM⟩, fun _ h₂ => GlobalTheory.PlaceVec.placeModel_unique hF.vac.1 hF.sdS hF.sdT hsq hinf hM h₂ s⟩ hθ
      (hΛ _ (hk p).st) (Units.ne_zero _) (om_vac_base hB hS hψ hQ hω (one_mem _) (hk p).fin (one_mem_St S _) (hk p).st) fun x => ?_
    have := GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D S) (k p) x
    rw [inv_one] at this
    rw [one_mul, this]
  have e : B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) =
      ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ * vacC B ψ 1 (k p) : ℂˣ) : ℂ) • fun x => Φ (actO S T 1 (k p)⁻¹ x) := by
    funext x
    rw [datumFn_eq_sum B hQ k hk x, Finset.sum_apply]
    rfl
  rw [Base.vecFlat, Base.vecAt, Frame.vec, e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mv, map_smul, smul_smul, mul_one, Units.val_mul]

section Steps

open GlobalTheory.ExportSeries.Model GlobalTheory.AdelicLatMove GlobalTheory.TwoStepModel

theorem ct_ct {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) : ct (ct A) = A := by
  ext i j
  change cF D (cF D (A i j)) = A i j
  induction A i j using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => exact congrArg (· ⊗ₜ[D.host.F] e) (star_star y)

theorem int_of_int_adj {F : Frame S T} (hF : F.Good) {x : WO S T} (h : IsIntM (frMapAdj S T F.βS F.βT x)) :
    IsIntM (frMapO S T F.βS F.βT x) := by
  have g1 : ∀ V : HSp D, V.gram.map (eToEAf D) * (V.gram⁻¹).map (eToEAf D) = 1 := fun V => by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (Formalism.L2.Theta.gram_det_ne V)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have := int_ct (int_mul (int_mul (gram_frame_int S hF.sdS hF.frS).1 h) (gram_frame_int T hF.sdT hF.frT).2)
  rw [GlobalTheory.PlaceVec.frMapAdj_eq] at this
  change IsIntM (ct (_ * (_ * ct (x.map (toEAf D)) * _) * _)) at this
  have e : ∀ X : Matrix (Fin S.rank) (Fin T.rank) (EAf D),
      ct F.βS.val * S.gram.map (eToEAf D) * F.βS.val * ((F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) * X *
        (T.gram.map (eToEAf D) * F.βT.val)) * ((F.βT⁻¹).val * (T.gram⁻¹).map (eToEAf D) * ct (F.βT⁻¹).val) =
      ct F.βS.val * X * ct (F.βT⁻¹).val := fun X => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (S.gram.map _), g1, Matrix.one_mul,
      ← Matrix.mul_assoc F.βT.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (T.gram.map _), g1, Matrix.one_mul]
  rw [e, ct_mul, ct_mul, ct_ct, ct_ct, ct_ct, ← Matrix.mul_assoc] at this
  exact this

theorem idem_orth {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem Pg * idem Pg = idem Pg ∧ idem Q * idem Q = idem Q ∧ idem Q * cA D (idem Pg) = 0 ∧
      (∀ PP ∈ Pg, idemAt PP * cA D (idem Q) = 0 ∧ Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) ∧
      ∀ PP ∈ Q, idemAt PP * cA D (idem Pg) = 0 ∧ Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := by
  obtain ⟨P, h1, h2, hP⟩ := h.split
  have key : ∀ R ⊆ P, ∀ PP ∈ P, idemAt PP * cA D (idem R) = 0 := fun R hR PP hPP => by
    rw [idem, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => hP.mul_conj hPP (hR hj)
  refine ⟨GlobalTheory.PlaceVec.idemSum_mul_self (hP.mono h1).isIdemSum, GlobalTheory.PlaceVec.idemSum_mul_self (hP.mono h2).isIdemSum, ?_,
    fun PP hPP => ⟨key _ h2 _ (h1 hPP), hP.isIdemAt (h1 hPP)⟩, fun PP hPP => ⟨key _ h1 _ (h2 hPP), hP.isIdemAt (h2 hPP)⟩⟩
  rw [show idem Q = ∑ PP ∈ Q, idemAt PP from rfl, Finset.sum_mul]
  exact Finset.sum_eq_zero fun j hj => key _ h1 _ (h2 hj)

open Classical in

theorem datumFn_eq_tensor {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank} {Q : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Q)
    {ω : Reds D T.rank S.rank → ℂ} (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') :
    F.datumFn G Q ω = tensorHalf (idem Q) (cA D (idem G.Pg))
      (fun x => if IsHalf (cA D (idem G.Pg)) x ∧ IsIntM (frMapAdj S T F.βS F.βT x) then
        omegaG G.levT G.muC (fun PP => redM PP (frMapAdj S T F.βS F.βT x)) else 0)
      (fun x => if IsHalf (idem Q) x ∧ IsIntM (frMapO S T F.βS F.βT x) then
        ω (fun PP => redM PP (frMapO S T F.βS F.βT x)) else 0) := by
  obtain ⟨hg, hq, -, og, oq⟩ := idem_orth h
  have hg' : cA D (idem G.Pg) * cA D (idem G.Pg) = cA D (idem G.Pg) := by rw [← RingHom.map_mul, hg]
  have hq' : cA D (idem Q) * cA D (idem Q) = cA D (idem Q) := by rw [← RingHom.map_mul, hq]
  funext x
  rw [tensorHalf_apply, show idem Q + cA D (idem G.Pg) = halfIdem G.Pg Q from add_comm _ _, Frame.datumFn]
  by_cases hx : IsHalf (halfIdem G.Pg Q) x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1, zero_mul, mul_zero]
  have hxe : cA D (idem G.Pg) • x + idem Q • x = x := by
    rw [← add_smul]
    exact Matrix.ext fun i j => hx i j
  have i1 := isHalf_smul hg' x
  have i2 := isHalf_smul hq x
  rw [if_pos hx, mul_one]
  by_cases hi : IsIntM (frMapO S T F.βS F.βT x)
  · have hj := int_adj_of_int hF hi
    have k1 : IsIntM (frMapAdj S T F.βS F.βT (cA D (idem G.Pg) • x)) := by
      rw [frMapAdj_smul]; exact isIntM_smul_cA hg' hj
    have k2 : IsIntM (frMapO S T F.βS F.βT (idem Q • x)) := by
      rw [frMapO_smul]; exact isIntM_smul hq hi
    rw [if_pos ⟨hx, hj⟩, if_pos ⟨hx, hi⟩, if_pos ⟨i2, k2⟩, if_pos ⟨i1, k1⟩, mul_comm]
    congr 1
    · refine hω _ _ fun PP hPP => ?_
      have e : frMapO S T F.βS F.βT (idem Q • x) =
          frMapO S T F.βS F.βT x - toEAf D (cA D (idem G.Pg)) • frMapO S T F.βS F.βT x := by
        rw [← frMapO_smul, eq_sub_iff_add_eq', ← frMapO_add', hxe]
      rw [e, GlobalTheory.RedHalfDrop.redM_sub_smul PP hi (toEAf_mem_intAf_of_idem hg')
        (GlobalTheory.RedHalfDrop.resS_eq_zero_of_mul (oq PP hPP).2 _ (oq PP hPP).1)]
    · refine GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP => ?_
      have e : frMapAdj S T F.βS F.βT (cA D (idem G.Pg) • x) =
          frMapAdj S T F.βS F.βT x - toEAf D (cA D (idem Q)) • frMapAdj S T F.βS F.βT x := by
        rw [← frMapAdj_smul, eq_sub_iff_add_eq, ← GlobalTheory.PlaceVec.frMapAdj_add, hxe]
      rw [e, GlobalTheory.RedHalfDrop.redM_sub_smul PP hj (toEAf_mem_intAf_of_idem hq')
        (GlobalTheory.RedHalfDrop.resS_eq_zero_of_mul (og PP hPP).2 _ (og PP hPP).1)]
  · rw [if_neg (show ¬ (IsHalf (halfIdem G.Pg Q) x ∧ IsIntM (frMapO S T F.βS F.βT x)) from fun h => hi h.2), mul_zero]
    by_cases k2 : IsIntM (frMapO S T F.βS F.βT (idem Q • x))
    · rw [if_neg (show ¬ (IsHalf (cA D (idem G.Pg)) (cA D (idem G.Pg) • x) ∧
        IsIntM (frMapAdj S T F.βS F.βT (cA D (idem G.Pg) • x))) from fun k1 => hi ?_), mul_zero]
      rw [← hxe, frMapO_add']
      exact fun i j => add_mem (int_of_int_adj hF k1.2 i j) (k2 i j)
    · rw [if_neg fun h => k2 h.2, zero_mul]

open Classical in

theorem eq_vec_of_two_steps {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank} {Q : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Q)
    {ω : Reds D T.rank S.rank → ℂ} (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') {fg f : WO S T → ℂ}
    (h1 : IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (cA D (idem G.Pg)) F.lat 1 F.f₀
      (fun x => if IsHalf (cA D (idem G.Pg)) x ∧ IsIntM (frMapAdj S T F.βS F.βT x) then
        omegaG G.levT G.muC (fun PP => redM PP (frMapAdj S T F.βS F.βT x)) else 0) fg)
    (h2 : IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (idem Q) F.lat 1 fg
      (fun x => if IsHalf (idem Q) x ∧ IsIntM (frMapO S T F.βS F.βT x) then
        ω (fun PP => redM PP (frMapO S T F.βS F.βT x)) else 0) f) : f = F.vec G Q ω := by
  obtain ⟨hg, hq, ho, -, -⟩ := idem_orth h
  have hg' : cA D (idem G.Pg) * cA D (idem G.Pg) = cA D (idem G.Pg) := by rw [← RingHom.map_mul, hg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ F.lat, a • u ∈ F.lat := fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  obtain ⟨P, s1, -, hP⟩ := h.split
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red hF.sdS.1 hF.sdT.1
    (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart (hP.mono s1).isIdemSum)) (frMapAdj S T F.βS F.βT)
    (GlobalTheory.PlaceVec.frMapAdj_add S T _ _) (GlobalTheory.PlaceVec.frMapAdj_up S T _ _) (GlobalTheory.PlaceVec.frMapAdj_down S T _ _) G.Pg
    (omegaG G.levT G.muC) (GlobalTheory.PlaceDatum.omegaG_congr G.levT G.muC)
  have hM := Frame.isPlaceModel_placeMap hF h
  have hM' := hM
  rw [show halfIdem G.Pg Q = idem Q + cA D (idem G.Pg) from add_comm _ _] at hM'
  have m1 := isPlaceModel_comp_tensorHalf hq hg' ho hΛ hSB hM'
  have m2 := isPlaceModel_comp_restrictHalf hg' hq (by rw [mul_comm, ho]) hΛ hM
  have e := h1.2 _ m2
  rw [show idem Q + cA D (idem G.Pg) = halfIdem G.Pg Q from add_comm _ _] at m1
  rw [LinearMap.comp_apply] at e
  rw [← e] at m1
  rw [h2.2 _ m1, Frame.vec, datumFn_eq_tensor hF h hω]
  rfl

end Steps

theorem omegaFlat_eq_prod {r n : ℕ} (Q : Finset (Pl D.host.E)) (ξ : ResChars D ℂˣ) (y : Reds D r n) :
    omegaFlat Q r ξ y = ∏ PP ∈ Q, flat (ξ PP) (y PP) := by
  unfold omegaFlat
  split_ifs with h
  · rw [← Finset.prod_attach Q]
    exact Finset.prod_congr rfl fun PP _ => (flat_of_isUnit _ (IsUnit.unit_spec _).symm).symm
  · obtain ⟨PP, h1⟩ := not_forall.1 h
    obtain ⟨hP, h2⟩ := Classical.not_imp.1 h1
    exact (Finset.prod_eq_zero hP (flat_of_not_isUnit _ h2)).symm

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

open Classical in

theorem omegaFlat_eq_locFn {ψ : Twist D Circle} {t t₀ : T0} (ht : IsTupOf R B ψ t) (hL : R.toLevCh.Is t₀) (hB : B.Good)
    (hψ : ψ.Good) (hQ : B.admitted ψ.Q) (y : Reds D (Wc D i).rank (Vc D i).rank) :
    omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) y = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y := by
  have hx := fun PP => ht.xiR_eq hL hB hψ hQ (PP := PP)
  rw [omegaFlat_eq_prod, Base.locFn, Finset.prod_coe_sort ψ.Q fun PP => flat (ψ.resC PP) (y PP)]
  rw [ht.2] at hx ⊢
  rw [Finset.prod_union hQ.2]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => ?_
    rw [hx PP (Finset.mem_union_left _ hP), Twist.locC, Twist.locC, if_pos hP, if_neg (Finset.disjoint_left.1 hQ.2 hP), mul_one]
  · refine Finset.prod_congr rfl fun PP hP => ?_
    rw [hx PP (Finset.mem_union_right _ hP), Twist.locC, Twist.locC, if_pos hP, if_neg (Finset.disjoint_right.1 hQ.2 hP), one_mul]

open Classical in

theorem eq_vecFlat_princ (h : BaseOf R i B) {ψ : Twist D Circle} {t t₀ : T0} (ht : IsTupOf R B ψ t) (hL : R.toLevCh.Is t₀)
    (hB : B.Good) (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {f : WO (Vc D i) (Wc D i) → ℂ} (hf : IsFlatVec R i t f) :
    f = (princ B).vecFlat ψ := by
  obtain ⟨eg, eQ, fg, hg, hq, h1, h2⟩ := hf
  simp only [omegaFlat_eq_locFn ht hL hB hψ hQ] at h2
  rw [← idem_eq hg] at h1
  rw [← idem_eq hq, ht.2] at h2
  rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT] at h1 h2
  rw [← h.vac, ← h.Pg] at h1
  refine eq_vec_of_two_steps (G := princG B.G) hB.frame hQ.1 (fun y y' hy => ?_) (fg := fg) ?_ h2
  · unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  · simp only [omegaG_princ]
    exact h1

theorem levelLift_isLift_principalLevelDatum_realisation (h : BaseOf R i B) {p : G0 B.G.Pg (Wc D i).rank} {κ : GA D (Wc D i)}
    (hκ : Lev.IsLevelLift (Wc D i) B.F.βT B.G.levT p κ) :
    Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) κ)) κ := by
  refine ⟨hκ.1, mem_parLev.2 ⟨parLev_UA hκ.2.1, h.βT ▸ parLev_St hκ.2.1, fun PP _ => mem_blockTri.2 fun a b hab => ?_,
    fun PP hP => absurd hP (Finset.notMem_empty _)⟩, rfl⟩
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have ha : a.val < D.R.r := lt_of_lt_of_eq a.2 rW
  have e : blkOf D.R.r D.R.t a = 0 := if_pos ha
  exact absurd (lt_of_lt_of_eq hab e) (Nat.not_lt_zero _)

end Real

theorem vecFlat_eq_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B →
    Finite B.G.P.H ∧
    (∃ k : B.G.P.H → GA D (Wc D i), ∀ p, Lev.IsLevelLift (Wc D i) B.F.βT B.G.levT p.1 (k p) ∧ SuppAt (idem B.G.Pg) (Wc D i) (k p)) ∧
    ∀ [Fintype B.G.P.H] (k : B.G.P.H → GA D (Wc D i)), (∀ p, Lev.IsLevelLift (Wc D i) B.F.βT B.G.levT p.1 (k p)) →
      (∀ p, ∃ g0, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (k p)) ∧
      ∀ (ψ : Twist D Circle) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ), ψ.Good → B.admitted ψ.Q → IsTupOf R B ψ t → IsFlatVec R i t f →
        B.vecFlat ψ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • R.ωP i t (1, k p) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i B hB h
  refine ⟨finite_H _, ?_, fun k hk => ⟨fun p => ⟨_, levelLift_isLift_principalLevelDatum_realisation h (hk p)⟩, fun ψ t f hψ hQ ht hf => ?_⟩⟩
  · choose k hk using fun p : B.G.P.H => GlobalTheory.TypeSupportLift.exists_lift_supp B hB p.1
    exact ⟨k, hk⟩
  · rw [eq_vecFlat_princ h ht hC.lev hB hψ hQ hf]
    exact vecFlat_eq_sum_princ hB (D.sp.V_sig _) hψ hQ (h.isWeil hC.thP.ωP ht) k fun p => lifts_of_isLiftG0 (hk p)

end GlobalTheory.FlatVecSum

end
