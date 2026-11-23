import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixIffJointlyBijectivePairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixPiIffForallEvalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentRealPlaceIffFrameUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentFiniteAdelesIffFrameUnipotentRadiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentScaledBasisColumnsMatrixTranspoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesFlagTie

open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

variable {D : D7}

theorem unip_joint {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂)
    (hinj : ∀ y, f y = 0 → g y = 0 → y = 0) (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) :
    Unip E K M ↔ Unip (E.map f) (K.map f) (M.map f) ∧ Unip (E.map g) (K.map g) (M.map g) :=
  GlobalTheory.T.isFlagUnipotentMatrix_iff_jointlyBijective_pair f g hinj hsurj E K M

theorem unip_pi {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) (ι → S))
    (K : Matrix (Fin ρ) (Fin n) (ι → S)) (M : Matrix (Fin n) (Fin n) (ι → S)) :
    Unip E K M ↔ ∀ i, Unip (E.map (Pi.evalRingHom (fun _ => S) i)) (K.map (Pi.evalRingHom (fun _ => S) i))
      (M.map (Pi.evalRingHom (fun _ => S) i)) :=
  GlobalTheory.T.isFlagUnipotentMatrix_pi_iff_forall_eval E K M

theorem unip_real (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) ℂ) :
    Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
    InN (I.ε v) (fun a => rv I v (x a)) (rv I v z) ((I.P v)⁻¹ * N * I.P v) :=
  GlobalTheory.T.isFlagUnipotent_realPlace_iff_frame_unipotentRadical I v x c z hc hz N

theorem unip_fin (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔
    ((∀ a : Fin ρ, (N - 1) *ᵥ incl I (x a) ∈
        Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (x b)) '' {b | b.1 < a.1})) ∧
    (N - 1) *ᵥ incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b)) ∧
    ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b))) :=
  GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical I x c z hc hz N

theorem eM_linIndep (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) (ht : t ≠ 0)
    (hl : lam ≠ 0) : LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose :=
  GlobalTheory.T.linearIndependent_scaledBasisColumnsMatrix_transpose X h t lam ht hl

theorem unip_congr {R : Type} [CommRing R] {n ρ : ℕ} {E E' : Matrix (Fin n) (Fin ρ) R}
    {K K' : Matrix (Fin ρ) (Fin n) R} {M M' : Matrix (Fin n) (Fin n) R} (hE : E = E') (hK : K = K') (hM : M = M') :
    Unip E K M ↔ Unip E' K' M' := by
  subst hE hK hM; rfl

theorem castGA_self {I : Formalism.MainNotions.S.AutInst} (e : I = I) (x : I.GA) : castGA e x = x := rfl

theorem thetaV_incA (v : InfinitePlace (Formalism.L2.SG.InstExistsPf.instOf D).F) (y : D.host.E) :
    thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D y) = (Formalism.L2.SG.InstExistsPf.instOf D).φ v y := by
  have := thetaV_tmul (Formalism.L2.SG.InstExistsPf.instOf D) v 1 y
  rw [map_one, one_mul] at this
  exact this

theorem tauF_incA (y : D.host.E) :
    tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y := by
  exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y

theorem core (D : D7) {ρ : ℕ} (x : Fin ρ → Fin (D.sp.Y 0).rank → D.host.E) (c : Fin ρ → D.host.E)
    (z : Fin (D.sp.Y 0).rank → D.host.E) (hc : ∀ a, c a ≠ 0)
    (hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J (x a) z = 0)
    (hLI : LinearIndependent D.host.E (Matrix.of fun k a => c a * x a k).transpose) (g : GA D (D.sp.Y 0)) :
    g ∈ NFlag (D.sp.Y 0) (Matrix.of fun k a => c a * x a k) ↔
      (Formalism.IndefR.RationalEmbedding.iota D g).1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) x z ∧
        (Formalism.IndefR.RationalEmbedding.iota D g).2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) x z := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  refine (GlobalTheory.BesselChar.mem_NFlag_iff _ _ hLI g).trans ?_
  refine (unip_joint (A := AF D.host.F ⊗[D.host.F] D.host.E) (Pi.ringHom fun v => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v)
      (tauF (Formalism.L2.SG.InstExistsPf.instOf D))
      (fun y h1 h2 => Formalism.L2.SG.Pf.TT_ext _ y (fun v => congr_fun h1 v) h2)
      (fun a b => by
        obtain ⟨y, h1, h2⟩ := Formalism.L2.SG.Pf.TT_surj (Formalism.L2.SG.InstExistsPf.instOf D) a b
        exact ⟨y, funext h1, h2⟩) _ _ _).trans ?_
  refine (and_congr_left' (unip_pi _ _ _)).trans ?_
  refine and_congr (forall_congr' fun v => ?_) ?_
  · have hR := unip_real (Formalism.L2.SG.InstExistsPf.instOf D) v x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (thetaV (Formalism.IndefR.RationalEmbedding.inst D) v))
    refine (unip_congr (Matrix.ext fun k a => thetaV_incA v _) (Matrix.ext fun k a => thetaV_incA v _)
      (Matrix.ext fun k a => rfl)).trans (hR.trans ?_)
    show _ ↔ InN _ _ _ (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v))
    rw [hb1 v]
    rfl
  · have hF := unip_fin (Formalism.L2.SG.InstExistsPf.instOf D) x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (tauF (Formalism.IndefR.RationalEmbedding.inst D)))
    refine (unip_congr (Matrix.ext fun k a => tauF_incA _) (Matrix.ext fun k a => tauF_incA _)
      (Matrix.ext fun k a => rfl)).trans (hF.trans ?_)
    show _ ↔ (_ ∧ _ ∧ _)
    rw [hb2]
    rfl

theorem transport (D : D7) (I : Formalism.MainNotions.S.AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) {ρ : ℕ} (eR : Fin ρ → Fin I.n → I.E)
    (zR : Fin I.n → I.E) (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Ninf I eR zR ↔ s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ((castGA hI.symm s).2 ∈ Nfin I eR zR ↔ s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ∀ p q : Fin I.n → I.E, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => ιE (p (Fin.cast hr k))) (fun k => ιE (q (Fin.cast hr k))) =
        ιE (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  have hx : (fun a k => ιE (eR a (Fin.cast hr k))) = eR := funext fun a => hv (eR a)
  refine ⟨?_, ?_, fun p q => ?_⟩
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · exact (congrArg₂ (fun A B => Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J A B)
      (hv p) (hv q)).trans (hid _).symm

theorem mem_flagN_iff : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u := by
  intro D X h u t lam ht hl hId V₀ d hd n
  have hLI := eM_linIndep X h t lam ht hl
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have horth : ∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.zR u) = 0 := by
    intro a
    apply X.ιE.injective
    show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (X.eX a)) (X.crd (X.zu u))) = X.ιE 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, map_zero]
    exact (X.zu_orth u a).1
  have hT := transport D X.B.I X.ιE hId h (rank_eq X h) X.eR (X.zR u) (Formalism.IndefR.RationalEmbedding.iota D n)
  have hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) = 0 :=
    fun a => by rw [hT.2.2, horth a, map_zero]
  have hcore := core D (fun a k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (GlobalTheory.Core.SBesEx.scl t lam)
    (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) hsc hz hLI n
  show n ∈ NFlag (D.sp.Y 0) d.e ↔ _
  rw [hd]
  exact hcore.trans (and_congr hT.1.symm hT.2.1.symm)

end GlobalTheory.Core.SBesFlagTie
