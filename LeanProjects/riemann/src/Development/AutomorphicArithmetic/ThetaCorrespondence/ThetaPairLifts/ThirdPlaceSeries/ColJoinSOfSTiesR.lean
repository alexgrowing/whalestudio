import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section SpOf
end SpOf
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
def spectralRowIsometry (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G :=
  Classical.choose (S.rowTie hF)
theorem eHH_sEE_eq_conjHH_isometryOfJoin (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (F : D.what₂.EE) :
    (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF F) :=
  Classical.choose_spec (S.rowTie hF) F
theorem isometryOfJoin_eq_of_conj_compat (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G)
    (hj : ∀ F, (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (j F)) : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF = j := by
  ext1 F
  apply (conjHH S.X S.G).injective
  rw [← _root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF F, hj F]
theorem colJoinS_of_spectral_ties_real (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : ColJoinS hF (S.hI hF) S.tr :=
  colJoinS_of_pin hF (S.hI hF) S.tr S.into S.bij fun u x =>
    (LinearEquiv.eq_symm_apply (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u))).2 (S.colPin hF u x)
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev complexRealisationJoinData {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) :=
  Q.Rl.toCx3 Q.F
structure IndefiniteRealisationJoin (R : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) where
  m : D.what₂.Word → (Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.Mem
  mPin : HEq m P.I.wU
  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.a (m u)) → ℂ)
  cF : (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Df1.nV P.A3.fam3.base3.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0
  eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj (twQ P)] (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).EE
  chainTie : ChainTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (σ := D.what₂.embLL) (m := m) (cφ := cφ) (cF := cF)
  v0Surjective : GoodPartHasComplexCoordinates (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (cF := cF)
  rowTie : RowTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (eV := Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) (s := twQ P) (σ := D.what₂.embLL) (cF := cF) (eR := eR)
  colNorm : ColNormT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (s := twQ P) (m := m) (cφ := cφ)
  pairTie : ∀ hF : FinX S.Y, PairTieT (X := S.X) (G := S.G) (j := _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) (Tr := S.tr) (hK := S.Y.hK) (Dt := S.Y.Dt)
    (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (sEE := Q.sEE) (s := twQ P) (m := m) (cφ := cφ) (eR := eR)
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem embedding_eq_cj_twQ_embLL (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (a : D.what₂.LL) :
    P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj (twQ P) (D.what₂.embLL a) :=
  twist_of_mk D.what₂.embLL P.A3.A.v0 Q.Rl.hv0 a
def IndefiniteRealisationJoin.toJoinAt (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) :
    JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) Q.F.fc (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE (twQ P) D.what₂.embLL where
  m := J.m
  cφ := J.cφ
  cF := J.cF
  eR := J.eR
  twist := _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL Q
  chainTie := J.chainTie
  v0Surjective := J.v0Surjective
  rowTie := J.rowTie
  colNorm := J.colNorm
  pairTie := J.pairTie
end Real
end Formalism.L2.SG.JoinSI
end
end
