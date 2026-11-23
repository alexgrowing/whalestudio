import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCovPinNotIsXiDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare
  GlobalTheory.HalfOnRecord
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoversOnRecord

variable {D : D7}

section General

variable {H : ModHost D} {Dw : Datum H} {l : Level H} {r : ℕ}

def IsBaseFrame (Dw : Datum H) (V : HSp D) (hr : V.rank = r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
    gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)

def XiValue {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
          (IntermediateField.inclusion d.c₂.le).toRingHom)
        (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
      (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
      (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
        rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2 = ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

def Covers {T0 : Type} (L : LevCh D T0) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ (dδ : T0 → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((inC c).comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (dδ t).I = coverHalf D (L.Q t) ∧ IsCoverHalf l (L.Q t) (dδ t).pd (dδ t).I (dδ t).l₂) ∧
    CovPin Xo c dδ ∧
    (∀ t, HalfAt L.Pg (L.Q t) l.Mb (dδ t).I) ∧
    (∀ t (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x →
      ((xi t (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((L.xi t x : Circle) : ℂ)) ∧
    CXiVal V hr (inC c) dδ U₂ dict₂ ι x₀ xi ∧
    (∀ t, XiValue (dδ t) V hr ι x₀ (U₂ t) (dict₂ t) (xi t)) ∧
    ∀ t, ∃ m : ℕ, 0 < m ∧ (dδ t).cδ ^ m = 1

end General

def recordPar (hF : OFull D) (hz : OZeta D) (P : PiBar D.host) : Par D :=
  Formalism.L2.Pj.parAt D hF hz GlobalTheory.Moduli.moduli_scheme_exists (designLevel P) (designLevel_spec P)

def IsReading (Q : Par D) (i : Fin D.R.m) (ι : (Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop :=
  LatEmb (Wc D i) ι ∧ LatIsom (Wc D i) (Q.Dw ((i : ℕ) + 1)).EF ι ∧ IsBaseFrame (Q.Dw ((i : ℕ) + 1)) (Wc D i) (rank_Wc i) x₀

def RowOn {T0 : Type} (L : LevCh D T0) (Q : Par D) (i : Fin D.R.m)
    (ι : (Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop :=
  ∃ c₁ : Coeff Q.l, Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
    ∀ c' : Coeff Q.l, c₁.F ≤ c'.F → Covers L (Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank (Wc D i) (rank_Wc i) ι x₀

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

end Rec

def RowOnRecord (D : D7) (hF : OFull D) (hz : OZeta D) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) [Finite T0] (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ i : Fin D.R.m, (∃ ι x₀, IsReading (recordPar hF hz R.C.P) i ι x₀) ∧
      ∀ ι x₀, IsReading (recordPar hF hz R.C.P) i ι x₀ → (QGuard R ↔ RowOn R.toLevCh (recordPar hF hz R.C.P) i ι x₀)

end GlobalTheory.CoversOnRecord
