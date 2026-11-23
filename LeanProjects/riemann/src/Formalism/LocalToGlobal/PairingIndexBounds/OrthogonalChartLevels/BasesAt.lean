import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.SharpRestriction.GrowthBounds.ChartComparison

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

def basesAt (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) :=
  Classical.epsilon fun g => (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt =
    colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _)

def reGL {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) : GL m R →* GL n R :=
  Units.map (Matrix.reindexAlgEquiv R R e : Matrix m m R ≃ₐ[R] Matrix n n R).toMonoidHom

structure PtCh (n : ℕ) (X : Sys (D.what₂.places.resChar w)) where
  J : Matrix (Fin n) (Fin n) D.host.E
  Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
  y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  B : GL (Fin n) D.host.E
  iw : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v

def chAt : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → PtCh (D := D) (w := w) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (sysAt Ch std vp unif eO eO_spec dG dG_spec om)
  | 0, La =>
    { J := J0.reindex (finCongr A0.rk.symm) (finCongr A0.rk.symm)
      Lb := Lb0.map (((reE (E := D.host.E) (n := ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj 0).m + 1) (by exact A0.rk.symm) : _ ≃ₗ[D.host.E] _) : _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))
      Uloc := fun v => (Uloc0 v).map (reGL (finCongr A0.rk.symm))
      y := reGL (finCongr A0.rk.symm) (Classical.epsilon fun x => A0.IsPt La.1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) J0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      B := reGL (finCongr A0.rk.symm) A0.B
      iw := A0.iw }
  | i + 1, La =>
    if hi : i + 1 ≤ D.R.m then
      { J := (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
            (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
        Lb := ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
          (((reE (E := D.host.E) (n := ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) (by exact ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm) : _ ≃ₗ[D.host.E] _) :
            _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))
        Uloc := fun v => (((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Uloc v).map
          (reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm))
        y := reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
          (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
            (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
            x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        B := reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
          ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).B
        iw := ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).iw }
    else
      { J := 1, Lb := Submodule.span (𝓞 D.host.E) (Set.range fun k => Pi.single k (1 : D.host.E)), Uloc := fun _ => ⊤, y := 1, B := 1,
        iw := A0.iw }

def cpAt : ChartPts (sysAt Ch std vp unif eO eO_spec dG dG_spec om) D where
  N := fun j _ => ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1
  hk := fun _ _ => rfl
  J := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).J
  Lb := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).Lb
  Uloc := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).Uloc
  y := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).y
  B := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).B
  iw := fun j La => (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 j La).iw

def fdAt (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FData (sysAt Ch std vp unif eO eO_spec dG dG_spec om) D :=
  fdOfCharts (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0) a bad

end Formalism.L2.PairingIndexBounds.F
