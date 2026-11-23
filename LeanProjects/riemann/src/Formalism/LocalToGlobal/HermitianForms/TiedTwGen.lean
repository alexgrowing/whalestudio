import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def latCrd (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : letI := D.host.cmStar; Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  L.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

theorem clsCrd_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c = latCrd D i hi (D.clsLat u i c) := rfl

def badQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  badG D ∪ (Q : Set (HeightOneSpectrum (𝓞 D.host.F)))

variable {D : D7}

set_option maxHeartbeats 1000000 in

structure LevelChart (D : D7) (T : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (i : ℕ) (hi : i ≤ D.R.m) {cl : Type}
    (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad

  y : cl → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def ClsTied.toChart {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) :
    LevelChart D (D.mem u).A.T (badG D) i hi ((D.mem u).C.stab i) (clsCrd D u i hi) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def lamTG (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW (M.lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

theorem lamTG_fm (u : D.what₂.Word) (i : ℕ) : lamTG (D.fm u) i = lamT u i := rfl

set_option maxHeartbeats 1000000 in

structure ValuationCompatibleChart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (okW : D.what₂.places.Pl → Prop) {Ch : Type} (chOf : C.cls i → Ch) {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop where

  Fi : ∀ φ : C.cls i → C.Y i → ℂ, φ ∈ M.Fi i ↔
    ∀ β, (fun (c : {c // chOf c = β}) z => φ c.1 (eY.symm z)) ∈ FiC (K β).lev (embT D) (lamTG M i) (K β).y

  rat : ∀ φ : C.cls i → C.Y i → ℂ, (∃ x, M.emb i x = φ) ↔
    φ ∈ M.Fi i ∧ ∀ c, ∃ P ∈ RatSpan D (M.lam i), ∀ z, φ c z = fnOf _ (shiftOf (lamTG M i)) 1 P (eY z)

  lat : ∀ w, okW w → ∀ x : (M.lat i).V, x ∈ M.S i w ↔
    ∀ (c : C.cls i) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (lat c)) B →
      ∃ P ∈ IntSpan D w (M.lam i),
        ∀ z, M.emb i x c z =
          fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (eY z)

def IpVTieG {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi) : Prop :=
  ∀ c (o : Fr D i hi), o.IsON → ∀ P ∈ CSpan (M.lam i), ∀ Q ∈ CSpan (M.lam i),
    M.ipV i c
      (fun z => fnOf _ (shiftOf (lamTG M i)) (fun τ => (o.1 τ)⁻¹) P (eY z))
      (fun z => fnOf _ (shiftOf (lamTG M i)) (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
    nfAll (M.lam i) Q P

def NormTieG {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (M.lat i).V)
    (Pc : C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, M.emb i x c z =
      fnOf _ (shiftOf (lamTG M i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (M.lat i).b (M.lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, (C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamTG M i) τ)) *
          (nfAll (M.lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

set_option maxHeartbeats 1000000 in

structure DilationCompatibleChart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    {Ch : Type} (chOf : C.cls i → Ch) {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop where
  ch : ∀ v a c, chOf (M.dil i v a c) = chOf c
  dil : ∀ v (a : (A.Fv v)ˣ) (k : ℤ), (k : A.Fv v) = a → ∀ β (c : {c // chOf c = β}) δ,
    IsDia (K β).lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' ((K β).y ⟨M.dil i v a c.1, (ch v a c.1).trans c.2⟩) : Cls (K β).lev) = Quotient.mk'' ((K β).y c * δ)
  dilT : ∀ v (a : (A.Fv v)ˣ) (k : ℤ), (k : A.Fv v) = a → ∀ β (c : {c // chOf c = β}) δ,
    IsDia (K β).lev (eV v).1 (eV v).2 k δ → ∀ g ∈ AdFun (K β).lev (embT D),
    M.dilT i v a c.1 (fun z => g ((K β).y ⟨M.dil i v a c.1, (ch v a c.1).trans c.2⟩) (eY z)) =
      fun z => g ((K β).y c * δ) (eY z)

end Gen

end Formalism.L2.Forms
