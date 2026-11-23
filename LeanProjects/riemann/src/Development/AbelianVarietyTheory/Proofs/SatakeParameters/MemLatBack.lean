import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Apx

variable {D : D7} {X : Fields} (s : Seam D X)

def apxAt {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (k : GL (Fin N) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Sp X.E N ≃ₗ[X.E] Sp X.E N :=
  Classical.epsilon fun g : Sp X.E N ≃ₗ[X.E] Sp X.E N => NearAt (seamP s P) n k (seamGL s g)

def seamVec (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by
    funext l
    simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

def latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 X.E) (Sp X.E n) :=
  L.comap (seamVec s n)

theorem mem_latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Sp X.E n) :
    y ∈ latBack s L ↔ (fun l => s.iE (y l)) ∈ L := Iff.rfl

end Apx

section Ad

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def fnlIota (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal :=
  Classical.epsilon fun ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal =>
    ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

def latAdX (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  latBack t.seam (latCo D.sp (gramN D i hi) (A.crd i hi) a x ((St i hi).K β).lev.Lb)

open Classical in

def fnlLat (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u))
    (w : Sp t.X.E (D.R.N i)) : 𝓞 t.X.E ⧸ P.1.asIdeal :=
  if hv : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) ∧ (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal then
    if hz : ∃ z : latS (F := D.host.F) (hv.choose.adicCompletion D.host.F) (intV D.host.E hv.choose)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ((St i hi).K β).lev.Lb)),
        z.1 = fun l => prV (E := D.host.E) hv.choose
          (pullV (F := D.host.F) (ratA D.host.F (A.crd i hi) * x) (fun k => t.seam.iE (w k)) l) then
      fnlIota A i hi β P hv.choose hv.choose_spec.2 (((St i hi).K β).lev.fT hv.choose hv.choose_spec.2 hz.choose)
    else 0
  else 0

open Classical in

def fnlAd (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u))
    (w : Sp t.X.E (D.R.N i)) : 𝓞 t.X.E ⧸ P.1.asIdeal :=
  if hs : ∃ s : 𝓞 t.X.E, s ∉ P.1.asIdeal ∧ s • w ∈ latAdX A a i hi β x then
    Ring.inverse (Ideal.Quotient.mk P.1.asIdeal hs.choose) * fnlLat A i hi β x P (hs.choose • w)
  else 0

open Classical in

def phiAd (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (x' : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) : t.X.K :=
  if ∀ P : t.Pr.vT (t.word u), ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (latAdX A a i (Nat.le_of_succ_le hi) β x),
      w y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (latAdX A a (i + 1) hi β' x') ∧
        fnlAd A a (i + 1) hi β' x' P (w y) = fnlAd A a i (Nat.le_of_succ_le hi) β x P y then 1 else 0

def crdHom (i : ℕ) (hi : i + 1 ≤ D.R.m) (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) :=
  seamHom t.seam (inFr
    (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
    (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)

def frAd (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : SB t μ) :
    Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i) :=
  apxAt t.seam P.1 ((t.cst μ).D P) (ratA D.host.F (A.crd i hi) * x * ratA D.host.F (A.fb i hi β P))

def xiTopAd (hi : t.m2 + 1 + 1 ≤ D.R.m) : StepDatum St (t.m2 + 1) hi := fun β β' x x' z =>
  t.seam.σ₀ (phiAd A a (t.m2 + 1) hi β β' x.1 x'.1 (crdHom A (t.m2 + 1) hi z) *
    ∏ P : SB t μ,
      PhiTopG (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp (t.m2 + 1) (t.m2 + 1 + 1) (D.R.N (t.m2 + 1 + 1)) P.1
          (prXpG t.X.E (D.R.N (t.m2 + 1 + 1)) ∘ₗ
            inFr (frAd A (t.m2 + 1) (Nat.le_of_succ_le hi) β x.1 P) (frAd A (t.m2 + 1 + 1) hi β' x'.1 P) (crdHom A (t.m2 + 1) hi z) ∘ₗ
            LinearMap.funLeft t.X.E t.X.E (Fin.castAdd (cOf D.R (t.m2 + 1)))) *
        ftY t.sel (t.tup μ) (t.cst μ) P
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ
            inFr (frAd A (t.m2 + 1) (Nat.le_of_succ_le hi) β x.1 P) (frAd A (t.m2 + 1 + 1) hi β' x'.1 P) (crdHom A (t.m2 + 1) hi z))
          (A.y0 β P))

end Ad

end GlobalTheory.TwU

end
