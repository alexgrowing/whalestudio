import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.TwoLat

namespace GlobalTheory.OrthFilt

section General

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} {L : X.Modules} {g : ℕ}
  {E E' : ι → X.Modules} {r : ι → ℕ}

def OrthEmb (hL : VMetric p L g) (h : ∀ a, VMetric p (E a) (r a)) (T : ∀ a, E a ⟶ L) : Prop :=
  (∀ a σ (V : X.Opens) (s t : Γ(E a, V)), ∀ y ∈ CxPts.ptsIn p σ V,
    (hL.met σ).form ((T a).app V s) ((T a).app V t) y = ((h a).met σ).form s t y) ∧
  ∀ a b, a ≠ b → ∀ σ (V : X.Opens) (s : Γ(E a, V)) (t : Γ(E b, V)), ∀ y ∈ CxPts.ptsIn p σ V,
    (hL.met σ).form ((T a).app V s) ((T b).app V t) y = 0

def Adapted (T : ∀ a, E a ⟶ L) (fl : ∀ a, Vert.Flag (E a) (r a)) (w : Vert.Flag L g) (e : (Σ a, Fin (r a)) ≃ Fin g) : Prop :=
  (∀ a, StrictMono fun i : Fin (r a) => e ⟨a, i⟩) ∧
  ∀ z : Σ a, Fin (r a), ∃ t : (fl z.1).F z.2.succ ⟶ w.F (e z).succ, t ≫ w.ι (e z).succ = (fl z.1).ι z.2.succ ≫ T z.1

def IsGraded (hL : VMetric p L g) {m : ℕ} (o : ι ≃ Fin m) (h : ∀ a, VMetric p (E a) (r a)) (u : ∀ a, E a ⟶ E' a) : Prop :=
  ∃ (F : Fin (m + 1) → X.Modules) (j : ∀ i, F i ⟶ L) (s : ∀ i : Fin m, F i.castSucc ⟶ F i.succ)
    (κ : ∀ a, F (o a).succ ⟶ E' a) (t : ∀ a, E a ⟶ F (o a).succ) (z : ∀ a, s (o a) ≫ κ a = 0),
    (∀ i, IsSubbundle (j i) ∧ ∃ n, IsVB (F i) n) ∧ Limits.IsZero (F 0) ∧ IsIso (j (Fin.last m)) ∧
    (∀ i, s i ≫ j i.succ = j i.castSucc) ∧ (∀ a, (ShortComplex.mk _ _ (z a)).ShortExact) ∧ (∀ a, t a ≫ κ a = u a) ∧
    OrthEmb hL h fun a => t a ≫ j (o a).succ

theorem orthEmb_id (hL : VMetric p L g) : OrthEmb (ι := Unit) (E := fun _ => L) hL (fun _ => hL) fun _ => 𝟙 L :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ h => (h rfl).elim⟩

theorem adapted_id (w : Vert.Flag L g) :
    Adapted (ι := Unit) (E := fun _ => L) (r := fun _ => g) (fun _ => 𝟙 L) (fun _ => w) w (Equiv.uniqueSigma _) :=
  ⟨fun _ => strictMono_id, fun _ => ⟨𝟙 _, (Category.id_comp _).trans (Category.comp_id _).symm⟩⟩

theorem isGraded_rank_one (hL : VMetric p L 1) :
    ∃ (w : Vert.Flag L 1) (u : L ⟶ w.gr 0), IsIso u ∧
      IsGraded (ι := Unit) (E := fun _ => L) (E' := fun _ => w.gr 0) hL (Equiv.ofUnique Unit (Fin 1)) (fun _ => hL) fun _ => u := by
  obtain ⟨w⟩ : Nonempty (Vert.Flag L 1) := ⟨.ofRankOne hL.isVB⟩
  have := w.isIso_last
  have hz : Limits.IsZero (w.F 0) := isVB_zero_iff.1 (w.isVB 0)
  have hπ : IsIso (w.π 0) := by
    rw [Vert.Flag.π]
    have e : w.step 0 = 0 := hz.eq_of_src _ _
    exact Limits.coequalizer.π_of_eq e
  refine ⟨w, inv (w.ι (Fin.last 1)) ≫ w.π 0, @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hπ, w.F, w.ι, w.step, fun _ => w.π 0,
    fun _ => @inv _ _ _ _ (w.ι (Fin.last 1)) this, fun _ => Limits.cokernel.condition _, fun i => ⟨w.isSubbundle i, _, w.isVB i⟩, hz, this,
    w.step_ι, fun _ => VMetric.stepSeq_shortExact w 0, fun _ => rfl, ?_⟩
  have e : inv (w.ι (Fin.last 1)) ≫ w.ι (Fin.last 1) = 𝟙 L := IsIso.inv_hom_id _
  change OrthEmb hL (fun _ => hL) fun _ : Unit => inv (w.ι (Fin.last 1)) ≫ w.ι (Fin.last 1)
  rw [e]
  exact orthEmb_id hL

def SameMet {k' : Type} [CommRing k'] (φ : k ≃+* k') {p' : X ⟶ Sp k'} (h : VMetric p' L g) (h₀ : VMetric p L g) : Prop :=
  ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ) (y : CxPts p' (σ.comp φ.symm.toRingHom)), y.1 = y₀.1 → ∀ c : Chart L g,
    y₀ ∈ CxPts.ptsIn p σ c.U → (h₀.met σ).G c y₀ = (h.met (σ.comp φ.symm.toRingHom)).G c y

def pairPol [Fintype ι] (r : ι → ℕ) (n : ℕ) : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ :=
  (∑ z, MvPolynomial.X (Sum.inr z) ^ 2) * rename Sum.inl (MixDens.vdm r) * (-∑ z, MvPolynomial.X (Sum.inr z)) ^ n

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open GlobalTheory.ArLieBase GlobalTheory.VdmRec

variable {D : D7} (O : Setup D)

def intEquiv : 𝓞 D.what₂.LL ≃+* 𝓞 O.κ.c.F := RingOfIntegers.mapRingEquiv O.κ.e

variable {O} in

abbrev strL {c : O.s.Comp} (M : DRBase O c) : M.B ⟶ Sp (𝓞 D.what₂.LL) := M.q ≫ spMap (intEquiv O).toRingHom

def PairAt (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → Bs.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB)
    (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB) (G : ∀ σ', EigMet O.s.T.Z σ') : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (t σ)) ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E' σ) _ σ false (t' σ)) ∧
    (∀ σ, Matches O.s.T.Z jB πB (u σ) (t σ) (t' σ)) ∧
    (∀ σ, IsLieLat O.s.T.Z O.κ.e jB πB (E σ) _ σ (ArIn.ind ∅) (fun _ => True) (t σ)) ∧
    (∀ σ, IsGrLat O.s.T.Z O.κ.e jB πB (E' σ) _ σ (t' σ)) ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    (∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E σ) _ σ false rfl G (h σ) (t σ)) ∧
    ∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E' σ) _ σ false rfl G (h' σ) (t' σ)

theorem pairBase_iff (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → Bs.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ) :
    PairBase O R c q E E' h h' u ↔ ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (t : _) (t' : _) (G : _),
      PairAt O R c q E E' h h' u jB πB t t' G :=
  ⟨fun ⟨Bg, jB, πB, pb, t, t', G, h⟩ => ⟨Bg, jB, πB, t, t', G, pb, h⟩,
    fun ⟨Bg, jB, πB, t, t', G, pb, h⟩ => ⟨Bg, jB, πB, pb, t, t', G, h⟩⟩

def PairCoverDeg (R : ℝ) (c : O.s.Comp) {B : Scheme.{0}} (q : B ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → B.Modules) {h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)}
    {h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)} (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf)
    (u : ∀ σ, E σ ⟶ E' σ) (d : ℕ) : Prop :=
  ∃ (V : Cover (O.var c)) (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ B) (ρ : V.X ⟶ Y) (w : ρ ≫ π ≫ q = V.p)
    (fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ))
    (fl' : ∀ σ, Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj (E' σ))) (O.S.Dw.mult σ)),
    V.deg = ρ.residueDegree (genericPoint V.X) * d ∧
    IsArithVar (π ≫ q) (O.var c).dim ∧ FlagChain.IsCov (π ≫ q) (O.var c).dim ρ ∧ IsFlagBundle π E O.S.Dw.mult fl ∧
    (∀ σ, Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map (u σ))) ((fl σ).pull ρ) (fl' σ)) ∧
    (∀ z : Letter O.S.Dw, V.Induces (lineAdl O R c (.inl (z.1, z.2)) 1)
      ((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ w) 1) ∧
    ∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z → V.Induces (lineAdl O R c (.inr k) 1)
      (VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ w)) 1

end GlobalTheory.OrthFilt

end
