import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagTorusAlgebraicallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotRedDouble

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CompanionTheory.Ar.FlagPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ}

section Point

variable (C : FlagCpt Z e) (P : FrPt Xo c (CAt σ))

def Over (y : CxPts C.Y.str (σ.comp e.toRingHom)) : Prop :=
  y.1 ≫ C.π = GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ ∧ C.Carries (k := ℂ) (φ := σ) y.1 (frameOf (R := CAt σ) Z P)

variable {C P}

theorem comp_str {p : Sp ℂ ⟶ C.Y.X} (h : (p ≫ C.π) ≫ genStr Z = spMap σ) :
    p ≫ C.Y.str = spMap (σ.comp e.toRingHom) := by
  rw [← C.π_str, ← Category.assoc, ← Category.assoc, h]
  exact (Spec.map_comp _ _).symm

theorem comp_genStr (y : CxPts C.Y.str (σ.comp e.toRingHom)) : (y.1 ≫ C.π) ≫ genStr Z = spMap σ := by
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
  have h3 : spMap (σ.comp e.toRingHom) ≫ spMap e.symm.toRingHom = spMap σ := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    exact CommRingCat.hom_ext (RingHom.ext fun a => congrArg σ (e.apply_symm_apply a))
  have h4 : y.1 ≫ C.π ≫ genStr Z ≫ spMap e.toRingHom = spMap (σ.comp e.toRingHom) := by
    rw [C.π_str]; exact y.2
  refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h4).trans h3)
  simp only [Category.assoc, h2, Category.comp_id]

variable (C) in

def basePt (y : CxPts C.Y.str (σ.comp e.toRingHom)) : CxPts (genStr Z) σ := ⟨y.1 ≫ C.π, comp_genStr y⟩

theorem carriedC_iff : CarriedC C P ↔ ∃ y, Over C P y :=
  ⟨fun ⟨p, hp, hc⟩ => ⟨⟨p, comp_str (by rw [hp]; exact Horiz.ptF_jQ_over Z P)⟩, hp, hc⟩,
    fun ⟨y, hy⟩ => ⟨y.1, hy⟩⟩

theorem carries_frameCast_iff {k : Type} [Field k] {φ : c.F →+* k} {x x' : Sp k ⟶ Z.X} (h : x = x')
    {p : Sp k ⟶ C.Y.X} {g : EigFrame Z φ x} : C.Carries p (Horiz.frameCast h g) ↔ C.Carries p g := by
  subst h
  rfl

theorem over_iff_cxOf {y : CxPts C.Y.str (σ.comp e.toRingHom)} :
    Over C P y ↔ y.1 ≫ C.π = (Horiz.cxOf Z P).1.1 ∧ C.Carries y.1 (Horiz.cxOf Z P).2 :=
  and_congr_right fun _ => (carries_frameCast_iff (φ := σ) (Category.assoc _ _ _).symm).symm

variable (C P)

theorem nonempty_cxPts (σ : c.F →+* ℂ) : Nonempty (CxPts C.Y.str (σ.comp e.toRingHom)) :=
  (GlobalTheory.CxPtsDense.nonempty_and_dense F C.Y _).1

def ptOf : CxPts C.Y.str (σ.comp e.toRingHom) :=
  haveI := nonempty_cxPts C σ
  Classical.epsilon (Over C P)

variable {C P}

theorem over_ptOf (hc : CarriedC C P) : Over C P (ptOf C P) :=
  Classical.epsilon_spec (carriedC_iff.1 hc)

end Point

section Flag

variable {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U)

open Classical in

def pr (k : U.Comp) (x : Frame (U.X k).Ψ N) : CxPts (Φ.C k).Y.str (σ.comp e.toRingHom) :=
  if h : x ∈ (U.X k).dom then ptOf (Φ.C k) (U.un k ⟨x, h⟩) else (nonempty_cxPts (Φ.C k) σ).some

theorem pr_coe (k : U.Comp) (x : (U.X k).dom) : pr Φ k x.1 = ptOf (Φ.C k) (U.un k x) := dif_pos x.2

theorem exists_carriedC (P : FrPt Xo c (CAt σ)) : ∃ k, CarriedC (Φ.C k) P := by
  obtain ⟨⟨i, p⟩, h, -⟩ := Φ.lifts ℂ σ (Horiz.cxOf Z P).1.1 (Horiz.cxOf Z P).1.2 (Horiz.cxOf Z P).2
  exact ⟨i, carriedC_iff.2 ⟨⟨p, comp_str (h.1 ▸ (Horiz.cxOf Z P).1.2)⟩, over_iff_cxOf.2 h⟩⟩

variable {Φ} {k : U.Comp} {x : (U.X k).dom}

theorem over_pr (hc : CarriedC (Φ.C k) (U.un k x)) : Over (Φ.C k) (U.un k x) (pr Φ k x.1) :=
  pr_coe Φ k x ▸ over_ptOf hc

theorem pr_π (hc : CarriedC (Φ.C k) (U.un k x)) :
    (pr Φ k x.1).1 ≫ (Φ.C k).π = GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ Z.jQ := (over_pr hc).1

variable (Φ)

example [Subsingleton U.Comp] (k : U.Comp) (x : (U.X k).dom) : Over (Φ.C k) (U.un k x) (pr Φ k x.1) := by
  obtain ⟨i, h⟩ := exists_carriedC Φ (U.un k x)
  exact over_pr (Subsingleton.elim i k ▸ h)

example (k : U.Comp) (x x' : (U.X k).dom) (h : U.un k x = U.un k x') : pr Φ k x.1 = pr Φ k x'.1 := by
  rw [pr_coe, pr_coe, h]

end Flag

example {D : Formalism.BasicNotions.D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp)
    (x : ((s.U κ.σ₀).X k).dom) : Over (Φ.C k) ((s.U κ.σ₀).un k x) (pr Φ k x.1) := over_pr (carriedC_un s Φ k x)

end GlobalTheory.CompanionTheory.Ar.FlagPt
