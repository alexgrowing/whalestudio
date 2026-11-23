import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusPullOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkLoc

open GlobalTheory.Cartier.CartierDiv

section Sec

variable {X : Scheme.{0}} [IsIntegral X]

open Classical in

def locFn (D : CartierDiv X) (U : X.Opens) (f : X.functionField) (i : (toLB D).ι) : Γ(X, U ⊓ (toLB D).U i) :=
  if h : genericPoint X ∈ U ⊓ (toLB D).U i ∧ ∀ x ∈ U ⊓ (toLB D).U i, RegAt x (f * i.1.2) then
    (exists_fnOf_eq h.1 h.2).choose else 0

variable {D : CartierDiv X} {U : X.Opens} {f : X.functionField}

theorem fnOf_locFn (hf : ∀ x ∈ U, D.RegularAt x f) (i : (toLB D).ι) (h : genericPoint X ∈ U ⊓ (toLB D).U i) :
    fnOf _ h (locFn D U f i) = f * i.1.2 := by
  have h2 : ∀ x ∈ U ⊓ (toLB D).U i, RegAt x (f * i.1.2) := fun x hx =>
    (i.2.2 x hx.2).regularAt_iff.1 (hf x hx.1)
  rw [locFn, dif_pos ⟨h, h2⟩]
  exact (exists_fnOf_eq h h2).choose_spec

theorem locFn_mem (hf : ∀ x ∈ U, D.RegularAt x f) : locFn D U f ∈ secOn (toLB D) U := fun i j =>
  fn_ext fun h => by
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_locFn hf, fnOf_locFn hf, fnOf_toLB_g]
    have := Units.ne_zero j.1.2
    field_simp

omit [IsIntegral X] in

theorem zero_mem_secOn (L : LB X) : (0 : ∀ i, Γ(X, U ⊓ L.U i)) ∈ secOn L U := fun i j => by
  simp

open Classical in

def secOfRat (D : CartierDiv X) (U : X.Opens) (f : X.functionField) : ((toLB D).pull U.ι).Sec :=
  if hf : ∀ x ∈ U, D.RegularAt x f then KeyNear.pullOn U.ι (fun y => y.2) (locFn D U f) (locFn_mem hf)
  else KeyNear.pullOn U.ι (fun y => y.2) 0 (zero_mem_secOn _)

theorem secOfRat_eq (hf : ∀ x ∈ U, D.RegularAt x f) :
    secOfRat D U f = KeyNear.pullOn U.ι (fun y => y.2) (locFn D U f) (locFn_mem hf) := by
  rw [secOfRat, dif_pos hf]

theorem mem_nonzeroLocus_secOfRat (hf : ∀ x ∈ U, D.RegularAt x f) (y : U.toScheme)
    (hy : D.GeneratesAt (U.ι y) f) : y ∈ nonzeroLocus (secOfRat D U f) := by
  obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) (U.ι y)
  rw [secOfRat_eq hf]
  have hx : U.ι y ∈ U ⊓ (toLB D).U i := ⟨y.2, hi⟩
  refine KeyNear.mem_nonzeroLocus_pullOn (i := i) U.ι _ _ _ ?_
  rw [← unitAt_fnOf_iff hx (gen_mem hx), fnOf_locFn hf]
  exact (i.2.2 _ hi).generatesAt_iff.1 hy

end Sec

section Plk

open GlobalTheory.FlagBundle GlobalTheory.FlagEmb GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def what₂ {K : Type} {n : ℕ} (B : Matrix (Fin n) (Fin n) K) (i : Fin n) : Fin i → Fin (n - 1 + 1) → K :=
  fun l c => B (Fin.castLE i.2.le l) (Fin.cast (Nat.sub_add_cancel (Fin.pos i)) c)

abbrev plkM (x : Step Dw) : ℕ := plN (Dw.mult x.1 - 1) x.2.1

def plkFn {K : Type} [CommRing K] (B : Mat Dw.mult K) (x : Step Dw) : Fin (plkM x + 1) → K :=
  plk (what₂ (B x.1) x.2.1) id

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

def plkSec (C : FlagCpt Z e) (U : C.Y.X.Opens) (B : Mat Dw.mult C.Y.Fn) (x : Step Dw) (q : Fin (plkM x + 1)) :
    ((C.Y.lb (-detDiv C x.1 (x.2.1 : ℕ))).pull U.ι).Sec :=
  secOfRat _ U (plkFn B x q)

def baseFn (C : FlagCpt Z e) (V : (gen Z).Opens) (h : genericPoint C.Y.X ∈ C.π ⁻¹ᵁ V) : Γ(gen Z, V) →+* C.Y.Fn :=
  (fnOf _ h).comp (C.π.appLE V (C.π ⁻¹ᵁ V) le_rfl).hom

end Plk

end GlobalTheory.FlagAmple.PlkLoc
