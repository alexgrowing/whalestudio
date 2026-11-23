import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O}

namespace Link

variable (K : Link T c' h)

def twc (n : ℕ) : G T.L Ω →* (PadicAlgCl l)ˣ := W.pushCh (algebraMap c'.O (PadicAlgCl l)) (K.κ * K.β ^ n)

def rhoQ (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)) : G T.L Ω →* GL (Fin 4) (PadicAlgCl l) :=
  Af.tw (r.comp (resLe T.F_le)).toHomUnits (K.twc n)

theorem twc_val (n : ℕ) (g : G T.L Ω) :
    (K.twc n g : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (K.κ g * K.β g ^ n) := by
  rfl

theorem rho_val (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)) (g : G T.L Ω) :
    (K.rhoQ n r g : M4 (PadicAlgCl l)) = (K.twc n g : PadicAlgCl l) • r (resLe T.F_le g) := by
  simp only [rhoQ, Af.tw_val]
  rfl

variable {K} {X : Space (T.fr ∅) (inc h)} {B : W.UniversalOrdinaryDeterminantRing K.r}

private theorem map_adj_mul_mul_diag_eq_of_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M R : M4 A) (i : Fin 4) :
    f ((adj M * R * M) i i) = (adj (M.map f) * R.map f * M.map f) i i := by
  have ha : adj (M.map f) = (adj M).map f := by
    ext a b
    simp [adj_apply]
  rw [ha, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

theorem IsPhi.psi_val {n : ℕ} {φ : B.B →ₐ[c'.O] X.B} (hφ : K.IsPhi X n B φ) (y : X.A →ₐ[c'.O] PadicAlgCl l)
    (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)) (hg : resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v))) :
    ((pt φ y).psi v i g : PadicAlgCl l) =
      K.twc n g * (X.P.map (y : X.A →+* PadicAlgCl l)).ψ (K.e v) i (resLe T.F_le g) := by
  have e1 := hφ.2 v i g
  have e2 := X.ψ_map (K.e v) i (resLe T.F_le g) hg
  show y (algebraMap X.B X.A (φ ((B.u.ψ v i) g))) = _
  rw [e1, map_mul, e2, map_mul, Link.twc_val, ← IsScalarTower.algebraMap_apply c'.O X.B X.A, AlgHom.commutes]
  congr 1
  exact map_adj_mul_mul_diag_eq_of_map (y : X.A →+* PadicAlgCl l) _ _ i

end Link

theorem resLe_mem_Dec {F L : IntermediateField ℚ Ω} (hFL : F ≤ L) {A : ValuationSubring Ω} {g : G L Ω} :
    resLe hFL g ∈ Dec (F := F) A ↔ g ∈ Dec (F := L) A := Iff.rfl

theorem resLe_mem_Ine {F L : IntermediateField ℚ Ω} [NumberField F] [NumberField L] (hFL : F ≤ L) {A : ValuationSubring Ω} {g : G L Ω} :
    resLe hFL g ∈ Ine (F := F) A ↔ g ∈ Ine (F := L) A := Iff.rfl

theorem cycBar_resLe {F L : IntermediateField ℚ Ω} (hFL : F ≤ L) (g : G L Ω) :
    cycBar F Ω l (resLe hFL g) = cycBar L Ω l g := rfl

end UpperTheory.V.Ws

end
