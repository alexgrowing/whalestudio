import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) : R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr x k

theorem crd_tmul (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) (k : Fin (Module.finrank F E)) :
    crd R (r ⊗ₜ[F] e) k = r * algebraMap F R ((Module.finBasis F E).repr e k) := by
  unfold crd
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem crd_add (R : Type) [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (x + y) k = crd R x k + crd R y k := by
  simp [crd]

theorem crd_neg (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R (-x) k = -crd R x k := by
  simp [crd]

theorem crd_zero (R : Type) [CommRing R] [Algebra F R] (k : Fin (Module.finrank F E)) :
    crd R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

theorem crd_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    crd R' (Algebra.TensorProduct.map f (AlgHom.id F E) x) k = f (crd R x k) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, crd_zero, crd_zero, map_zero]
  | tmul r e =>
    rw [Algebra.TensorProduct.map_tmul, crd_tmul, crd_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add, crd_add, crd_add, hx, hy, map_add]

theorem crd_ext (R : Type) [CommRing R] [Algebra F R] {x y : R ⊗[F] E}
    (h : ∀ k, crd R x k = crd R y k) : x = y :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr.injective (Finsupp.ext h)

theorem sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    ∑ k, crd R y k ⊗ₜ[F] (Module.finBasis F E) k = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis R (Module.finBasis F E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

end Coord

variable {D : D7}

theorem cv_eq (v : Pl D) (x : AE D) :
    cv D v x = Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) x := rfl

theorem infPart_eq (x : AE D) :
    infPart D x = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x := rfl

theorem ext_comp {D : D7} {x y : AE D} (hf : ∀ v, cv D v x = cv D v y) (hi : infPart D x = infPart D y) : x = y := by
  refine crd_ext (AF D.host.F) fun k => ?_
  have hf' : ∀ v : Pl D, evFin D.host.F v (crd (AF D.host.F) x k) = evFin D.host.F v (crd (AF D.host.F) y k) := by
    intro v
    have := congrArg (fun z => crd (Fv D.host.F v) z k) (hf v)
    simpa only [cv_eq, crd_map] using this
  have hi' : fstA D.host.F (crd (AF D.host.F) x k) = fstA D.host.F (crd (AF D.host.F) y k) := by
    have := congrArg (fun z => crd (Ainf D.host.F) z k) hi
    simpa only [infPart_eq, crd_map] using this
  exact Prod.ext hi' (Subtype.ext (funext hf'))

theorem cv_cA {D : D7} (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem infPart_cA {D : D7} (x : AE D) : infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crd_int_ev (k : Fin (Module.finrank D.host.F D.host.E)) :
    ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc D.host.F D.host.E (v : Pl D),
      crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ v in Filter.cofinite, ∀ j,
      algebraMap D.host.F (Fv D.host.F v) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k) ∈
        (v : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro j
    exact (algebraMap D.host.F (Af D.host.F) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) k)).2
  filter_upwards [hev] with v hv
  intro y hy
  refine intLoc_induction (p := fun y => crd (Fv D.host.F v) y k ∈ (v : Pl D).adicCompletionIntegers D.host.F)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    rw [crd_tmul]
    refine mul_mem ha ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl
    rw [ho, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hv j) _
  · rw [crd_zero]; exact zero_mem _
  · intro y z hy hz; rw [crd_add]; exact add_mem hy hz
  · intro y hy; rw [crd_neg]; exact neg_mem hy

theorem glue_one (D : D7) (f : ∀ v : Pl D, Fv D.host.F v ⊗[D.host.F] D.host.E)
    (hf : ∀ v, f v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ v, cv D v x = f v) ∧ infPart D x = 0 := by
  classical
  let c : Fin (Module.finrank D.host.F D.host.E) → (v : Pl D) → Fv D.host.F v := fun k v => crd (Fv D.host.F v) (f v) k
  have hc : ∀ k, ∀ᶠ v in Filter.cofinite, c k v ∈ (v : Pl D).adicCompletionIntegers D.host.F := by
    intro k
    filter_upwards [crd_int_ev (D := D) k] with v hv
    exact hv _ (hf v)
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun k => RestrictedProduct.mk (c k) (hc k)
  refine ⟨∑ k, pairA D.host.F 0 (C k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E) k, fun v => ?_, ?_⟩
  · rw [map_sum]
    conv_rhs => rw [← sum_crd (Fv D.host.F v) (f v)]
    rfl
  · rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]

theorem glue_mat (D : D7) {m p : ℕ} (b : ∀ v : Pl D, Matrix (Fin m) (Fin p) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v) :
    ∃ x : Mx D m p, (∀ v i j, cv D v (x i j) = b v i j) ∧ ∀ i j, infPart D (x i j) = 0 := by
  choose g hg using fun i j => glue_one D (fun v => b v i j) (fun v => hb v i j)
  exact ⟨Matrix.of fun i j => g i j, fun v i j => (hg i j).1 v, fun i j => (hg i j).2⟩

theorem isUnit_of_comp (D : D7) (y : AE D) (hf : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v y * z = 1)
    (hi : infPart D y = 1) : IsUnit y := by
  choose z hz hzy using hf
  obtain ⟨s, hs, hs0⟩ := glue_one D z hz
  set e : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E) with he
  have hev : ∀ v, cv D v e = 0 := by
    intro v
    show (evFin D.host.F v (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    have : evFin D.host.F v (pairA D.host.F 1 0) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
  have hei : infPart D e = 1 := rfl
  have h1 : y * (s + e) = 1 := by
    refine ext_comp (fun v => ?_) ?_
    · rw [map_mul, map_add, hs, hev, add_zero, hzy, map_one]
    · rw [map_mul, map_add, hs0, hei, zero_add, hi, mul_one, map_one]
  exact ⟨⟨y, s + e, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end PositivityTheory.Rg.Rsw.L.LGenK
