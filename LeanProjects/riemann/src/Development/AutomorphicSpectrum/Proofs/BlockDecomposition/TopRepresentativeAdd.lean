import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

open GlobalTheory.CompanionTheory.CupRep

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) :
    Ideal.Quotient.mk T.J (liftV T h g) = ev T h g :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T h g))

theorem liftV_sub_map_mem {V : X.Opens} {T T' : Thick (smFun X q)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T')
    (g : Γ(X, V)) : liftV T' h' g - φ.φ (liftV T h g) ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [mk_liftV]
  have e : Ideal.Quotient.mk T'.J (φ.φ (liftV T h g)) =
      Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J (liftV T h g)) := (Ideal.quotientMap_mk).symm
  rw [e, mk_liftV]
  exact GlobalTheory.CompanionTheory.GrForm.ev_nat φ h h' g

theorem liftV_add_mem {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (x y : Γ(X, V)) :
    liftV T h x + liftV T h y - liftV T h (x + y) ∈ T.J := by
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_sub, map_add, mk_liftV, mk_liftV, mk_liftV, map_add, sub_self]

variable (s : ℕ) (V : X.Opens)

theorem addC_mem (g : Γ(X, V)) :
    addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V T.obj T.property) g) ∈
      FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
  refine mem_FC.2 fun u => ?_
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  rw [Nat.cast_one, hF.one]
  exact liftV_sub_map_mem (u.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom _ _ g

theorem cupList_mem {d : ℕ} (l : Fin d → CH.Cn (CH.modF (sP (KS q s {V})).A) 1)
    (hl : ∀ k, l k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1) :
    cupListC (sP (KS q s {V})).A l ∈ FC (sFil (KS q s {V}) ((d : ℕ) : ℤ)) d := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  induction d with
  | zero =>
    refine mem_FC.2 fun u => ?_
    rw [hF.top _ (by simp)]
    trivial
  | succ n ih =>
    exact cup_mem hF (by omega) (ih _ fun i => hl _) (hl (Fin.last n))

theorem xdtC_val {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) (u : ComposableArrows (KS q s {V}).FullSubcategory d) :
    vl (xdtC (q := q) s V t x) u =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) *
      vl (cupListC (sP (KS q s {V})).A fun k =>
        addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)) u :=
  congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last d)) =>
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) * b)
    (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))

end GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

namespace GlobalTheory.CompanionTheory.ConeLocal

open GlobalTheory.CompanionTheory.CupRep XdtAdd

theorem rep_xdtC_add {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (s : ℕ) (V : X.Opens)
    {d : ℕ} (t : Fin d → Γ(X, V)) (x y : Γ(X, V)) (a b : HQ (KS q s {V}) d ((d : ℤ) + 1) d)
    (ha : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t x) a)
    (hb : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t y) b) :
    Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t (x + y)) (a + b) := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  refine rep_congr (rep_add ha hb) fun u => ?_
  have hc := mem_FC.1 (cupList_mem s V (fun k => addC (KS q s {V}) fun T =>
    liftV T.obj (ks_in q s V T.obj T.property) (t k)) fun k => addC_mem s V (t k)) u
  let T0 := u.obj (CH.front (Nat.zero_add d) (Fin.last 0))
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0))))
  have h1 : ((sP (KS q s {V})).A.map ψ).hom
      (liftV T0.obj (ks_in q s V _ T0.property) x + liftV T0.obj (ks_in q s V _ T0.property) y -
        liftV T0.obj (ks_in q s V _ T0.property) (x + y)) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact (sP (KS q s {V})).J.map_mem ψ (liftV_add_mem T0.obj _ x y)
  have h2 := hF.mul 1 d _ h1 hc
  have e : ((1 + d : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
  rw [e] at h2
  change vl (xdtC (q := q) s V t x) u + vl (xdtC (q := q) s V t y) u - vl (xdtC (q := q) s V t (x + y)) u ∈ _
  rw [xdtC_val, xdtC_val, xdtC_val]
  convert h2 using 1
  rw [map_sub, map_add]
  ring

end GlobalTheory.CompanionTheory.ConeLocal
