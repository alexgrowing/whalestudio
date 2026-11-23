import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDerivationExt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinorGroupMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.CoefMemCmp

section Cup
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

def edge {m : ℕ} (k : Fin m) (i : Fin 2) : Fin (m + 1) := ⟨k + i, by omega⟩

theorem edge_mono {m : ℕ} (k : Fin m) : Monotone (edge k) := fun a b hab =>
  show (k : ℕ) + a ≤ k + b from Nat.add_le_add_left hab _

theorem cupList_val (A : C ⥤ CommAlgCat.{0} R) {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1) (u : ComposableArrows C m) :
    (show A.obj (u.obj (Fin.last m)) from cupListC A ℓ u) =
      ∏ k, (show A.obj (u.obj (Fin.last m)) from CH.term (CH.modF A) u (ℓ k) (edge k) (edge_mono k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    have hm : m + 1 = m + 1 := rfl
    change (show A.obj (u.obj (Fin.last (m + 1))) from CH.term (CH.modF A) u (cupListC A fun i => ℓ (Fin.castSucc i)) (CH.front hm) (CH.front_mono hm)) *
      (show A.obj (u.obj (Fin.last (m + 1))) from CH.term (CH.modF A) u (ℓ (Fin.last m)) (CH.back hm) (CH.back_mono hm)) = _
    congr 1
    · change (A.map (u.map (homOfLE (Fin.le_last (CH.front hm (Fin.last m)))))).hom
        (show A.obj (((CH.front_mono hm).functor ⋙ u).obj (Fin.last m)) from
          cupListC A (fun i => ℓ (Fin.castSucc i)) ((CH.front_mono hm).functor ⋙ u)) = _
      rw [ih (fun i => ℓ (Fin.castSucc i)) ((CH.front_mono hm).functor ⋙ u), map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      refine (Auxff.term_comp (CH.modF A) u (ℓ k.castSucc) (CH.front hm) (CH.front_mono hm) (edge k) (edge_mono k)).trans ?_
      exact CH.term_congr _ _ _ _ _ (funext fun i => Fin.ext rfl)

end Cup

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem map_self {T : C} (f : T ⟶ T) (hf : f = 𝟙 T) (y : Φ.A.obj T) : (Φ.A.map f).hom y = y := by
  subst hf
  simp

theorem form_one (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) (x : Φ.A.obj E.D) (v : ComposableArrows C 1) :
    E.form σ ![i] x v = E.a σ i (v.map (homOfLE (Fin.zero_le (Fin.last 1)))) * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form
  rw [Fin.prod_univ_one]
  congr 1
  have e : v.map (homOfLE (Fin.le_last (Fin.succ (0 : Fin 1)))) = 𝟙 (v.obj (Fin.last 1)) :=
    (congrArg v.map (Subsingleton.elim _ (𝟙 (Fin.last 1)))).trans (v.map_id _)
  exact (map_self _ e _).trans rfl

theorem form_sub (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j : ℕ} (I : Fin j → Fin d) (x y : Φ.A.obj E.D)
    (s : ComposableArrows C j) : E.form σ I (x - y) s = E.form σ I x s - E.form σ I y s := by
  unfold Frame.form
  rw [map_sub, mul_sub]

theorem taylor_form {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (hc : E.GrConst Fil)
    (P : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (hT : Taylor Fil E P) (σ : ∀ T : C, E.D ⟶ T) (x : Φ.A.obj E.D)
    (u : ComposableArrows C 1) :
    (Φ.A.map (σ _)).hom x - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom ((Φ.A.map (σ (u.obj 0))).hom x) -
      ∑ i, E.form σ ![i] (P i x) u ∈ (Fil 2).S (u.obj (Fin.last 1)) := by
  set φ := u.map (homOfLE (Fin.zero_le (Fin.last 1))) with hφ
  have h1 := hT _ (σ (u.obj (Fin.last 1))) (σ (u.obj 0) ≫ φ) x
  have e0 : ∀ y, (Φ.A.map (σ (u.obj 0) ≫ φ)).hom y = (Φ.A.map φ).hom ((Φ.A.map (σ (u.obj 0))).hom y) := fun y => by simp
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin d)), E.τ i (σ (u.obj 0) ≫ φ) (σ (u.obj (Fin.last 1))) *
      ((Φ.A.map (σ (u.obj 0) ≫ φ)).hom (P i x) - (Φ.A.map (σ (u.obj (Fin.last 1)))).hom (P i x)) ∈ (Fil 2).S (u.obj (Fin.last 1)) := by
    intro i _
    have a1 : E.τ i (σ (u.obj 0) ≫ φ) (σ (u.obj (Fin.last 1))) ∈ (Fil ((1 : ℕ) : ℤ)).S (u.obj (Fin.last 1)) := by
      have := E.mem i (σ (u.obj 0) ≫ φ) (σ (u.obj (Fin.last 1)))
      rw [← hF.one] at this
      simpa using this
    have a2 := hc 0 (σ (u.obj 0) ≫ φ) (σ (u.obj (Fin.last 1))) (x := P i x) (by
      rw [hF.top _ (by simp)]; trivial)
    have a3 := hF.mul 1 1 _ a1 (by simpa using a2)
    simpa using a3
  have h3 := Ideal.add_mem _ h1 (Ideal.sum_mem _ h2)
  convert h3 using 1
  rw [← e0]
  simp only [form_one, mul_sub, Finset.sum_sub_distrib]
  unfold Frame.a
  ring

end Frame

section Sign

theorem sum_sgn {B : Type} [CommRing B] {m d : ℕ} (I : Idx m d) (a : Fin d → Fin m → B) :
    ∑ J : Fin m → Fin d, sgn I J • ∏ l, a (J l) l = (Matrix.of fun k l => a (I.1 k) l).det := by
  classical
  rw [Matrix.det_apply]
  unfold sgn
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (I.1 ∘ π)]
  · simp only [if_true, Matrix.of_apply, Function.comp_apply]
    rw [Units.smul_def]
  · intro J _ hJ
    rw [if_neg hJ, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Sign

section Res
variable {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {e : ℕ}
  (E : Frame (sP Q) e) (σ : ∀ T, E.D ⟶ T)

def lc (i : Fin e) : CH.Cn (CH.modF (sP Q').A) 1 := fun v => E.form σ ![i] 1 (v ⋙ ObjectProperty.ιOfLE h)

theorem lc_val (i : Fin e) (v : ComposableArrows Q'.FullSubcategory 1) :
    (show (sP Q').A.obj (v.obj (Fin.last 1)) from lc h E σ i v) =
      E.a σ i ((v ⋙ ObjectProperty.ιOfLE h).map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
  change E.form σ ![i] 1 (v ⋙ ObjectProperty.ιOfLE h) = _
  rw [form_one, map_one, mul_one]

theorem cup_lc {m : ℕ} (I : Fin m → Fin e) (u : ComposableArrows Q'.FullSubcategory m) :
    (show (sP Q').A.obj (u.obj (Fin.last m)) from cupListC (sP Q').A (fun k => lc h E σ (I k)) u) =
      ∏ k : Fin m, ((sP Q).A.map ((u ⋙ ObjectProperty.ιOfLE h).map (homOfLE (Fin.le_last k.succ)))).hom
        (E.a σ (I k) ((u ⋙ ObjectProperty.ιOfLE h).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) := by
  rw [cupList_val]
  refine Finset.prod_congr rfl fun k _ => ?_
  change ((sP Q').A.map (u.map (homOfLE (Fin.le_last (edge k (Fin.last 1)))))).hom
    (show (sP Q').A.obj (((edge_mono k).functor ⋙ u).obj (Fin.last 1)) from lc h E σ (I k) ((edge_mono k).functor ⋙ u)) = _
  rw [lc_val]
  rfl

theorem form_cup {m : ℕ} (I : Fin m → Fin e) (x : (sP Q).A.obj E.D) (u : ComposableArrows Q'.FullSubcategory m) :
    E.form σ I x (u ⋙ ObjectProperty.ιOfLE h) =
      (show (sP Q').A.obj (u.obj (Fin.last m)) from cupListC (sP Q').A (fun k => lc h E σ (I k)) u) *
        (show (sP Q').A.obj (u.obj (Fin.last m)) from ((sP Q).A.map (σ ((ObjectProperty.ιOfLE h).obj (u.obj (Fin.last m))))).hom x) := by
  rw [cup_lc]
  rfl

end Res

section Main
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) {W U : X.Opens}
  (hWU : W ≤ U) {d e : ℕ}

theorem lift_diff {tW : Fin d → Γ(X, W)} {tU : Fin e → Γ(X, U)} {EW : Frame (sP (KS q s {W})) d}
    {εW : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj EW.D} (hW : IsLoc q s tW EW εW)
    {EU : Frame (sP (KS q s {U})) e} {εU : Γ(X, U) ≃+* (sP (KS q s {U})).A.obj EU.D} (hU : IsLoc q s tU EU εU)
    (σW : ∀ T, EW.D ⟶ T) (σU : ∀ T, EU.D ⟶ T) (g : Γ(X, U)) (T : (KS q s {W}).FullSubcategory) :
    (show (sP (KS q s {W})).A.obj T from
      ((sP (KS q s {U})).A.map (σU ((ObjectProperty.ιOfLE (ks_le q s hWU)).obj T))).hom (εU g)) -
      ((sP (KS q s {W})).A.map (σW T)).hom (εW (rs hWU g)) ∈ (sP (KS q s {W})).J.S T := by
  have h1 := hU.2.2.2.1 ((ObjectProperty.ιOfLE (ks_le q s hWU)).obj T) (σU _) g
  have h2 := hW.2.2.2.1 T (σW T) (rs hWU g)
  have h3 := GlobalTheory.CompanionTheory.GrForm.ev_res hWU T.obj (ks_in q s U _ (ks_le q s hWU _ T.property)) (ks_in q s W _ T.property) g
  exact Ideal.Quotient.eq.1 (h1.symm.trans (h3.symm.trans h2))

theorem rep_one {tW : Fin d → Γ(X, W)} {tU : Fin e → Γ(X, U)} {EW : Frame (sP (KS q s {W})) d}
    {εW : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj EW.D} (hW : IsLoc q s tW EW εW)
    {EU : Frame (sP (KS q s {U})) e} {εU : Γ(X, U) ≃+* (sP (KS q s {U})).A.obj EU.D} (hU : IsLoc q s tU EU εU)
    (p : Fin d → Γ(X, W) → Γ(X, W)) (hT : Taylor (sFil (KS q s {W})) EW (fun k x => εW (p k (εW.symm x))))
    (σW : ∀ T, EW.D ⟶ T) (σU : ∀ T, EU.D ⟶ T) (m : ℕ) (r : ℤ) (hr : r = m) (L : Fin m → Fin e) (z : Γ(X, U))
    (c : HQ (KS q s {W}) r (r + 1) m)
    (hc : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => EU.form σU L (εU z) (u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU))) c) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ J : Fin m → Fin d, EW.form σW J (εW (rs hWU z) * ∏ k, εW (p (J k) (rs hWU (tU (L k))))) u) c := by
  have hF : IsFil (sP (KS q s {W})) (sFil (KS q s {W})) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil _
  refine GlobalTheory.CompanionTheory.CupRep.cup_rep hF EW σW hW.1 m (fun k => lc (ks_le q s hWU) EU σU (L k))
    (fun k i => εW (p i (rs hWU (tU (L k)))))
    (fun k T => (show (sP (KS q s {W})).A.obj T from
      ((sP (KS q s {U})).A.map (σU ((ObjectProperty.ιOfLE (ks_le q s hWU)).obj T))).hom (εU (tU (L k)))) -
      ((sP (KS q s {W})).A.map (σW T)).hom (εW (rs hWU (tU (L k))))) ?_ ?_ (εW (rs hWU z)) r hr c ?_
  · exact fun k T => lift_diff q s hWU hW hU σW σU _ T
  · intro k u
    have t := taylor_form hF EW hW.1 _ hT σW (εW (rs hWU (tU (L k)))) u
    simp only [RingEquiv.symm_apply_apply] at t
    have e1 : (show (sP (KS q s {W})).A.obj (u.obj (Fin.last 1)) from lc (ks_le q s hWU) EU σU (L k) u) =
        (show (sP (KS q s {W})).A.obj (u.obj (Fin.last 1)) from ((sP (KS q s {U})).A.map (σU ((ObjectProperty.ιOfLE (ks_le q s hWU)).obj (u.obj (Fin.last 1))))).hom (εU (tU (L k)))) -
        ((sP (KS q s {W})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
          (show (sP (KS q s {W})).A.obj (u.obj 0) from ((sP (KS q s {U})).A.map (σU ((ObjectProperty.ιOfLE (ks_le q s hWU)).obj (u.obj 0)))).hom (εU (tU (L k)))) := by
      rw [lc_val]
      unfold Frame.a
      rw [hU.2.2.2.2]
      exact congrArg₂ (· - ·) rfl (GlobalTheory.CompanionTheory.CocProd.map_map _ _ _).symm
    convert t using 1
    rw [e1]
    simp only [map_sub]
    ring
  · refine rep_congr hc fun u => ?_
    subst hr
    rw [form_cup]
    have hf : ∀ k : Fin m, ((sP (KS q s {U})).A.map ((u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU)).map (homOfLE (Fin.le_last k.succ)))).hom
        (EU.a σU (L k) ((u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU)).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) ∈
        (sFil (KS q s {W}) ((1 : ℕ) : ℤ)).S (u.obj (Fin.last m)) := fun k => by
      rw [Nat.cast_one, hF.one]
      have a : EU.a σU (L k) ((u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU)).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)) ∈
          (sP (KS q s {U})).J.S _ := EU.mem _ _ _
      exact (sP (KS q s {U})).J.map_mem ((u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU)).map (homOfLE (Fin.le_last k.succ))) a
    have hx := lift_diff q s hWU hW hU σW σU z (u.obj (Fin.last m))
    rw [← hF.one] at hx
    have h1 := GlobalTheory.CompanionTheory.CocProd.prod_mem hF _ hf (q := 1) (by simpa using hx)
    rw [← cup_lc] at h1
    rw [← mul_sub]
    simpa using h1

end Main

section Sum
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem rep_sum {a b : IdF A} {j : ℕ} {ι : Type} [Fintype ι]
    {z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : ι → CH.H (sq a b) j}
    (h : ∀ i, CrystallineSemistableComparison.Pb.Rep a b (z i) (c i)) : CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i, z i s) (∑ i, c i) := by
  classical
  have key : ∀ S : Finset ι, CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i ∈ S, z i s) (∑ i ∈ S, c i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact rep_zero fun s => Ideal.zero_mem _
    | insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact rep_add (h i) ih
  exact key Finset.univ

end Sum

theorem cmp_coef : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) {W U : X.Opens} (hWU : W ≤ U) {d e : ℕ}
    (tW : Fin d → Γ(X, W)) (tU : Fin e → Γ(X, U)) (EW : Frame (sP (KS q s {W})) d) (εW : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj EW.D),
    IsLoc q s tW EW εW → ∀ (EU : Frame (sP (KS q s {U})) e) (εU : Γ(X, U) ≃+* (sP (KS q s {U})).A.obj EU.D), IsLoc q s tU EU εU →
    ∀ (p : Fin d → Γ(X, W) → Γ(X, W)), Taylor (sFil (KS q s {W})) EW (fun k x => εW (p k (εW.symm x))) →
    ∀ (σW : ∀ T, EW.D ⟶ T) (σU : ∀ T, EU.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    ∀ (ξ : HQ (KS q s {W}) r (r + 1) m) (y : Idx m d → Γ(X, W)) (z : Idx m e → Γ(X, U)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, EW.form σW I.1 (εW (y I)) u) ξ →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
        (fun u => ∑ L : Idx m e, EU.form σU L.1 (εU (z L)) (u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU))) ξ →
      ∀ I, y I = ∑ L : Idx m e, rs hWU (z L) * (Matrix.of fun k l => p (I.1 k) (rs hWU (tU (L.1 l)))).det := by
  intro K _ _ X q s W U hWU d e tW tU EW εW hW EU εU hU p hT σW σU m r hr hm ξ y z hy hz I
  have hF : IsFil (sP (KS q s {W})) (sFil (KS q s {W})) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil _
  have hF' : IsFil (sP (KS q s {U})) (sFil (KS q s {U})) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil _
  have hL : ∀ L : Idx m e, ∃ c, CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => EU.form σU L.1 (εU (z L)) (u ⋙ ObjectProperty.ιOfLE (ks_le q s hWU))) c := by
    intro L
    obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF' EU σU hU.1 m 0 r (by simpa using hr) L.1 (εU (z L))
      (by rw [hF'.top _ (by simp)]; trivial)
    exact ⟨_, rep_res (ks_le q s hWU) r (r + 1) hc⟩
  choose c hc using hL
  have e1 : ∑ L, c L = ξ := rep_unique (rep_sum hc) hz
  have h1 : ∀ L : Idx m e, CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ J : Fin m → Fin d, EW.form σW J (εW (rs hWU (z L)) * ∏ k, εW (p (J k) (rs hWU (tU (L.1 k))))) u) (c L) :=
    fun L => rep_one q s hWU hW hU p hT σW σU m r hr L.1 (z L) (c L) (hc L)
  have h2 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ L : Idx m e, ∑ J : Fin m → Fin d, EW.form σW J (εW (rs hWU (z L)) * ∏ k, εW (p (J k) (rs hWU (tU (L.1 k))))) u) ξ :=
    e1 ▸ rep_sum h1
  have h3 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ i : Idx m e × (Fin m → Fin d), EW.form σW i.2
        (εW (rs hWU (z i.1)) * ∏ k, εW (p (i.2 k) (rs hWU (tU (i.1.1 k))))) u) ξ := by
    refine rep_congr h2 fun u => ?_
    rw [Fintype.sum_prod_type, sub_self]
    exact Ideal.zero_mem _
  have h4 := GlobalTheory.CompanionTheory.ConeLocal.rep_collapse hF EW σW hW.1 m r hr (fun i : Idx m e × (Fin m → Fin d) => i.2)
    (fun i => εW (rs hWU (z i.1)) * ∏ k, εW (p (i.2 k) (rs hWU (tU (i.1.1 k))))) ξ h3
  let y' : Idx m d → Γ(X, W) := fun I =>
    ∑ L : Idx m e, rs hWU (z L) * (Matrix.of fun k l => p (I.1 k) (rs hWU (tU (L.1 l)))).det
  have e2 : ∀ I : Idx m d, ∑ i : Idx m e × (Fin m → Fin d),
      sgn I i.2 • (εW (rs hWU (z i.1)) * ∏ k, εW (p (i.2 k) (rs hWU (tU (i.1.1 k))))) = εW (y' I) := by
    intro I
    rw [Fintype.sum_prod_type]
    simp only [y', map_sum, map_mul]
    refine Finset.sum_congr rfl fun L _ => ?_
    have e3 : ∀ J : Fin m → Fin d, sgn I J • (εW (rs hWU (z L)) * ∏ k, εW (p (J k) (rs hWU (tU (L.1 k))))) =
        εW (rs hWU (z L)) * sgn I J • ∏ k, εW (p (J k) (rs hWU (tU (L.1 k)))) := fun J => by
      rw [zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun J _ => e3 J, ← Finset.mul_sum]
    congr 1
    rw [sum_sgn I (fun i l => εW (p i (rs hWU (tU (L.1 l)))))]
    exact (RingHom.map_det εW.toRingHom (Matrix.of fun k l => p (I.1 k) (rs hWU (tU (L.1 l))))).symm
  have h5 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ I : Idx m d, EW.form σW I.1 (εW (y' I)) u) ξ := by
    refine rep_congr h4 fun u => ?_
    simp only [e2, sub_self]
    exact Ideal.zero_mem _
  have h6 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1))
      (fun u => ∑ I : Idx m d, EW.form σW I.1 (εW (y I - y' I)) u) 0 := by
    have h := rep_add hy (rep_smul (-1 : K) h5)
    rw [neg_one_smul, add_neg_cancel] at h
    refine rep_congr h fun u => ?_
    simp only [map_sub, form_sub, Finset.sum_sub_distrib, neg_one_smul]
    convert Ideal.zero_mem _ using 1
    ring
  have h7 := (GlobalTheory.CompanionTheory.ConeLocal.loc_coef q tW s EW εW hW σW m r hr hm).2 _ h6
  exact sub_eq_zero.1 (congrFun h7 I)

end GlobalTheory.CompanionTheory.ConeLocal.CoefMemCmp

namespace GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc

theorem resKS_resKS {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)
    {W V U V' : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ V') (h₃ : W ≤ U) (h₄ : U ≤ V') (r r' : ℤ) (j : ℕ)
    (x : HQ (KS q s {V'}) r r' j) :
    resKS q s h₁ r r' j (resKS q s h₂ r r' j x) = resKS q s h₃ r r' j (resKS q s h₄ r r' j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

theorem rs_rs {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (x : Γ(X, U)) :
    rs h₂ (rs h₁ x) = rs h₃ x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem det_delta {R : Type} [CommRing R] {m d : ℕ} (I L : Idx m d) :
    (Matrix.of fun k l => if I.1 k = L.1 l then (1 : R) else 0).det = if I = L then 1 else 0 := by
  by_cases h : I = L
  · subst h
    rw [if_pos rfl]
    have e : (Matrix.of fun k l => if I.1 k = I.1 l then (1 : R) else 0) = 1 := by
      ext k l
      simp [Matrix.one_apply, I.2.injective.eq_iff]
    rw [e, Matrix.det_one]
  · rw [if_neg h]
    have hk : ∃ k, ∀ l, I.1 k ≠ L.1 l := by
      by_contra hc
      push_neg at hc
      apply h
      have hsub : Finset.univ.image I.1 ⊆ Finset.univ.image L.1 := by
        intro x hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨l, hl⟩ := hc k
        exact Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl.symm⟩
      have hcard : (Finset.univ.image L.1).card ≤ (Finset.univ.image I.1).card := by
        rw [Finset.card_image_of_injective _ I.2.injective, Finset.card_image_of_injective _ L.2.injective]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hr : Set.range I.1 = Set.range L.1 := by
        have := congrArg (fun S : Finset (Fin d) => (S : Set (Fin d))) heq
        simpa using this
      exact Subtype.ext ((StrictMono.range_inj I.2 L.2).1 hr)
    obtain ⟨k, hk⟩ := hk
    exact Matrix.det_eq_zero_of_row_eq_zero k fun l => by simp [hk l]

theorem sum_delta {R : Type} [CommRing R] {m d : ℕ} (y : Idx m d → R) (I : Idx m d) :
    ∑ L : Idx m d, y L * (Matrix.of fun k l => if I.1 k = L.1 l then (1 : R) else 0).det = y I := by
  simp only [det_delta]
  simp

theorem basicOpen_rs_le {X : Scheme.{0}} {V V' : X.Opens} (hVV : V ≤ V') (f : Γ(X, V')) :
    X.basicOpen (rs hVV f) ≤ X.basicOpen f := by
  have := Scheme.basicOpen_res X f (homOfLE hVV).op
  simp only [rs]
  change X.basicOpen ((X.presheaf.map (homOfLE hVV).op) f) ≤ _
  rw [this]
  exact inf_le_right

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (f : Γ(X, V')) (e : ℕ) (cu : Coord q (X.basicOpen f) e) (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, ∃ M : ℕ, rs hVV (f ^ M) * y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  intro K _ _ X q _ s V V' hVV hV' d c
  letI := (strV q V).toAlgebra
  intro D hD E ε hloc σ m r hr hs f e cu ξ y hy I
  have hWV : X.basicOpen (rs hVV f) ≤ V := X.basicOpen_le _
  have hUf : X.basicOpen f ≤ V' := X.basicOpen_le f
  have hWU : X.basicOpen (rs hVV f) ≤ X.basicOpen f := basicOpen_rs_le hVV f
  have hW : IsAffineOpen (X.basicOpen (rs hVV f)) := c.affine.basicOpen _
  obtain ⟨cW, hcW⟩ := GlobalTheory.CompanionTheory.CoordRes.main c hWV hW
  letI := (strV q (X.basicOpen (rs hVV f))).toAlgebra
  obtain ⟨p, hp⟩ := GlobalTheory.CompanionTheory.ConeLocal.DerivExt.main q c.affine (rs hVV f) D
  have hs1 : 1 ≤ s := by omega
  obtain ⟨EW, εW, lW⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q cW s hs1
  obtain ⟨EU, εU, lU⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q cu s hs1
  have hpδ : ∀ k j, p k (rs hWV (c.t j)) = if k = j then 1 else 0 := by
    intro k j
    rw [hp, hD]
    split_ifs <;> simp
  have hδ : ∀ k j, p k (cW.t j) = if k = j then 1 else 0 := by
    intro k j
    rw [hcW, hpδ]
  have hT := GlobalTheory.CompanionTheory.ConeLocal.taylor_loc q cW s EW εW lW p hδ
  let σW : ∀ T, EW.D ⟶ T := fun T => (EW.ne T).some
  let σU : ∀ T, EU.D ⟶ T := fun T => (EU.ne T).some
  obtain ⟨z, hz⟩ := (GlobalTheory.CompanionTheory.ConeLocal.loc_coef q cu.t s EU εU lU σU m r hr hs).1 (resKS q s hUf _ _ _ ξ)
  obtain ⟨yW, hyW⟩ := (GlobalTheory.CompanionTheory.ConeLocal.loc_coef q cW.t s EW εW lW σW m r hr hs).1
    (resKS q s hWV _ _ _ (resKS q s hVV _ _ _ ξ))
  have h1 := rep_res (ks_le q s hWV) r (r + 1) hy
  have h2 := rep_res (ks_le q s hWU) r (r + 1) hz
  have e1 := GlobalTheory.CompanionTheory.ConeLocal.CoefMemCmp.cmp_coef q s hWV cW.t c.t EW εW lW E ε hloc (fun k => p k) hT σW σ m r hr hs _ yW y hyW h1 I
  have hyW' := hyW
  rw [resKS_resKS q s hWV hVV hWU hUf] at hyW'
  have e2 := GlobalTheory.CompanionTheory.ConeLocal.CoefMemCmp.cmp_coef q s hWU cW.t cu.t EW εW lW EU εU lU (fun k => p k) hT σW σU m r hr hs _ yW z hyW' h2 I
  have e3 : yW I = rs hWV (y I) := by
    rw [e1]
    simp only [hpδ]
    exact sum_delta (fun L => rs hWV (y L)) I
  have hcomp : (rs hWU).comp (rs hUf) = (rs hWV).comp (rs hVV) := by
    ext x
    simp only [RingHom.comp_apply]
    rw [rs_rs hUf hWU (hWV.trans hVV), rs_rs hVV hWV (hWV.trans hVV)]
  have hsurj : ∀ a : Γ(X, X.basicOpen f), ∃ (b : Γ(X, V')) (N : ℕ), rs hUf f ^ N * a = rs hUf b := by
    intro a
    obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X V' hV' f a
    exact ⟨b, n, hb.symm⟩
  have hinj : ∀ x : Γ(X, V), rs hWV x = 0 → ∃ N : ℕ, rs hVV f ^ N * x = 0 := by
    intro x hx
    exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X c.affine x (rs hVV f) hx
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ConeLocal.JacAlg.clear_sum (rs hVV) (rs hWV) (rs hUf) (rs hWU) f hcomp hsurj hinj (fun k => D k) (fun k => p k)
    (fun k x y => map_add _ _ _) (fun k x y => by simpa using (p k).leibniz x y) (fun k x => hp k x) I.1 z
    (fun L l => cu.t (L.1 l)) (y I) (by rw [← e3]; exact e2)
  refine ⟨M, ?_⟩
  rw [map_pow]
  exact hM

end GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc
