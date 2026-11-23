import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLdlog

open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def ee {d : ℕ} (E : Frame Φ d) (k i : Fin d) : Φ.A.obj E.D := if i = k then 1 else 0

theorem cupList_mem (hF : IsFil Φ Fil) : ∀ (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m := by
  intro m
  induction m with
  | zero =>
    intro ℓ _
    refine mem_FC.2 fun s => ?_
    rw [Nat.cast_zero, hF.top 0 le_rfl]
    trivial
  | succ m ih =>
    intro ℓ hl
    exact cup_mem hF rfl (ih _ fun k => hl _) (hl (Fin.last m))

theorem form_id_eq {n : ℕ} (E : Frame Φ n) (σ : ∀ T : C, E.D ⟶ T) (w : Φ.A.obj E.D)
    (u : ComposableArrows C n) :
    E.form σ id w u = vl (∑ I : Fin n → Fin n, fc E σ I (∏ k, ee E k (I k))) u * (Φ.A.map (σ _)).hom w := by
  rw [vl, Finset.sum_apply]
  change _ = (∑ I : Fin n → Fin n, vl (fc E σ I (∏ k, ee E k (I k))) u) * _
  rw [Finset.sum_mul]
  simp only [← form_mul]
  rw [Finset.sum_eq_single id]
  · have e : ∏ k, ee E k (id k) = 1 := Finset.prod_eq_one fun k _ => by simp [ee]
    rw [e, mul_one]
  · intro I _ hI
    obtain ⟨k, hk⟩ : ∃ k, I k ≠ k := by
      by_contra hc
      push_neg at hc
      exact hI (funext hc)
    have e : ∏ k, ee E k (I k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (by simp [ee, hk])
    rw [e, mul_zero]
    simp [Frame.form]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rep_back (hF : IsFil Φ Fil) {n : ℕ} (E : Frame Φ (n + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (ℓ : Fin (n + 1) → CH.Cn (CH.modF Φ.A) 1) (h : Fin (n + 1) → ∀ T : C, Φ.A.obj T)
    (hJ : ∀ k T, h k T ∈ Φ.J.S T)
    (hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows C 1), (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) -
        (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) ∈ (Fil 2).S _)
    (w : Φ.A.obj E.D) (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (x : CH.H (gr Fil r) (n + 1))
    (z : ∀ u : ComposableArrows C (n + 1), Φ.A.obj (u.obj (Fin.last (n + 1))))
    (hz : ∀ u, z u - vl (cupListC Φ.A ℓ) u * (Φ.A.map (σ _)).hom w ∈ (Fil (r + 1)).S _)
    (hx : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id w) x) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) z x := by
  subst hr
  have hh : ∀ k, h0 (h k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun s => by
    have := hJ k (s.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k))) ∈
      FC (Fil ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k)))) u =
        (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (ee E k i) u +
          (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (ee E k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    exact hl k u
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ (ee E) (fun k => h0 (h k)) hh he
  obtain ⟨H, hH, rfl⟩ := hg
  let H' : CH.Cn (CH.modF Φ.A) n := fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w
  have hH' : H' ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add hx (rep_d (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc w hH u
  have e3 := hz u
  have e4 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e4] at e1 e2
  have e5 := ((Fil _).S _).neg_mem (((Fil _).S _).add_mem (((Fil _).S _).add_mem
    (Ideal.mul_mem_right ((Φ.A.map (σ _)).hom w) _ e1) e2) e3)
  convert e5 using 1
  rw [form_id_eq]
  change _ + vl (CH.d (CH.modF Φ.A) n H') u - z u = -((vl (cupListC Φ.A ℓ) u -
    vl (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, ee E k (I k))) u - vl (CH.d (CH.modF Φ.A) n H) u) * _ +
    (vl (CH.d (CH.modF Φ.A) n H) u * _ - vl (CH.d (CH.modF Φ.A) n H') u) + (z u - _))
  ring

end Fr

section Term
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem term_id {n : ℕ} (f : CH.Cn (CH.modF A) n) (s : ComposableArrows C n) (g : Fin (n + 1) → Fin (n + 1))
    (hg : Monotone g) (e : g = id) : CH.term (CH.modF A) s f g hg = f s := by
  subst e
  have e : ∀ (h : Fin.last n ⟶ Fin.last n) (z : A.obj (s.obj (Fin.last n))), (A.map (s.map h)).hom z = z := by
    intro h z
    have e1 : h = 𝟙 _ := Subsingleton.elim _ _
    have e2 : s.map h = 𝟙 _ := (congrArg s.map e1).trans (s.map_id _)
    have e3 : A.map (s.map h) = 𝟙 _ := (congrArg A.map e2).trans (A.map_id _)
    rw [e3]
    rfl
  exact e _ _

end Term

section Loc
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem lift_sub_mem (s : ℕ) {V : X.Opens} {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (y : Γ(X, V))
    (T : (KS q s {V}).FullSubcategory) :
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) y) -
      ((sP (KS q s {V})).A.map (σ T)).hom (ε y) ∈ (sP (KS q s {V})).J.S T := by
  obtain ⟨-, -, -, h4, -⟩ := hL
  exact Ideal.Quotient.eq.1 ((Classical.choose_spec (Ideal.Quotient.mk_surjective
    (ev T.obj (ks_in q s V T.obj T.property) y))).trans (h4 T (σ T) y))

theorem xdt_rep (s : ℕ) {V : X.Opens} {n : ℕ} (t : Fin (n + 1) → Γ(X, V)) (E : Frame (sP (KS q s {V})) (n + 1))
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (y : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (x : CH.H (gr (sFil (KS q s {V})) r) (n + 1))
    (hx : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε y)) x) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t y) x := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have h5 := hL.2.2.2.2
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k =>
    addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)
  let h : Fin (n + 1) → ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T := fun k T =>
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) (t k)) -
      ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hJ : ∀ k T, h k T ∈ (sP (KS q s {V})).J.S T := fun k T => lift_sub_mem q s t E ε hL σ (t k) T
  have hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows (KS q s {V}).FullSubcategory 1),
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) = 0 := by
    intro k u
    simp only [form_one]
    have e1 : ∑ i, E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) *
        ((sP (KS q s {V})).A.map (σ _)).hom (ee E k i) = E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
      rw [Finset.sum_eq_single k]
      · rw [show ee E k k = 1 from if_pos rfl, map_one, mul_one]
      · intro i _ hi
        rw [show ee E k i = 0 from if_neg hi, map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [e1]
    have e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) =
        ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
          (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) := by
      unfold Frame.a
      rw [h5, GlobalTheory.CompanionTheory.CocProd.map_map]
    rw [e2]
    change ((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (show (sP (KS q s {V})).A.obj (u.obj 0) from _)) -
      (_ + (((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) - _) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom ((show (sP (KS q s {V})).A.obj (u.obj 0) from _) - _))) = 0
    rw [map_sub]
    ring
  have hl' := fun k u => (hl k u).symm ▸ ((sFil (KS q s {V}) 2).S _).zero_mem
  have hlm : ∀ k, ℓ k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
    intro k
    refine mem_FC.2 fun u => ?_
    have e : vl (ℓ k) u = ((∑ i, E.form σ ![i] (ee E k i) u) + (h k (u.obj (Fin.last 1)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) :=
      sub_eq_zero.1 (hl k u)
    rw [e]
    refine ((sFil _ _).S _).add_mem (((sFil _ _).S _).sum_mem fun i _ => mem_FC.1 (fc_mem E σ hF ![i] _) u) ?_
    rw [Nat.cast_one, hF.one]
    exact ((sP (KS q s {V})).J.S _).sub_mem (hJ _ _) ((sP (KS q s {V})).J.map_mem _ (hJ _ _))
  refine rep_back hF E σ hc ℓ h hJ hl' (ε y) r hr x _ (fun u => ?_) hx
  subst hr
  have hb := mem_FC.1 (cupList_mem hF (n + 1) ℓ hlm) u
  have e0 : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) =
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
        (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) *
      vl (cupListC (sP (KS q s {V})).A ℓ) u := by
    have e : CH.back (Nat.zero_add (n + 1)) = id := by
      funext i
      apply Fin.ext
      simp [CH.back]
    have := term_id (cupListC (sP (KS q s {V})).A ℓ) u _ (CH.back_mono (Nat.zero_add (n + 1))) e
    change _ * (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u _ _ _) = _
    rw [this]
  have ha : ∀ p : Fin (n + 2), ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last p)))).hom
      (show (sP (KS q s {V})).A.obj (u.obj p) from liftV (u.obj p).obj (ks_in q s V (u.obj p).obj (u.obj p).property) y) -
      ((sP (KS q s {V})).A.map (σ _)).hom (ε y) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    intro p
    rw [Nat.cast_one, hF.one]
    have e1 := (sP (KS q s {V})).J.map_mem (u.map (homOfLE (Fin.le_last p))) (lift_sub_mem q s t E ε hL σ y (u.obj p))
    have e2 := const1 hF hc (σ (u.obj p) ≫ u.map (homOfLE (Fin.le_last p))) (σ _) (ε y)
    have e3 := ((sP (KS q s {V})).J.S _).add_mem e1 e2
    rw [map_sub, GlobalTheory.CompanionTheory.CocProd.map_map, sub_add_sub_cancel] at e3
    exact e3
  have e4 := hF.mul _ _ _ hb (ha (CH.front (Nat.zero_add (n + 1)) (Fin.last 0)))
  have e5 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e5] at e4
  convert e4 using 1
  change (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) - _ = _
  have ea : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
        (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0)))))).hom
        (show (sP (KS q s {V})).A.obj (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))) from
          liftV (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))).obj
            (ks_in q s V _ (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))).property) y) := rfl
  rw [e0, ea]
  ring

end Loc

def i0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem idx_eq {m : ℕ} (I : Idx m m) : I = i0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

instance {m : ℕ} : Unique (Idx m m) := ⟨⟨i0 m⟩, idx_eq⟩

theorem sgn_det {B : Type} [CommRing B] {m : ℕ} (c : Fin m → Fin m → B) :
    ∑ J : Fin m → Fin m, sgn (i0 m) J • ∏ k, c k (J k) = (Matrix.of fun i k => c k i).det := by
  rw [Matrix.det_apply]
  simp only [sgn, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (⇑π)]
  · simp only [i0, Function.id_comp, if_true]
    rw [Units.smul_def]
    simp
  · intro J _ hJ
    simp [i0, hJ]
  · simp

theorem inv_map {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) : Ring.inverse (e a) = e (Ring.inverse a) := by
  by_cases h : IsUnit a
  · obtain ⟨v, rfl⟩ := h
    have e1 : e (v : A) = ((Units.map e.toMonoidHom v : Bˣ) : B) := rfl
    rw [e1, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (e a) := fun hu => h ((MulEquiv.isUnit_map e).1 hu)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

theorem inv_prod {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] (u : ι → A) (h : ∀ k, IsUnit (u k)) :
    Ring.inverse (∏ k, u k) = ∏ k, Ring.inverse (u k) := by
  choose v hv using h
  simp only [← hv]
  rw [← Units.coe_prod, Ring.inverse_unit, ← Finset.prod_inv_distrib, Units.coe_prod]
  simp only [Ring.inverse_unit]

theorem rep_one {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {m : ℕ} (E : Frame Φ m)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (w : Idx m m → Φ.A.obj E.D) (cl : CH.H (gr Fil r) m)
    (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m m, E.form σ I.1 (w I) u) cl) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id (w (i0 m))) cl := by
  refine rep_congr h fun u => ?_
  rw [Fintype.sum_unique]
  change E.form σ (i0 m).1 (w (i0 m)) u - _ ∈ _
  rw [show (i0 m).1 = id from rfl, sub_self]
  exact Ideal.zero_mem _

theorem main : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' →
    ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, V')), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
    (∀ k T, Ideal.Quotient.mk _ (ĝ k T) = ev T.obj (ks_in q s V' T.obj T.property) (g k)) →
    ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (cupListC (sP (KS q s {V'})).A fun k => dlogC (KS q s {V'}) s (ĝ k)) (x) →
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det)) (resKS q s hVV _ _ _ x) ∨
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (-(Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det))) (resKS q s hVV _ _ _ x) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD g hg ĝ hĝ x hx
  left
  obtain ⟨E, ε, hL⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.CompanionTheory.ConeLocal.taylor_loc q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have h1 := rep_res (ks_le q s hVV) _ _ hx
  choose h hh happ using fun k => GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main q s (by omega) hVV c.t E ε hL _ hT σ (g k) (hg k) (ĝ k) (hĝ k)
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s (ĝ k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i =>
    Ring.inverse (ε (rs hVV (g k))) * ε (D i (ε.symm (ε (rs hVV (g k)))))
  have h2 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from cupListC (sP (KS q s {V})).A ℓ u) *
        ((sP (KS q s {V})).A.map (σ _)).hom 1) (resKS q s hVV _ _ _ x) := by
    refine rep_congr h1 fun u => ?_
    have e := congrFun (cup_resQ (ks_le q s hVV) (fun k => dlogC (KS q s {V'}) s (ĝ k))) u
    rw [map_one, mul_one]
    exact (sub_eq_zero.2 e) ▸ Ideal.zero_mem _
  have h3 := GlobalTheory.CompanionTheory.CupRep.cup_rep hF E σ hc (n + 1) ℓ cc h hh happ 1 _ hr _ h2
  have h4 := GlobalTheory.CompanionTheory.ConeLocal.rep_collapse hF E σ hc (n + 1) _ hr (fun I => I) (fun I => 1 * ∏ k, cc k (I k)) _ h3
  have h5 := rep_one E σ _ (fun I => ∑ J, sgn I J • (1 * ∏ k, cc k (J k))) _ h4
  have hu : ∀ k, IsUnit (rs hVV (g k)) := fun k => (hg k).map (rs hVV)
  have e : ∑ J : Fin (n + 1) → Fin (n + 1), sgn (i0 (n + 1)) J • (1 * ∏ k, cc k (J k)) =
      ε (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det) := by
    simp only [one_mul]
    rw [sgn_det, inv_prod _ hu, ← Matrix.det_mul_row]
    have e1 := (ε : Γ(X, V) →+* (sP (KS q s {V})).A.obj E.D).map_det
      (Matrix.of fun k l => Ring.inverse (rs hVV (g l)) * D k (rs hVV (g l)))
    refine Eq.trans ?_ e1.symm
    congr 1
    ext i k
    simp [cc, inv_map]
  rw [e] at h5
  exact xdt_rep q s c.t E ε hL σ _ _ hr _ h5

end GlobalTheory.CompanionTheory.ConeLdlog
