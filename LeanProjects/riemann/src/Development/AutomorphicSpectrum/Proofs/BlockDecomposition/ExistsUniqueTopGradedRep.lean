import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeTopChart

open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.CocProd

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem rep_shift {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C (j + 1), A.obj (s.obj (Fin.last (j + 1)))}
    {c : CH.H (sq a b) (j + 1)} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (G : CH.Cn (CH.modF A) j)
    (hG : ∀ s : ComposableArrows C j, (show A.obj (s.obj (Fin.last j)) from G s) ∈ a.S _)
    (e : ∀ s : ComposableArrows C (j + 1), z' s - (z s + (show A.obj (s.obj (Fin.last (j + 1))) from CH.d _ j G s)) ∈ b.S _) :
    CrystallineSemistableComparison.Pb.Rep a b z' c := by
  have h1 := rep_add h (rep_d (b := b) G hG)
  rw [add_zero] at h1
  refine rep_congr h1 fun s => ?_
  have h2 := (b.S _).neg_mem (e s)
  rw [neg_sub] at h2
  exact h2

theorem term_id {k : ℕ} (u : ComposableArrows C k) (f : CH.Cn (CH.modF A) k) (g : Fin (k + 1) → Fin (k + 1))
    (hg : Monotone g) (e : g = id) :
    (show A.obj (u.obj (Fin.last k)) from CH.term (CH.modF A) u f g hg) = (show A.obj (u.obj (Fin.last k)) from f u) := by
  subst e
  change (A.map (u.map (homOfLE (Fin.le_last (Fin.last k))))).hom (f u) = _
  rw [show (homOfLE (Fin.le_last (Fin.last k)) : Fin.last k ⟶ Fin.last k) = 𝟙 _ from Subsingleton.elim _ _,
    u.map_id, A.map_id]
  rfl

theorem back_zero (k : ℕ) : CH.back (Nat.zero_add k) = id := by
  funext i
  apply Fin.ext
  simp [CH.back]

end Gen

def J0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem top_index_eq {m : ℕ} (I : Idx m m) : I = J0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

section Lift
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) :
    Ideal.Quotient.mk T.J (liftV T h g) = ev T h g :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T h g))

theorem map_liftV {s : ℕ} {V : X.Opens} {T T' : (KS q s {V}).FullSubcategory} (φ : T ⟶ T') (g : Γ(X, V)) :
    Ideal.Quotient.mk T'.obj.J (((sP (KS q s {V})).A.map φ).hom (liftV T.obj (ks_in q s V _ T.property) g)) =
      ev T'.obj (ks_in q s V _ T'.property) g := by
  rw [GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) φ.hom (ks_in q s V _ T.property) (ks_in q s V _ T'.property) g, ← mk_liftV]
  rfl

end Lift

end GlobalTheory.CompanionTheory.ConeTopChart

namespace GlobalTheory.CompanionTheory.ConeTopChart
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.CocProd
section Key
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem lift_sub {s : ℕ} {V : X.Opens} {d : ℕ} {t : Fin d → Γ(X, V)} {E : Frame (sP (KS q s {V})) d}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) {T T' : (KS q s {V}).FullSubcategory}
    (φ : T ⟶ T') (u : E.D ⟶ T') (g : Γ(X, V)) :
    ((sP (KS q s {V})).A.map φ).hom (liftV T.obj (ks_in q s V _ T.property) g) - ((sP (KS q s {V})).A.map u).hom (ε g) ∈
      (sFil (KS q s {V}) 1).S T' := by
  rw [(GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})).one T']
  exact Ideal.Quotient.eq.1 ((map_liftV φ g).trans (hL.2.2.2.1 T' u g))

theorem lift_sub_mem_ideal {s : ℕ} {V : X.Opens} {d : ℕ} {t : Fin d → Γ(X, V)} {E : Frame (sP (KS q s {V})) d}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (T : (KS q s {V}).FullSubcategory)
    (u : E.D ⟶ T) (g : Γ(X, V)) :
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V _ T.property) g) - ((sP (KS q s {V})).A.map u).hom (ε g) ∈
      (sP (KS q s {V})).J.S T :=
  Ideal.Quotient.eq.1 ((mk_liftV _ _ g).trans (hL.2.2.2.1 T u g))

theorem addC_near {s : ℕ} {V : X.Opens} {d : ℕ} {t : Fin d → Γ(X, V)} {E : Frame (sP (KS q s {V})) d}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (k : Fin d)
    (u : ComposableArrows (KS q s {V}).FullSubcategory 1) :
    (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from
      addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V _ T.property) (t k)) u) -
    (∑ i, E.form σ ![i] (if k = i then 1 else 0) u +
      ((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from liftV (u.obj (Fin.last 1)).obj (ks_in q s V _ (u.obj (Fin.last 1)).property) (t k)) -
        ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
       ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
        ((show (sP (KS q s {V})).A.obj (u.obj 0) from liftV (u.obj 0).obj (ks_in q s V _ (u.obj 0).property) (t k)) -
          ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))))) = 0 := by
  rw [Finset.sum_eq_single k (fun i _ hi => by
    rw [if_neg (Ne.symm hi)]; unfold Frame.form; rw [map_zero, mul_zero]) (by simp), if_pos rfl]
  unfold Frame.form Frame.a
  rw [Fin.prod_univ_one]
  simp only [Matrix.cons_val_zero, map_one, mul_one]
  have hφ : u.map (homOfLE (Fin.le_last (0 : Fin 1).succ)) = 𝟙 _ := by rw [← u.map_id]; rfl
  rw [hφ, (sP (KS q s {V})).A.map_id, hL.2.2.2.2 k, Functor.map_comp, CommAlgCat.hom_comp, AlgHom.comp_apply]
  change (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from liftV (u.obj (Fin.last 1)).obj (ks_in q s V _ (u.obj (Fin.last 1)).property) (t k)) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
        (show (sP (KS q s {V})).A.obj (u.obj 0) from liftV (u.obj 0).obj (ks_in q s V _ (u.obj 0).property) (t k)) -
    (((sP (KS q s {V})).A.map (σ (u.obj (Fin.last 1)))).hom (ε (t k)) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ (u.obj 0))).hom (ε (t k))) +
      ((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from liftV (u.obj (Fin.last 1)).obj (ks_in q s V _ (u.obj (Fin.last 1)).property) (t k)) -
        ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
       ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
        ((show (sP (KS q s {V})).A.obj (u.obj 0) from liftV (u.obj 0).obj (ks_in q s V _ (u.obj 0).property) (t k)) -
          ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))))) = 0
  rw [map_sub]
  ring

end Key
end GlobalTheory.CompanionTheory.ConeTopChart

namespace GlobalTheory.CompanionTheory.ConeTopChart
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.CocProd
section Key2
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem key {s : ℕ} {V : X.Opens} {n : ℕ} {t : Fin (n + 1) → Γ(X, V)} {E : Frame (sP (KS q s {V})) (n + 1)}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (x : Γ(X, V)) :
    ∃ G : CH.Cn (CH.modF (sP (KS q s {V})).A) n,
      (∀ u : ComposableArrows (KS q s {V}).FullSubcategory n,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from G u) ∈ (sFil (KS q s {V}) ((n : ℤ) + 1)).S _) ∧
      ∀ u : ComposableArrows (KS q s {V}).FullSubcategory (n + 1),
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC (q := q) s V t x u) -
          (E.form σ id (ε x) u + (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.d _ n G u)) ∈
          (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)).S _ := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k =>
    addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V _ T.property) (t k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i => if k = i then 1 else 0
  let hk : Fin (n + 1) → ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T := fun k T =>
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V _ T.property) (t k)) -
      ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hh : ∀ k, h0 (hk k) ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun u => by
    rw [Nat.cast_one, hF.one]
    exact lift_sub_mem_ideal hL _ (σ _) (t k)
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hk k))) ∈
      FC (sFil (KS q s {V}) ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hk k)))) u = 0 := by
      have e1 : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hk k)))) u =
          vl (ℓ k) u - (∑ i, E.form σ ![i] (cc k i) u + vl (CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hk k))) u) := by
        change vl (ℓ k) u - (vl (∑ i, fc E σ ![i] (cc k i)) u + _) = _
        congr 2
        rw [vl, Finset.sum_apply]
        rfl
      rw [e1, cech_d_h0_eval]
      exact addC_near hL σ k u
    rw [e]
    exact zero_mem _
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ cc (fun k => h0 (hk k)) hh he
  obtain ⟨H, hH, rfl⟩ := hg
  have hsum : ∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, cc k (I k)) = fc E σ id 1 := by
    rw [Finset.sum_eq_single id]
    · congr 1
      simp [cc]
    · intro I _ hI
      obtain ⟨k, hk'⟩ : ∃ k, I k ≠ k := by
        by_contra h
        push_neg at h
        exact hI (funext h)
      have h0' : ∏ k, cc k (I k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (by simp [cc, Ne.symm hk'])
      rw [h0']
      funext u'
      change E.form σ I 0 u' = 0
      unfold Frame.form
      rw [map_zero, mul_zero]
    · simp
  rw [hsum] at hn
  refine ⟨fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from H u) * ((sP (KS q s {V})).A.map (σ _)).hom (ε x),
    fun u => ?_, fun u => ?_⟩
  · have h1 := mem_FC.1 hH u
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e] at h1
    exact Ideal.mul_mem_right _ _ h1
  · set Y := ((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε x) with hY
    set P := vl (cupListC (sP (KS q s {V})).A ℓ) u with hP
    set Fc := vl (fc E σ id 1) u with hFc
    set D := vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u with hD
    have hv : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC (q := q) s V t x u) =
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
          (zeroC (KS q s {V}) fun T => liftV T.obj (ks_in q s V _ T.property) x) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) * P := by
      change _ * (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
        (cupListC (sP (KS q s {V})).A ℓ) (CH.back (Nat.zero_add (n + 1))) (CH.back_mono _)) = _
      rw [term_id u _ _ _ (back_zero _)]
    have hFY : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
          (zeroC (KS q s {V}) fun T => liftV T.obj (ks_in q s V _ T.property) x) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) - Y ∈
        (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
      rw [Nat.cast_one]
      exact lift_sub hL (u.map (homOfLE (Fin.le_last _))) (σ _) x
    have hform : E.form σ id (ε x) u = Fc * Y := by
      have := form_mul E σ id (ε x) 1 u
      rwa [mul_one] at this
    have hR : P - Fc - D ∈ (sFil (KS q s {V}) ((n + 1 + 1 : ℕ) : ℤ)).S _ := mem_FC.1 hn u
    have hdm := d_mul E σ hF hc (ε x) hH u
    have hFcm : Fc ∈ (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)).S _ := mem_FC.1 (fc_mem E σ hF id 1) u
    have hDm : D ∈ (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)).S _ := mem_FC.1 (d_mem hH) u
    have hPm : P ∈ (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)).S _ := by
      have h1 := hF.anti (r := ((n + 1 : ℕ) : ℤ)) (by push_cast; omega) _ hR
      have h2 := add_mem (add_mem h1 hDm) hFcm
      rwa [sub_add_cancel, sub_add_cancel] at h2
    have hm1 := hF.mul 1 (n + 1) _ hFY hPm
    rw [show 1 + (n + 1) = n + 1 + 1 by omega] at hm1
    have hall := add_mem (add_mem hm1 (Ideal.mul_mem_left _ Y hR)) hdm
    have e2 : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 1 + 1 := by push_cast; ring
    rw [e2] at hall
    rw [hv, hform]
    convert hall using 1
    ring

end Key2
end GlobalTheory.CompanionTheory.ConeTopChart

namespace GlobalTheory.CompanionTheory.ConeTopChart

theorem top_chart : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V : X.Opens) (c : Coord q V (n + 1)) (y : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1)),
    ∃! x : Γ(X, V), Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t x) (y) := by
  intro _ _ _ K _ _ X q n _ s hs V c y
  obtain ⟨E, ε, hL⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨hex, huniq⟩ := GlobalTheory.CompanionTheory.ConeLocal.loc_coef q c.t s E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega)
  have toForm : ∀ (x : Γ(X, V)) (z : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (E.form σ id (ε x)) z ↔
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t x) z := by
    intro x z
    obtain ⟨G, hG, hGe⟩ := key hL σ x
    constructor
    · intro h
      exact rep_shift h G hG hGe
    · intro h
      refine rep_shift h (-G) (fun u => (Ideal.neg_mem_iff _).2 (hG u)) (fun u => ?_)
      have e : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.d _ n (-G) u) =
          -(show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.d _ n G u) := by
        rw [map_neg]
        rfl
      rw [e]
      convert (Ideal.neg_mem_iff _).2 (hGe u) using 1
      ring
  have uniqForm : ∀ (x x' : Γ(X, V)) (z : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (E.form σ id (ε x)) z →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (E.form σ id (ε x')) z →
      x = x' := by
    intro x x' z h h'
    have h2 := rep_add h (rep_smul (-1 : K) h')
    have e0 : z + (-1 : K) • z = 0 := by rw [neg_one_smul, add_neg_cancel]
    rw [e0] at h2
    have h3 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
        (fun u => ∑ I : Idx (n + 1) (n + 1), E.form σ I.1 (ε ((fun _ => x - x') I)) u) 0 := by
      refine rep_congr h2 fun u => ?_
      rw [Finset.sum_eq_single (J0 _) (fun I _ hI => absurd (top_index_eq I) hI) (by simp)]
      have e1 : E.form σ id (ε x) u + (-1 : K) • E.form σ id (ε x') u - E.form σ (J0 (n + 1)).1 (ε (x - x')) u = 0 := by
        change _ - E.form σ id (ε (x - x')) u = 0
        unfold Frame.form
        rw [map_sub, map_sub, neg_one_smul]
        ring
      rw [e1]
      exact zero_mem _
    have h4 := congrFun (huniq (fun _ => x - x') h3) (J0 _)
    exact sub_eq_zero.1 h4
  obtain ⟨y', hy'⟩ := hex y
  have h1 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (E.form σ id (ε (y' (J0 _)))) y := by
    refine rep_congr hy' fun u => ?_
    rw [Finset.sum_eq_single (J0 _) (fun I _ hI => absurd (top_index_eq I) hI) (by simp)]
    change E.form σ id (ε (y' (J0 _))) u - E.form σ id (ε (y' (J0 _))) u ∈ _
    rw [sub_self]
    exact zero_mem _
  exact ⟨y' (J0 _), (toForm _ _).1 h1, fun x' hx' => uniqForm _ _ _ ((toForm _ _).2 hx') h1⟩

end GlobalTheory.CompanionTheory.ConeTopChart
