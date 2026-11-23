import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompatStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.CocProd

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLRestr

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ}

theorem cupList_mem (hF : IsFil Φ Fil) : ∀ (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m := by
  intro m
  induction m with
  | zero =>
    intro ℓ _
    refine mem_FC.2 fun s => ?_
    rw [hF.top _ (by simp)]
    trivial
  | succ m ih =>
    intro ℓ h
    exact cup_mem hF _ (ih _ fun k => h _) (h _)

theorem rep_cup (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (n : ℕ) (ℓ : Fin (n + 1) → CH.Cn (CH.modF Φ.A) 1) (c : Fin (n + 1) → Fin d → Φ.A.obj E.D)
    (h : Fin (n + 1) → ∀ T : C, Φ.A.obj T) (hJ : ∀ k T, h k T ∈ Φ.J.S T)
    (hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows C 1), (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (c k i) u + (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) ∈ (Fil 2).S _)
    (w : Φ.A.obj E.D) (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (x : CH.H (gr Fil r) (n + 1))
    (hx : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Fin (n + 1) → Fin d, E.form σ I (w * ∏ k, c k (I k)) u) x) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => (show Φ.A.obj (u.obj (Fin.last (n + 1))) from cupListC Φ.A ℓ u) * (Φ.A.map (σ _)).hom w) x := by
  subst hr
  have hh : ∀ k, h0 (h k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun s => by
    have := hJ k (s.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (c k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k))) ∈
      FC (Fil ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (c k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k)))) u =
        (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (c k i) u +
          (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (c k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    exact hl k u
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ c (fun k => h0 (h k)) hh he
  have hz : ∀ u, (∑ I : Fin (n + 1) → Fin d, E.form σ I (w * ∏ k, c k (I k)) u) =
      vl (∑ I : Fin (n + 1) → Fin d, fc E σ I (∏ k, c k (I k))) u * (Φ.A.map (σ _)).hom w := by
    intro u
    rw [vl, Finset.sum_apply]
    change _ = (∑ I : Fin (n + 1) → Fin d, vl (fc E σ I (∏ k, c k (I k))) u) * _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => form_mul E σ I w _ u
  obtain ⟨H, hH, rfl⟩ := hg
  let H' : CH.Cn (CH.modF Φ.A) n := fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w
  have hH' : H' ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add hx (rep_d (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  rw [hz]
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc w hH u
  have e3 := (Fil _).S _ |>.add_mem (Ideal.mul_mem_right ((Φ.A.map (σ _)).hom w) _ e1) e2
  have e4 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e4] at e3
  have e5 := ((Fil _).S _).neg_mem e3
  convert e5 using 1
  change _ + vl (CH.d (CH.modF Φ.A) n H') u - _ = -((vl (cupListC Φ.A ℓ) u - vl (∑ I : Fin (n + 1) → Fin d, fc E σ I (∏ k, c k (I k))) u -
      vl (CH.d (CH.modF Φ.A) n H) u) * _ + (vl (CH.d (CH.modF Φ.A) n H) u * _ - vl (CH.d (CH.modF Φ.A) n H') u))
  ring

theorem rep_zero_cup (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (L : CH.Cn (CH.modF Φ.A) m) (hL : L ∈ FC (Fil (m : ℤ)) m) (zc : CH.Cn (CH.modF Φ.A) 0)
    (w : Φ.A.obj E.D) (hz : ∀ s : ComposableArrows C 0, vl zc s - (Φ.A.map (σ _)).hom w ∈ Φ.J.S _)
    (r : ℤ) (hr : r = m) (x : CH.H (gr Fil r) m)
    (hx : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => (show Φ.A.obj (u.obj (Fin.last m)) from L u) * (Φ.A.map (σ _)).hom w) x) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) ((CH.mulP Φ.A).cupC (Nat.zero_add m) zc L) x := by
  subst hr
  refine rep_congr hx fun u => ?_
  rw [CrystallineSemistableComparison.Auxff.cupC_apply]
  have e1 : CH.term (CH.modF Φ.A) u L (CH.back (Nat.zero_add m)) (CH.back_mono _) = L u :=
    CrystallineSemistableComparison.Auxff.term_id _ u L _ _ (fun t => by simp [CH.back])
  let s0 : ComposableArrows C 0 := (CH.front_mono (Nat.zero_add m)).functor ⋙ u
  let φ : s0.obj (Fin.last 0) ⟶ u.obj (Fin.last m) :=
    u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add m) (Fin.last 0))))
  have e0 : (show Φ.A.obj (u.obj (Fin.last m)) from CH.term (CH.modF Φ.A) u zc (CH.front (Nat.zero_add m)) (CH.front_mono _)) =
      (Φ.A.map φ).hom (vl zc s0) := rfl
  have a1 : (Φ.A.map φ).hom (vl zc s0) - (Φ.A.map (σ _ ≫ φ)).hom w ∈ Φ.J.S (u.obj (Fin.last m)) := by
    have h := Φ.J.map_mem φ (hz s0)
    rw [map_sub, map_map] at h
    exact h
  have a2 : (Φ.A.map (σ _ ≫ φ)).hom w - (Φ.A.map (σ _)).hom w ∈ Φ.J.S (u.obj (Fin.last m)) :=
    GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.const1 hF hc _ _ w
  have a3 := (Φ.J.S (u.obj (Fin.last m))).neg_mem ((Φ.J.S (u.obj (Fin.last m))).add_mem a1 a2)
  rw [sub_add_sub_cancel, neg_sub] at a3
  have a4 : (Φ.A.map (σ _)).hom w - (Φ.A.map φ).hom (vl zc s0) ∈ (Fil ((1 : ℕ) : ℤ)).S (u.obj (Fin.last m)) := by
    rw [Nat.cast_one, hF.one]
    exact a3
  have a5 := hF.mul m 1 _ (mem_FC.1 hL u) a4
  have e6 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  rw [e6, mul_sub] at a5
  rw [e1]
  change vl L u * (Φ.A.map (σ _)).hom w - (Φ.A.map φ).hom (vl zc s0) * vl L u ∈ _
  rw [mul_comm ((Φ.A.map φ).hom (vl zc s0))]
  exact a5

end Gen

section Conc

theorem rep_xdt {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) {V : X.Opens}
    (n : ℕ) (t : Fin (n + 1) → Γ(X, V)) (E : Frame (sP (KS q s {V})) (n + 1))
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (x : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (cl : HQ (KS q s {V}) r (r + 1) (n + 1))
    (h : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε x)) cl) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t x) cl := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  obtain ⟨hc, -, -, h4, h5⟩ := hL
  have hlift : ∀ (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory),
      Ideal.Quotient.mk T.obj.J (liftV T.obj (ks_in q s V T.obj T.property) g) = ev T.obj (ks_in q s V T.obj T.property) g :=
    fun g T => Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) g))
  have hlJ : ∀ (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory),
      (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) g) -
        ((sP (KS q s {V})).A.map (σ T)).hom (ε g) ∈ (sP (KS q s {V})).J.S T :=
    fun g T => Ideal.Quotient.eq.1 ((hlift g T).trans (h4 T (σ T) g))
  let l : Fin (n + 1) → ∀ T : (KS q s {V}).FullSubcategory, T.obj.B :=
    fun k T => liftV T.obj (ks_in q s V T.obj T.property) (t k)
  let hh : Fin (n + 1) → ∀ T, (sP (KS q s {V})).A.obj T :=
    fun k T => (show (sP (KS q s {V})).A.obj T from l k T) - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i => if k = i then 1 else 0
  have cc_self : ∀ k, cc k k = 1 := fun k => if_pos rfl
  have cc_ne : ∀ {k i : Fin (n + 1)}, k ≠ i → cc k i = 0 := fun h => if_neg h
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => addC (KS q s {V}) (l k)
  have heq : ∀ (k : Fin (n + 1)) (u : ComposableArrows (KS q s {V}).FullSubcategory 1),
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) =
        E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) + (hh k (u.obj (Fin.last 1)) -
          ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (hh k (u.obj 0))) := by
    intro k u
    have e1 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) = _ := h5 k (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1)))) (σ _)
    rw [e1]
    simp only [hh, map_sub, map_map]
    change (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from l k _) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (l k _) = _
    ring
  have hJ : ∀ k T, hh k T ∈ (sP (KS q s {V})).J.S T := fun k T => hlJ (t k) T
  have hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows (KS q s {V}).FullSubcategory 1),
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (cc k i) u + (hh k (u.obj (Fin.last 1)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (hh k (u.obj 0)))) ∈ (sFil (KS q s {V}) 2).S _ := by
    intro k u
    rw [heq]
    simp only [GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.form_one]
    rw [Finset.sum_eq_single k]
    · rw [cc_self, map_one, mul_one, sub_self]
      exact Ideal.zero_mem _
    · intro i _ hi
      rw [cc_ne (Ne.symm hi), map_zero, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  have hmem : ∀ k, ℓ k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
    intro k
    refine mem_FC.2 fun u => ?_
    rw [Nat.cast_one, hF.one]
    have e := heq k u
    change (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) ∈ _
    rw [e]
    exact Ideal.add_mem _ (E.mem k _ _) (Ideal.sub_mem _ (hJ k _) ((sP (KS q s {V})).J.map_mem _ (hJ k _)))
  have h1 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1))
      (fun u => ∑ I : Fin (n + 1) → Fin (n + 1), E.form σ I (ε x * ∏ k, cc k (I k)) u) cl := by
    refine rep_congr h fun u => ?_
    have e : ∑ I : Fin (n + 1) → Fin (n + 1), E.form σ I (ε x * ∏ k, cc k (I k)) u = E.form σ id (ε x) u := by
      rw [Finset.sum_eq_single id]
      · have e0 : ∏ k, cc k (id k) = 1 := Finset.prod_eq_one fun k _ => cc_self k
        rw [e0, mul_one]
      · intro I _ hI
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hI
        have e0 : ∏ k, cc k (I k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (cc_ne (Ne.symm hk))
        rw [e0, mul_zero]
        unfold Frame.form
        simp
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    rw [e, sub_self]
    exact Ideal.zero_mem _
  have h2 := rep_cup hF E σ hc n ℓ cc hh hJ hl (ε x) r hr cl h1
  exact rep_zero_cup hF E σ hc (n + 1) _ (cupList_mem hF _ ℓ hmem) _ (ε x) (fun s0 => hlJ x _) r hr cl h2

end Conc

def i0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem idx_eq {m : ℕ} (I : Idx m m) : I = i0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

local instance {m : ℕ} : Unique (Idx m m) := ⟨⟨i0 m⟩, idx_eq⟩

theorem rep_top {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {m : ℕ} (E : Frame Φ m)
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
    ∀ ω : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), ∃ x ∈ jacSpan hVV (RingHom.id _) (fun k => D k) id, Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t x) (resKS q s hVV _ _ _ ω) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD ω
  have : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
  obtain ⟨E, ε, hL⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega)).1 (resKS q s hVV _ _ _ ω)
  have h1 := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega) ω y hy (i0 _)
  exact ⟨y (i0 _), h1, rep_xdt q s n c.t E ε hL σ _ _ hr _ (rep_top E σ _ (fun I => ε (y I)) _ hy)⟩

end GlobalTheory.CompanionTheory.ConeLRestr
