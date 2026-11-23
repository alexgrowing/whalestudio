import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoordsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfFormsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAboveStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

def I0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem idx_eq {m : ℕ} (I : Idx m m) : I = I0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

instance {m : ℕ} : Unique (Idx m m) := ⟨⟨I0 m⟩, idx_eq⟩

theorem sgn_det {B : Type} [CommRing B] {m : ℕ} (c : Fin m → Fin m → B) :
    ∑ J : Fin m → Fin m, sgn (I0 m) J • ∏ k, c k (J k) = (Matrix.of fun i k => c k i).det := by
  rw [Matrix.det_apply]
  simp only [sgn, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (⇑π)]
  · simp only [I0, Function.id_comp, if_true]
    rw [Units.smul_def]
    simp
  · intro J _ hJ
    simp [I0, hJ]
  · simp

theorem sgn_snoc {n : ℕ} (I : Idx n (n + 1)) (k : Fin (n + 1)) (h : I.1 ≠ k.succAbove) :
    sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) I.1 k) = 0 := by
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [if_neg]
  intro e
  exact h (GlobalTheory.T.strictMono_snoc_perm_eq_succAbove I.1 k π I.2 e)

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
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id (w (I0 m))) cl := by
  refine rep_congr h fun u => ?_
  rw [Fintype.sum_unique]
  change E.form σ (I0 m).1 (w (I0 m)) u - _ ∈ _
  rw [show (I0 m).1 = id from rfl, sub_self]
  exact Ideal.zero_mem _

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (n s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' → ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∃ φ : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1) →ₗ[K] Γ(X, V), Function.Injective φ ∧
      (∀ (g : Fin (n + 1) → Γ(X, V')), (∀ k, IsUnit (g k)) → ∀ ĝ : Fin (n + 1) → ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B, (∀ k T, Ideal.Quotient.mk T.obj.J (ĝ k T) = ev T.obj (ks_in q s V' _ T.property) (g k)) → ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1))
          (cupListC (sP (KS q s {V'})).A fun k => dlogC (KS q s {V'}) s (ĝ k)) x →
        φ (resKS q s hVV _ _ _ x) = Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det ∨
        φ (resKS q s hVV _ _ _ x) = -(Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det)) ∧
      (∀ ω : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        φ (resKS q s hVV _ _ _ ω) ∈ jacSpan hVV (RingHom.id _) (fun k => D k) id) ∧
      ∀ (f : CH.Cn (CH.modF (sP (KS q s {V'})).A) n), (∀ σ, f σ ∈ (sFil (KS q s {V'}) n).S _) →
        (∀ σ, CH.d _ n f σ ∈ (sFil (KS q s {V'}) ((n : ℤ) + 1)).S _) →
        ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (CH.d _ n f) x →
        ∃ η : Fin (n + 1) → Γ(X, V), (∀ k, η k ∈ jacSpan hVV (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
          φ (resKS q s hVV _ _ _ x) = ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) := by
  intro K _ _ X q _ n s hs V V' hVV hV' c D hD
  obtain ⟨E, ε, hL⟩ := GlobalTheory.T.exists_local_frame_of_coords q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨φ, hinj, hφ⟩ := GlobalTheory.T.top_graded_quotient_injective_map q c.t s E ε hL σ ((n : ℤ) + 1) hr (by omega)
  refine ⟨φ, hinj, ?_, ?_, ?_⟩
  · intro g hg ĝ hĝ x hx
    left
    have h1 := rep_res (ks_le q s hVV) _ _ hx
    choose h hh happ using fun k => GlobalTheory.T.local_frame_taylor_class_eq q s (by omega) hVV c.t E ε hL _ hT σ (g k) (hg k) (ĝ k) (hĝ k)
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
    have h3 := GlobalTheory.T.cup_list_representative_of_forms hF E σ hc (n + 1) ℓ cc h hh happ 1 _ hr _ h2
    have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun I => I) (fun I => 1 * ∏ k, cc k (I k)) _ h3
    have h5 := rep_one E σ _ (fun I => ∑ J, sgn I J • (1 * ∏ k, cc k (J k))) _ h4
    have hu : ∀ k, IsUnit (rs hVV (g k)) := fun k => (hg k).map (rs hVV)
    have e : ∑ J : Fin (n + 1) → Fin (n + 1), sgn (I0 (n + 1)) J • (1 * ∏ k, cc k (J k)) =
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
    exact hφ _ _ h5
  · intro ω
    obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega)).1 (resKS q s hVV _ _ _ ω)
    have h1 := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega) ω y hy (I0 _)
    have h2 := hφ (y (I0 _)) _ (rep_one E σ _ (fun I => ε (y I)) _ hy)
    rw [h2]
    exact h1
  · intro f hf hdf x hx
    obtain ⟨ξ, hξ⟩ := rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf
    have h1 := rep_res (ks_le q s hVV) _ _ hξ
    have h2 := rep_res (ks_le q s hVV) _ _ hx
    obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)
    have hmem := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy
    have h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
        (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x) := by
      refine rep_congr h2 fun u => ?_
      have e := congrFun (d_resQ (ks_le q s hVV) f) u
      exact (sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _
    have h3 := GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'
    have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2)
      (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3
    have h5 := rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4
    let Ik : Fin (n + 1) → Idx n (n + 1) := fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩
    let sg : Fin (n + 1) → ℤ := fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)
    refine ⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩
    · exact AddSubgroup.zsmul_mem _ (hmem (Ik k)) _
    · have e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) =
          ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by
        rw [Fintype.sum_prod_type_right, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single (Ik k)]
        · have a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; simp
          rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]
          push_cast
          have a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) =
              (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k))) := by
            linear_combination ((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1
          rw [a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]
        · intro I _ hI
          rw [sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [e] at h5
      exact hφ _ _ h5

end GlobalTheory.CompanionTheory.ConeLocal
