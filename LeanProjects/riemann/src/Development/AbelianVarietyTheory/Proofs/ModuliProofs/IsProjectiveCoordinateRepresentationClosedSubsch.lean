import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ClosedCoord
open MvPolynomial

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_ideal_factor {Y Z : Scheme.{0}} (i : Y ⟶ Z) [IsClosedImmersion i] {S : Type} [CommRing S]
    (x : Sp S ⟶ Z) : ∃ J : Ideal S, ∀ (R' : Type) [CommRing R'] (φ : S →+* R'),
      (∃ y : Sp R' ⟶ Y, y ≫ i = spMap φ ≫ x) ↔ ∀ f ∈ J, φ f = 0 := by
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.1 (inferInstance : IsClosedImmersion (pullback.snd i x))
  refine ⟨J, fun R' _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩ f hf
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (spMap φ) hy ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ ψ) = spMap φ := by
      rw [Spec.map_comp, hψ, Category.assoc, ← he, pullback.lift_snd]
    have h2 := Spec.map_injective h1
    have h3 : ψ.hom (Ideal.Quotient.mk J f) = φ f := congrArg (fun t => t.hom f) h2
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · intro h
    refine ⟨spMap (Ideal.Quotient.lift J φ h) ≫ e.inv ≫ pullback.fst i x, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl

theorem exists_homogenisation {R σ : Type} [CommRing R] (a : σ) (F : MvPolynomial σ R) :
    ∃ (d : ℕ) (G : MvPolynomial σ R),
      (∀ (R' : Type) [CommRing R'] (β : R →+* R') (u : R') (w : σ → R'),
        eval₂ β (fun j => u * w j) G = u ^ d * eval₂ β w G) ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (w : σ → R'), w a = 1 → eval₂ β w G = eval₂ β w F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
  | add p q hp hq =>
    obtain ⟨d, G, h1, h2⟩ := hp
    obtain ⟨d', G', h1', h2'⟩ := hq
    refine ⟨d + d', X a ^ d' * G + X a ^ d * G', fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h1, h1']; ring
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h2 _ β w hw, h2' _ β w hw, hw]; ring
  | mul_X p n hp =>
    obtain ⟨d, G, h1, h2⟩ := hp
    refine ⟨d + 1, G * X n, fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_mul, eval₂_X, h1]; ring
    · simp only [eval₂_mul, eval₂_X, h2 _ β w hw]

theorem eq_zero_of_away {R' σ : Type} [CommRing R'] (v : σ → R') (hv : Ideal.span (Set.range v) = ⊤) (r : R')
    (h : ∀ a, algebraMap R' (Localization.Away (v a)) r = 0) : r = 0 := by
  have : r ∈ (⊥ : Ideal R') := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range v) hv r ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (v a)) _ r).1 (h a)
    exact ⟨n, by simpa using hn⟩
  simpa using this

def awayUnit {R' : Type} [CommRing R'] (r : R') : (Localization.Away r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).unit

theorem awayUnit_coe {R' : Type} [CommRing R'] (r : R') :
    (awayUnit r : Localization.Away r) = algebraMap R' _ r := rfl

theorem awayUnit_inv_mul {R' : Type} [CommRing R'] (r : R') :
    ((awayUnit r)⁻¹ : (Localization.Away r)ˣ) * algebraMap R' (Localization.Away r) r = 1 := by
  rw [← awayUnit_coe]; exact Units.inv_mul _

theorem away_of_vanishing {R σ : Type} [CommRing R] [Finite σ]
    (P : ∀ (R' : Type) [CommRing R'], (R →+* R') → (σ → R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (φ : R' →+* R'') β v, P R' β v → P R'' (φ.comp β) (fun j => φ (v j)))
    (sc : ∀ (R' : Type) [CommRing R'] (u : R'ˣ) β v, P R' β v → P R' β (fun j => u * v j))
    (uni : ∀ (R' : Type) [CommRing R'] β v, P R' β v → Ideal.span (Set.range v) = ⊤)
    (ch : ∀ a, ∃ K : Ideal (MvPolynomial σ R), X a - 1 ∈ K ∧ ∀ (R' : Type) [CommRing R'] β w, w a = 1 →
      (P R' β w ↔ ∀ F ∈ K, eval₂ β w F = 0))
    (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R')
    (hv : ∀ F, (∀ (R'' : Type) [CommRing R''] β' w, P R'' β' w → eval₂ β' w F = 0) → eval₂ β v F = 0) (a : σ) :
    P (Localization.Away (v a)) ((algebraMap R' _).comp β) (fun j => algebraMap R' _ (v j)) := by
  classical
  choose K hK1 hK using ch
  have := Fintype.ofFinite σ

  have nrm : ∀ (A : Type) [CommRing A] β₀ (t : σ → A) (b : σ), P A β₀ t → ∀ F ∈ K b,
      eval₂ ((algebraMap A (Localization.Away (t b))).comp β₀)
        (fun j => ((awayUnit (t b))⁻¹ : (Localization.Away (t b))ˣ) * algebraMap A _ (t j)) F = 0 := by
    intro A _ β₀ t b ht
    exact (hK b _ _ _ (awayUnit_inv_mul _)).1 (sc _ _ _ _ (bc _ _ _ _ _ ht))
  suffices h : P (Localization.Away (v a)) ((algebraMap R' _).comp β)
      (fun j => ((awayUnit (v a))⁻¹ : (Localization.Away (v a))ˣ) * algebraMap R' _ (v j)) by
    have h2 := sc _ (awayUnit (v a)) _ _ h
    simpa only [Units.mul_inv_cancel_left] using h2
  refine (hK a _ _ _ (awayUnit_inv_mul _)).2 fun F hF => ?_
  obtain ⟨d, G, hG, hGF⟩ := exists_homogenisation a F
  have step : ∀ b, ∃ n : ℕ, X a ^ n * G ∈ K b := by
    intro b
    have hP : P (MvPolynomial σ R ⧸ K b) ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j)) := by
      refine (hK b _ _ _ ?_).2 fun F' hF' => ?_
      · rw [← map_one (Ideal.Quotient.mk (K b)), Ideal.Quotient.eq]; exact hK1 b
      · have := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X F').symm
        rw [eval₂_eta, Ideal.Quotient.eq_zero_iff_mem.2 hF'] at this
        exact this
    have h1 := nrm _ _ _ a hP F hF
    rw [← hGF _ _ _ (awayUnit_inv_mul _), hG, (Units.isUnit _).pow d |>.mul_right_eq_zero] at h1
    have h2 := eval₂_comp_left (algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))))
      ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk (K b) (X j)) G
    have h3 := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X G)
    rw [eval₂_eta] at h3
    have h4 : algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))) (Ideal.Quotient.mk (K b) G) = 0 := by
      rw [h3]; exact h2.trans h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (K b) (X a))) _ _).1 h4
    refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hn
  choose n hn using step
  have hH : eval₂ β v (X a ^ (∑ b, n b) * G) = 0 := by
    refine hv _ fun A _ β₀ t ht => eq_zero_of_away t (uni _ _ _ ht) _ fun b => ?_
    have hm : X a ^ (∑ b, n b) * G ∈ K b := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      rw [hm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn b)
    have h1 := nrm _ _ _ b ht _ hm
    rw [eval₂_comp_left]
    rw [eval₂_mul, eval₂_pow, eval₂_X, hG, mul_pow, _root_.mul_mul_mul_comm, ← pow_add,
      (Units.isUnit _).pow _ |>.mul_right_eq_zero] at h1
    rw [eval₂_mul, eval₂_pow, eval₂_X]
    exact h1
  have h5 := congrArg (algebraMap R' (Localization.Away (v a))) hH
  rw [eval₂_mul, eval₂_pow, eval₂_X, map_mul, map_pow, map_zero, ← awayUnit_coe,
    (Units.isUnit _).pow _ |>.mul_right_eq_zero, eval₂_comp_left] at h5
  rw [← hGF _ _ _ (awayUnit_inv_mul _), hG]
  exact mul_eq_zero_of_right _ h5

theorem projRep_closed : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by
  intro R σ _ _ I Z Y s M th i N ty ⟨hM, hloc, hpts⟩ hi hN hc
  have mem : ∀ F, F ∈ idealOf (i ≫ s) N ty (𝟙 Y) ↔ ∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y)
      (v : σ → R'), y ≫ i ≫ s = spMap β → SecCoord M th (y ≫ i) v → eval₂ β v F = 0 := by
    intro F
    simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, coe_eval₂Hom, Category.comp_id, hc, and_imp]
  have hbc : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Sp A ⟶ Z) (v : σ → A),
      SecCoord M th x v → SecCoord M th (spMap φ ≫ x) (fun j => φ (v j)) :=
    fun A B _ _ φ x v h => (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A x v hM h).1 B φ
  have huniq : ∀ (A : Type) [CommRing A] (β : R →+* A) (v : σ → A) (x x' : Sp A ⟶ Z), x ≫ s = spMap β →
      SecCoord M th x v → x' ≫ s = spMap β → SecCoord M th x' v → x = x' := by
    intro A _ β v x x' h1 h2 h3 h4
    obtain ⟨h5, h6⟩ := hloc A β x v h1 h2
    exact (hpts A β v h5 h6).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hN, fun R' _ β y v h1 h2 => ?_, fun R' _ β v hv hI => ?_⟩
  · rw [hc] at h2
    exact ⟨(hloc R' β (y ≫ i) v (by simpa using h1) h2).1, fun F hF => (mem F).1 hF R' β y v h1 h2⟩
  have hIv : ∀ F ∈ I, eval₂ β v F = 0 := fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 =>
    (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF)
  obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hpts R' β v hv hIv
  have key := away_of_vanishing (R := R) (σ := σ)
    (fun A _ β' w => ∃ y : Sp A ⟶ Y, y ≫ i ≫ s = spMap β' ∧ SecCoord M th (y ≫ i) w)
    (by
      rintro A B _ _ φ β' w ⟨y, h1, h2⟩
      refine ⟨spMap φ ≫ y, by rw [Category.assoc, h1, spMap_comp_eq], ?_⟩
      rw [Category.assoc]; exact hbc _ _ φ _ _ h2)
    (by
      rintro A _ u β' w ⟨y, h1, h2⟩
      exact ⟨y, h1, (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A _ w hM h2).2.1 u⟩)
    (by
      rintro A _ β' w ⟨y, h1, h2⟩
      exact (hloc A β' (y ≫ i) w (by simpa using h1) h2).1)
    (by
      intro a
      have hq : ∀ F, eval₂ ((Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})).comp C)
          (fun j => Ideal.Quotient.mk _ (X j)) F = Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}) F := by
        intro F
        have := (eval₂_comp_left (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) C X F).symm
        rw [eval₂_eta] at this
        exact this
      have ha : X a - 1 ∈ I ⊔ Ideal.span {X a - 1} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      obtain ⟨xa, ⟨hxa1, hxa2⟩, -⟩ := hpts (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {X a - 1}))
        ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j))
        (by
          rw [Ideal.eq_top_iff_one]
          refine Ideal.subset_span ⟨a, ?_⟩
          rw [← map_one (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}))]
          exact Ideal.Quotient.eq.2 ha)
        (fun F hF => by rw [hq]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
      obtain ⟨J, hJ⟩ := exists_ideal_factor i xa
      have hle : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, F ∈ J.comap (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) := by
        intro F hF
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hF]; exact J.zero_mem
      refine ⟨J.comap (Ideal.Quotient.mk _), hle _ ha, fun A _ β' w hw => ?_⟩
      have main : ∀ h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0,
          (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) ≫ s = spMap β' ∧
            SecCoord M th (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) w := by
        intro h
        refine ⟨?_, ?_⟩
        · rw [Category.assoc, hxa1, spMap_comp_eq]
          congr 1
          ext r
          simp
        · have := hbc _ _ (Ideal.Quotient.lift _ _ h) _ _ hxa2
          simpa using this
      constructor
      · rintro ⟨y, h1, h2⟩ F hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := by
          intro F hF
          have hle' : I ⊔ Ideal.span {X a - 1} ≤ RingHom.ker (eval₂Hom β' w) := by
            refine sup_le (fun F hF => (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF) ?_
            rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
            simp [hw]
          exact hle' hF
        have e := huniq A β' w _ _ (by simpa using h1) h2 (main h).1 (main h).2
        exact (hJ A _).1 ⟨y, e⟩ _ hF
      · intro hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := fun F h => hF F (hle F h)
        obtain ⟨y, hy⟩ := (hJ A (Ideal.Quotient.lift _ _ h)).2 (by
          intro f hf
          obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
          exact hF F hf)
        exact ⟨y, by rw [← Category.assoc, hy]; exact (main h).1, by rw [hy]; exact (main h).2⟩)
    R' β v (fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 => hF A β' w ⟨y, h1, h2⟩))
  obtain ⟨J, hJ⟩ := exists_ideal_factor i x
  obtain ⟨y, hy⟩ := (hJ R' (RingHom.id R')).2 (by
    intro f hf
    refine eq_zero_of_away v hv f fun a => ?_
    obtain ⟨y, h1, h2⟩ := key a
    refine (hJ _ (algebraMap R' _)).1 ⟨y, ?_⟩ f hf
    refine huniq _ _ _ _ _ (by simpa using h1) h2 ?_ (hbc _ _ _ _ _ hx2)
    rw [Category.assoc, hx1, spMap_comp_eq])
  have hid : spMap (RingHom.id R') = 𝟙 (Sp R') := Spec.map_id _
  rw [hid, Category.id_comp] at hy
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hx1], by rw [hc, hy]; exact hx2⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  rw [hc] at h2
  rw [← cancel_mono i, hy]
  exact huniq _ _ _ _ _ (by simpa using h1) h2 hx1 hx2

end GlobalTheory.ZM.ClosedCoord
end
