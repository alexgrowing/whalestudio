import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaClosed

theorem exists_ideal_of_locally {R : Type} [CommRing R]
    (Q : ∀ (R' : Type) [CommRing R'], (R →+* R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (y : R →+* R') (φ : R' →+* R''), Q R' y → Q R'' (φ.comp y))
    (loc : ∀ (R' : Type) [CommRing R'] (y : R →+* R'), (∀ q : Ideal R', q.IsPrime → ∃ f ∉ q,
      Q (Localization.Away f) ((algebraMap R' _).comp y)) → Q R' y)
    (cl : ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (y : R →+* R'),
      IsUnit (y f) → (Q R' y ↔ ∀ r ∈ I, y r = 0)) :
    ∃ 𝔞 : Ideal R, ∀ (R' : Type) [CommRing R'] (y : R →+* R'), Q R' y ↔ ∀ r ∈ 𝔞, y r = 0 := by
  classical
  choose f hf I hI using cl
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact hf ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨s, hs⟩ : ∃ s : Finset (PrimeSpectrum R), Ideal.span (f '' (s : Set _)) = ⊤ := by
    obtain ⟨T, hT, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 htop)
    obtain ⟨s, rfl⟩ := Finset.subset_set_image_iff.1 (by rwa [← Set.image_univ] at hT : (T : Set R) ⊆ f '' Set.univ)
      |>.imp fun _ h => h.2
    exact ⟨s, (Ideal.eq_top_iff_one _).2 (by simpa using h1)⟩
  have star : ∀ (R' : Type) [CommRing R'] (y : R →+* R'), Q R' y → ∀ p, ∀ n ∈ I p, ∃ j : ℕ, y (f p ^ j * n) = 0 := by
    intro R' _ y hy p n hn
    have h := (hI p (Localization.Away (y (f p))) ((algebraMap R' _).comp y)
      (IsLocalization.Away.algebraMap_isUnit (y (f p)))).1 (bc _ _ y _ hy) n hn
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (y (f p))) _ _).1 h
    exact ⟨j, by simpa using hj⟩
  refine ⟨⟨⟨⟨{r | ∀ (R' : Type) [CommRing R'] (y : R →+* R'), Q R' y → y r = 0}, ?_⟩, ?_⟩, ?_⟩,
    fun R' _ y => ⟨fun hy r hr => hr R' y hy, fun hy => ?_⟩⟩
  · intro a b ha hb R' _ y hy
    rw [map_add, ha R' y hy, hb R' y hy, add_zero]
  · intro R' _ y _
    exact map_zero y
  · intro c a ha R' _ y hy
    rw [smul_eq_mul, map_mul, ha R' y hy, mul_zero]
  refine loc R' y fun q hq => ?_
  let p : PrimeSpectrum R := ⟨q.comap y, inferInstance⟩
  refine ⟨y (f p), hf p, ?_⟩
  have hu : IsUnit (((algebraMap R' (Localization.Away (y (f p)))).comp y) (f p)) :=
    IsLocalization.Away.algebraMap_isUnit (y (f p))
  refine (hI p _ _ hu).2 fun n hn => ?_
  have hj : ∀ i, ∃ j : ℕ, algebraMap R (Localization.Away (f i)) (f p ^ j * n) ∈
      (I i).map (algebraMap R (Localization.Away (f i))) := fun i => by
    have hQ := (hI i _ ((Ideal.Quotient.mk ((I i).map (algebraMap R (Localization.Away (f i))))).comp
      (algebraMap R (Localization.Away (f i))))
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f i)) (f i)).map
        (Ideal.Quotient.mk _))).2 fun r hr =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)
    obtain ⟨j, hj⟩ := star _ _ hQ p n hn
    exact ⟨j, Ideal.Quotient.eq_zero_iff_mem.1 hj⟩
  choose j hj using hj
  have key : y (f p ^ s.sup j * n) = 0 := by
    refine hy _ fun R'' _ y' hy' => ?_
    by_contra hne
    have hann : (Submodule.span R'' {y' (f p ^ s.sup j * n)}).annihilator ≠ ⊤ := by
      rw [Ne, Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot]
      exact hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
    have hex : ∃ i ∈ s, y' (f i) ∉ m := by
      by_contra hc
      push Not at hc
      have : Ideal.span (f '' (s : Set _)) ≤ m.comap y' := Ideal.span_le.2 (by
        rintro _ ⟨i, hi, rfl⟩
        exact hc i hi)
      rw [hs, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact hm.ne_top this
    obtain ⟨i, hi, him⟩ := hex
    let z : R →+* Localization.Away (y' (f i)) := (algebraMap R'' _).comp y'
    have hzu : IsUnit (z (f i)) := IsLocalization.Away.algebraMap_isUnit (y' (f i))
    have hz := (hI i _ z hzu).1 (bc _ _ y' _ hy')
    have hker : (I i).map (algebraMap R (Localization.Away (f i))) ≤
        RingHom.ker (IsLocalization.Away.lift (f i) hzu) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]
      exact hz r hr
    have h0 := hker (hj i)
    rw [RingHom.mem_ker, IsLocalization.Away.lift_eq] at h0
    have h1 : z (f p ^ s.sup j * n) = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := j) hi)
      rw [hd, add_comm, pow_add, _root_.mul_assoc, map_mul, h0, mul_zero]
    obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (y' (f i))) _ _).1 h1
    exact him (hm.isPrime.mem_of_pow_mem e (hle (Submodule.mem_annihilator_span_singleton _ _ |>.2 he)))
  have := congrArg (algebraMap R' (Localization.Away (y (f p)))) key
  rw [map_zero] at this
  have h2 : ((algebraMap R' (Localization.Away (y (f p)))).comp y) (f p ^ s.sup j * n) = 0 := this
  rw [map_mul, map_pow] at h2
  exact (hu.pow _).mul_right_eq_zero.1 h2

theorem exists_unit_of_minors {R I : Type} [CommRing R] {v w : I → R} (hv : Ideal.span (Set.range v) = ⊤)
    (hw : Ideal.span (Set.range w) = ⊤) (h : ∀ a b, v a * w b = v b * w a) : ∃ u : Rˣ, ∀ a, v a = u * w a := by
  have key : ∀ e ∈ Ideal.span (Set.range w), ∃ u, ∀ a, v a * e = u * w a := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨v b, fun a => h a b⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx; obtain ⟨u', hu'⟩ := hy
      exact ⟨u + u', fun a => by rw [mul_add, hu, hu', add_mul]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨c * u, fun a => by rw [smul_eq_mul, mul_left_comm, hu, _root_.mul_assoc]⟩
  obtain ⟨u, hu⟩ := key 1 (hw ▸ Submodule.mem_top)
  simp only [_root_.mul_one] at hu
  have : Ideal.span (Set.range v) ≤ Ideal.span {u} := Ideal.span_le.2 (by
    rintro _ ⟨a, rfl⟩
    exact Ideal.mem_span_singleton.2 ⟨_, hu a⟩)
  rw [hv, top_le_iff, Ideal.span_singleton_eq_top] at this
  exact ⟨this.unit, hu⟩

theorem span_map_eq_top {R R' I : Type} [CommRing R] [CommRing R'] (y : R →+* R') {v : I → R}
    (hv : Ideal.span (Set.range v) = ⊤) : Ideal.span (Set.range fun a => y (v a)) = ⊤ := by
  have := congrArg (Ideal.map y) hv
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

open ReciprocityTheory.ChartRestriction.G.Out in

theorem isThetaPtOver_of_iso {S : Scheme.{0}} (P : PolAV S) {k : ℕ} {T T₀ : Over S} (β : T ⟶ T₀) [IsIso β.left]
    {I : Type} {x₀ : I → (T₀ ⟶ P.A)} (hk : ∀ i, x₀ i ^ (k ^ 2) = 1) {v₀ : I → Γ(T₀.left, ⊤)}
    (H : IsThetaPtOver P k x₀ v₀) : IsThetaPtOver P k (fun i => β ≫ x₀ i) (fun i => β.left.appTop.hom (v₀ i)) := by
  have : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  refine ThetaPtMove.isThetaPtOver_move β.left (isGrpPullback_of_iso (Iso.refl P.A))
    (LBIso.symm (LBIso.chartPull (chartPullPull P.L _ (𝟙 _) rfl) (chartPullId _) (PolBaseChange.lbIso_refl P.isLB)))
    β.left (𝟙 T₀) (Category.comp_id _) ((Over.w β).trans (Category.comp_id _).symm) (fun th h s => ?_)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hk, MonObj.comp_one]) H
  obtain ⟨r, hr⟩ := h s
  have e := VVRank.pullM_id P.A P.isLB 1 (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩

open ReciprocityTheory.ChartRestriction.G.Out in

theorem isThetaPt_of_local {S : Scheme.{0}} (P : PolAV S) {k : ℕ} {T : Over S} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    (H : ∀ p : T.left, ∃ (T' : Over S) (j : T' ⟶ T), IsOpenImmersion j.left ∧ p ∈ Set.range j.left ∧
      IsThetaPt P k (fun i => j ≫ x i) (fun i => j.left.appTop.hom (v i))) : IsThetaPt P k x v := by
  refine ⟨ho, hu, fun p => ?_⟩
  obtain ⟨T', j, hj, ⟨p', rfl⟩, -, -, H⟩ := H p
  obtain ⟨V, hV, H⟩ := H p'
  refine ⟨j.left ''ᵁ V, ⟨p', hV, rfl⟩, ?_⟩
  have e : (j.left.isoImage V).inv ≫ V.ι ≫ j.left = (j.left ''ᵁ V).ι := Scheme.Hom.isoImage_inv_ι _ _
  let β : overRes (j.left ''ᵁ V) ⟶ overRes V := Over.homMk (j.left.isoImage V).inv (by
    show (j.left.isoImage V).inv ≫ V.ι ≫ T'.hom = (j.left ''ᵁ V).ι ≫ T.hom
    rw [← e, ← Over.w j]
    simp only [Category.assoc])
  have : IsIso β.left := inferInstanceAs (IsIso (j.left.isoImage V).inv)
  have e' : β ≫ overResι V ≫ j = overResι (j.left ''ᵁ V) := Over.OverMorphism.ext e
  have Q := isThetaPtOver_of_iso P β (fun i => by
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hk, MonObj.comp_one, MonObj.comp_one]) H
  convert Q using 2 with i i
  · rw [← e']
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.appTop.hom (v i)) e).symm

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}
  (t : TObj g (N' ^ 2) J b s)

theorem lab_pow (a : Ix g (N' ^ 2)) : t.lab a ^ (N' ^ 2) = 1 := by
  have := t.ab.comm
  have cm : ∀ x y : Out.baseOver S ⟶ t.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ (N' ^ 2) = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, t.torsion, one_pow]

theorem hasTh_unit_mul {R : Type} [CommRing R] {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (u : Rˣ)
    (H : t.HasTh x v) : t.HasTh x (fun a => u * v a) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, h₂, fun p => ?_⟩
  obtain ⟨V, hV, th, s₁, α, τ, U, s₂, w, u', a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := H p
  refine ⟨V, hV, th, s₁, α, τ, U, s₂, w, Out.unitRes V (unitOn u) * u', a₁, a₂, a₃, a₄, a₅, a₆, a₇, fun i => ?_⟩
  rw [Units.val_mul, _root_.mul_assoc, ← a₈ i]
  exact (congrArg V.ι.appTop.hom (map_mul _ _ _)).trans (map_mul _ _ _)

theorem hasTh_of_local (ho : Odd N') {R : Type} [CommRing R] {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R}
    (H : ∀ q : Ideal R, q.IsPrime → ∃ f ∉ q, t.HasTh (spMap (algebraMap R (Localization.Away f)) ≫ x)
      (fun a => algebraMap R (Localization.Away f) (v a))) : t.HasTh x v := by
  refine isThetaPt_of_local t.pol ho ?_ (fun a => ?_) fun p => ?_
  · have h := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map (x ≫ s).appTop.hom
    rw [map_natCast, map_natCast, Nat.cast_pow] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  · exact (MonObj.comp_pow _ _ _).symm.trans ((congrArg (_ ≫ ·) (lab_pow t a)).trans (MonObj.comp_one _))
  obtain ⟨f, hf, H⟩ := H (show PrimeSpectrum R from p).asIdeal inferInstance
  refine ⟨Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x),
    Over.homMk (spMap (algebraMap R (Localization.Away f))) rfl,
    inferInstanceAs (IsOpenImmersion (spMap (algebraMap R (Localization.Away f)))), ?_, ?_⟩
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
    exact this.ge hf
  · unfold TObj.HasTh at H
    convert H using 2 with a a
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.OverMorphism.ext rfl))
    · exact (congrArg (fun q => q.hom (v a))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (Localization.Away f))))).symm

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (y : R →+* R') (φ : R' →+* R'') :
    spMap φ ≫ spMap y = spMap (φ.comp y) := (Spec.map_comp (CommRingCat.ofHom y) (CommRingCat.ofHom φ)).symm

theorem exists_ideal_hasTh_iff : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (R : Type) [CommRing R] (s : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (v : Ix g (N' ^ 2) → R), Odd N' → 3 ≤ N' → Ideal.span (Set.range v) = ⊤ → ∃ 𝔞 : Ideal R, ∀ (R' : Type) [CommRing R'] (y : R →+* R'), t.HasTh (spMap y) (fun a => y (v a)) ↔ ∀ r ∈ 𝔞, y r = 0 := by
  intro h₁ h₂ o _ g N' J b R _ s t v ho h3 hv
  have bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (y : R →+* R') (φ : R' →+* R'') (w : Ix g (N' ^ 2) → R'),
      t.HasTh (spMap y) w → t.HasTh (spMap (φ.comp y)) (fun a => φ (w a)) := fun R' R'' _ _ y φ w H =>
    spMap_comp' y φ ▸ T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ s t R' R'' φ _ w H
  refine exists_ideal_of_locally (fun R' _ y => t.HasTh (spMap y) (fun a => y (v a)))
    (fun R' R'' _ _ y φ H => bc R' R'' y φ _ H) (fun R' _ y H => hasTh_of_local t ho fun q hq => ?_) fun p => ?_
  · obtain ⟨f, hf, H⟩ := H q hq
    exact ⟨f, hf, by rw [spMap_comp']; exact H⟩
  obtain ⟨R₁, _, x, w₁, hx, hp, H₁⟩ := T.exists_thetaConstants_locally_on_base h₁ h₂ o g N' J b _ s t ho p
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp
    (Spec.map φ).isOpenEmbedding.isOpen_range
  let L := Localization.Away f
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift (Spec.map φ) (spMap (algebraMap R L))
    ((PrimeSpectrum.localization_away_comap_range L f).le.trans hle))
  have e : ψ.hom.comp φ.hom = algebraMap R L := by
    have := IsOpenImmersion.lift_fac (Spec.map φ) (spMap (algebraMap R L))
      ((PrimeSpectrum.localization_away_comap_range L f).le.trans hle)
    rw [← hψ, ← Spec.map_comp] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨w, H⟩ : ∃ w, t.HasTh (spMap (algebraMap R L)) w := ⟨_, e ▸ bc R₁ L φ.hom ψ.hom w₁ H₁⟩
  have hw : Ideal.span (Set.range w) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨c, hc⟩ := T.thetaCosetNonvanishing_of_hasTh h₁ h₂ o g N' J b _ s t N' L _ w m (by omega) dvd_rfl H hm.isPrime 0
    exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))
  let M : Ideal L := Ideal.span {m | ∃ a c, m = algebraMap R L (v a) * w c - algebraMap R L (v c) * w a}
  refine ⟨f, hf, M.comap (algebraMap R L), fun R' _ y hy => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z : L →+* R', y = z.comp (algebraMap R L) :=
    ⟨IsLocalization.Away.lift f hy, (IsLocalization.Away.lift_comp f hy).symm⟩
  have H' := bc L R' _ z w H
  refine ⟨fun Hy r hr => ?_, fun Hy => ?_⟩
  · obtain ⟨u, hu⟩ := T.thetaConstants_unique_up_to_unit h₁ h₂ o g N' J b _ s t R' _ _ _ Hy H' (span_map_eq_top _ hv)
    have : M ≤ RingHom.ker z := Ideal.span_le.2 (by
      rintro _ ⟨a, c, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_mul, hu, hu]
      simp only [RingHom.comp_apply]
      ring)
    exact this hr
  · have hM : M ≤ RingHom.ker z := by
      rw [← IsLocalization.map_comap (Submonoid.powers f) L M, Ideal.map_le_iff_le_comap]
      exact fun r hr => Hy r hr
    obtain ⟨u, hu⟩ := exists_unit_of_minors (span_map_eq_top (z.comp (algebraMap R L)) hv) (span_map_eq_top z hw)
      fun a c => by
        have := hM (Ideal.subset_span ⟨a, c, rfl⟩)
        rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero] at this
        exact this
    rw [funext hu]
    exact hasTh_unit_mul t u H'

end GlobalTheory.ThetaClosed
