import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem unit_of_pow {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Kˣ) {n : ℕ} (hn : 0 < n) (a b : Rˣ)
    (h : algebraMap R K a = (x : K) ^ n * algebraMap R K b) : ∃ y : Rˣ, algebraMap R K y = x := by
  have hb : algebraMap R K b * algebraMap R K (b⁻¹ : Rˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have ha : algebraMap R K a * algebraMap R K (a⁻¹ : Rˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hx : (x : K) ^ n * ((x⁻¹ : Kˣ) : K) ^ n = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have h₁ : (x : K) ^ n = algebraMap R K (a * (b⁻¹ : Rˣ)) := by
    rw [map_mul, h, _root_.mul_assoc, hb, _root_.mul_one]
  have h₂ : ((x⁻¹ : Kˣ) : K) ^ n = algebraMap R K (b * (a⁻¹ : Rˣ)) := by
    rw [map_mul]
    linear_combination (-((x⁻¹ : Kˣ) : K) ^ n) * ha + ((x⁻¹ : Kˣ) : K) ^ n * algebraMap R K (a⁻¹ : Rˣ) * h
      + algebraMap R K b * algebraMap R K (a⁻¹ : Rˣ) * hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (h₁ ▸ isIntegral_algebraMap)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (h₂ ▸ isIntegral_algebraMap)
  have hyz : y * z = 1 := IsFractionRing.injective R K (by rw [map_mul, hy, hz, Units.mul_inv, map_one])
  exact ⟨⟨y, z, hyz, (mul_comm z y).trans hyz⟩, hy⟩

private theorem appTop_nat {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (r : Γ(Spec (.of R), ⊤)) :
    (Scheme.ΓSpecIso (.of K)).hom.hom ((Spec.map (CommRingCat.ofHom φ)).appTop.hom r) =
      φ ((Scheme.ΓSpecIso (.of R)).hom.hom r) :=
  congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

private theorem appTop_inj {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (h : Function.Injective φ) :
    Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := fun a b e =>
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1
    (h ((appTop_nat φ a).symm.trans ((congrArg _ e).trans (appTop_nat φ b))))

private theorem unit_of_pow' {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Γ(Spec (.of K), ⊤)ˣ) {n : ℕ} (hn : 0 < n) (a b : Γ(Spec (.of R), ⊤)ˣ)
    (h : (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom a.val =
      x.val ^ n * (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom b.val) :
    ∃ y : Γ(Spec (.of R), ⊤)ˣ, (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom y.val = x.val := by
  have h' := congrArg (Scheme.ΓSpecIso (.of K)).hom.hom h
  rw [map_mul, map_pow, appTop_nat, appTop_nat] at h'
  obtain ⟨y, hy⟩ := unit_of_pow (R := R) (Units.map (Scheme.ΓSpecIso (.of K)).hom.hom.toMonoidHom x) hn
    (Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom a)
    (Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom b) h'
  refine ⟨Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom y, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).hom).1
  refine (appTop_nat _ _).trans (Eq.trans ?_ hy)
  exact congrArg (algebraMap R K) (congrArg (fun q => q.hom y.val) (Scheme.ΓSpecIso (.of R)).inv_hom_id)

private theorem exists_lift_units {M A B : Type} [Group M] [CommRing A] [CommRing B] (ρ : A →+* B)
    (hρ : Function.Injective ρ) (φ : M →* Bˣ) (h : ∀ m, ∃ y : Aˣ, ρ y.val = (φ m).val) :
    ∃ ψ : M →* Aˣ, ∀ m, ρ (ψ m).val = (φ m).val := by
  choose ψ hψ using h
  refine ⟨MonoidHom.mk' ψ fun a b => Units.ext (hρ ?_), hψ⟩
  rw [hψ, Units.val_mul, map_mul ρ, hψ, hψ, map_mul, Units.val_mul]

private theorem pigeon {S : Scheme.{0}} (G : Over S) [QuasiCompact G.hom] (P : G.left.Opens → Prop)
    (hP : ∀ x : G.left, ∃ V, x ∈ V ∧ P V) {R : Type} [CommRing R] [IsLocalRing R] (s : Spec (.of R) ⟶ S)
    (g : ℕ → (Spec (.of R) ⟶ G.left)) (hg : ∀ n, g n ≫ G.hom = s) :
    ∃ n m V, m < n ∧ P V ∧ ⊤ ≤ g n ⁻¹ᵁ V ∧ ⊤ ≤ g m ⁻¹ᵁ V := by
  choose V hV hPV using hP
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (s (IsLocalRing.closedPoint R))) isOpen_univ
  have hc : IsCompact ((G.hom ⁻¹ᵁ U : G.left.Opens) : Set G.left) :=
    QuasiCompact.isCompact_preimage _ U.isOpen hU.isCompact
  obtain ⟨F, -, hF⟩ := hc.elim_nhds_subcover (fun x => (V x : Set G.left))
    fun x _ => (V x).isOpen.mem_nhds (hV x)
  have : ∀ n, ∃ x : F, g n (IsLocalRing.closedPoint R) ∈ V x := fun n => by
    have : g n (IsLocalRing.closedPoint R) ∈ ((G.hom ⁻¹ᵁ U : G.left.Opens) : Set G.left) := by
      show (g n ≫ G.hom) (IsLocalRing.closedPoint R) ∈ U
      rw [hg]
      exact hsU
    obtain ⟨x, hx, h⟩ := Set.mem_iUnion₂.1 (hF this)
    exact ⟨⟨x, hx⟩, h⟩
  choose c hc using this
  obtain ⟨n, m, hnm, e⟩ := Finite.exists_ne_map_eq_of_infinite c
  have top : ∀ n, ⊤ ≤ g n ⁻¹ᵁ V (c n) := fun n =>
    (Scheme.preimage_eq_top_of_closedPoint_mem (g n) (hc n)).ge
  rcases lt_or_gt_of_ne hnm with h | h
  · exact ⟨m, n, _, h, hPV _, top m, e ▸ top n⟩
  · exact ⟨n, m, _, h, hPV _, top n, e ▸ top m⟩

private theorem appLE_comp {Y Z W : Scheme.{0}} (j : W ⟶ Z) (g : Z ⟶ Y) (g' : W ⟶ Y) (e : g' = j ≫ g) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g' ⁻¹ᵁ V) (f : Γ(Y, V)) :
    (g'.appLE V ⊤ h').hom f = j.appTop.hom ((g.appLE V ⊤ h).hom f) := by
  subst e
  have := Scheme.Hom.appLE_comp_appLE j g V ⊤ ⊤ h le_top
  rw [← this, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

private theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiCompact G.hom]
    {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) [IsMonHom u] (hu : GoodCover u)
    {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Spec (.of R) ⟶ S) (g : Over.mk s ⟶ G)
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s) ⟶ splitTorus S X)
    (j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s) ⟶ Over.mk s)
    (hj : j.left = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (w : t ≫ u = j ≫ g) : ∃ l : Over.mk s ⟶ splitTorus S X, j ≫ l = t := by
  obtain ⟨n, m, V, hmn, ⟨-, -, f, hf⟩, hn, hm⟩ :=
    pigeon G (GoodOpen u) hu s (fun n => (g ^ n).left) fun n => Over.w (g ^ n)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  have e : ((t ^ (d + 1)) ≫ u) * (j ≫ g ^ m) = j ≫ g ^ (m + d + 1) := by
    rw [MonObj.pow_comp, w, MonObj.comp_pow, MonObj.comp_pow, ← pow_add]
    congr 1
    omega
  have e₁ : (((t ^ (d + 1)) ≫ u) * (j ≫ g ^ m)).left = j.left ≫ (g ^ (m + d + 1)).left := by rw [e]; rfl
  have key : ∀ χ : Multiplicative X, ∃ y : Γ(Spec (.of R), ⊤)ˣ,
      (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom y.val =
        (splitTorusPointsEquiv S X _ t χ).val := fun χ => by
    have h₁ : ⊤ ≤ (((t ^ (d + 1)) ≫ u) * (j ≫ g ^ m)).left ⁻¹ᵁ V := by
      rw [e₁]
      exact fun x _ => hn (x := j.left x) trivial
    have h₂ : ⊤ ≤ (j ≫ g ^ m).left ⁻¹ᵁ V := fun x _ => hm (x := j.left x) trivial
    have h := hf χ.toAdd _ (t ^ (d + 1)) (j ≫ g ^ m) h₁ h₂
    rw [appLE_comp j.left _ _ e₁ V hn, appLE_comp j.left (g ^ m).left (j ≫ g ^ m).left rfl V hm,
      ← splitTorusPointsEquiv_val, map_pow, hj] at h
    exact unit_of_pow' _ d.succ_pos (Units.map ((g ^ (m + d + 1)).left.appLE V ⊤ hn).hom.toMonoidHom (f χ))
      (Units.map ((g ^ m).left.appLE V ⊤ hm).hom.toMonoidHom (f χ)) h
  obtain ⟨ψ, hψ⟩ := exists_lift_units _ (appTop_inj _ (IsFractionRing.injective R K)) _ key
  refine ⟨(splitTorusPointsEquiv S X (Over.mk s)).symm ψ, ?_⟩
  refine (splitTorusPointsEquiv S X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  refine (splitTorusPointsEquiv_val S X _ _ χ.toAdd).trans (Eq.trans ?_ (hψ χ))
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    ← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply, hj]
  rfl

theorem UpperTheory.split_torus_closed_immersion :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSeparated G.hom → QuasiCompact G.hom →
        ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G), IsMonHom u → Mono u → GoodCover u → IsClosedImmersion u.left := by
  intro S G _ hs hq X _ _ _ u hm hmono hu
  have hw : u.left ≫ G.hom = (splitTorus S X).hom := Over.w u
  have : Mono u.left := inferInstanceAs (Mono ((Over.forget S).map u))
  have : LocallyOfFiniteType (u.left ≫ G.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType u.left := locallyOfFiniteType_of_comp u.left G.hom
  have : QuasiCompact (u.left ≫ G.hom) := by rw [hw]; infer_instance
  have : QuasiCompact u.left := QuasiCompact.of_comp u.left G.hom
  have : UniversallyClosed u.left := by
    refine UniversallyClosed.of_valuativeCriterion u.left fun Q => ?_
    have w := Q.commSq.w
    obtain ⟨l, hl⟩ := exists_ext G u hu (R := Q.R) (K := Q.K) (Q.i₂ ≫ G.hom) (Over.homMk Q.i₂ rfl)
      (Over.homMk Q.i₁ (by rw [← hw, reassoc_of% w]; rfl)) (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap Q.R Q.K))) rfl) rfl
      (Over.OverMorphism.ext w)
    have e₁ : Spec.map (CommRingCat.ofHom (algebraMap Q.R Q.K)) ≫ l.left = Q.i₁ := congrArg (·.left) hl
    refine ⟨⟨l.left, e₁, ?_⟩⟩
    have hU := IsSeparated.valuativeCriterion G.hom
      { R := Q.R, K := Q.K, i₁ := Q.i₁ ≫ u.left, i₂ := Q.i₂ ≫ G.hom, commSq := ⟨by rw [w, Category.assoc]⟩ }
    exact congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hU
      ⟨l.left ≫ u.left, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ u.left) e₁),
        (Category.assoc _ _ _).trans ((congrArg (l.left ≫ ·) hw).trans (Over.w l))⟩
      ⟨Q.i₂, w.symm, rfl⟩)
  have : IsProper u.left := {}
  exact (IsClosedImmersion.iff_isProper_and_mono u.left).2 ⟨inferInstance, inferInstance⟩
