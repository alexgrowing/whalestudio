import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MulFinite

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem exists_pow_mul_eq_zero {k R : Type} [CommRing k] [CommRing R] (hk : IsField k) (φ : k →+* R)
    (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hk.toField
  obtain ⟨p, hp, h0⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h0
  rw [add_comm]
  exact h0

theorem isClosed_basicOpen {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by
  have hk : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ := exists_pow_mul_eq_zero hk _ a (isIntegral_appTop_of_universallyClosed f a)
  have : (Z.basicOpen a : Set Z) = (Z.basicOpen (c + a * b) : Set Z)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Z a z trivial, Scheme.mem_basicOpen Z (c + a * b) z trivial]
    let G : Γ(Z, ⊤) →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro h1 h2
      exact ((h1.pow m).mul h2).ne_zero e'
    · intro h2
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        have := hc.map G
        simpa using this
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact absurd h h2
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [this]
  exact (Z.basicOpen _).isOpen.isClosed_compl

theorem locallyQuasiFinite_of_cover {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [IsProper f] {I : Type} (a : I → Γ(Z, ⊤)) (hc : ⨆ i, Z.basicOpen (a i) = ⊤)
    (ha : ∀ i, IsAffineOpen (Z.basicOpen (a i))) : LocallyQuasiFinite f := by
  have : IsZariskiLocalAtSource @LocallyQuasiFinite.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite.{0}) _ hc fun i => ?_
  have : IsClosedImmersion (Z.basicOpen (a i)).ι :=
    .of_isPreimmersion _ (by simpa using isClosed_basicOpen f (a i))
  have : IsAffine (Z.basicOpen (a i)).toScheme := ha i
  have : IsFinite ((Z.basicOpen (a i)).ι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  infer_instance

theorem isAffineHom_fromSpecResidueField (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : y ∈ U
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_top _
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_bot _

theorem isUnit_gs {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem gs_appLE {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (V : Z.Opens) (hle : V ≤ r ⁻¹ᵁ U)
    (h : z ∈ V) (a : Γ(Y, U)) : gs (𝟙 Z) z V ((r.appLE U V hle).hom a) = gs r z U a :=
  (gs_res (𝟙 Z) z hle h _).trans ((gs_pull (𝟙 Z) r z U (hle h) a).trans (by rw [Category.id_comp]))

theorem gs_pow {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem pow_aux {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e N : ℕ) :
    ((g ^ N).val * x) ^ e * ((g ^ e * t)⁻¹).val ^ N = x ^ e * (t⁻¹).val ^ N := by
  have h : ((g ^ N) ^ e * ((g ^ e * t)⁻¹) ^ N) = (t⁻¹) ^ N := by
    rw [mul_inv, mul_pow, ← _root_.mul_assoc, inv_pow, ← pow_mul, ← pow_mul, _root_.mul_comm e N,
      mul_inv_cancel, _root_.one_mul]
  have h' : (g ^ N).val ^ e * ((g ^ e * t)⁻¹).val ^ N = (t⁻¹).val ^ N := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1])) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : L.ι) (h₀ : ∀ z, m (w (r z)) ∈ L.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => (r ≫ w) ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ (r ≫ w) ⁻¹ᵁ LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀] :=
    fun j z hz => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hz
      · exact h₀ z
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j)) ^ e *
        ((gm (r ≫ w) z (LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀]) (α.s ![j, j₀]))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) ^ e *
      ((r ≫ w).appLE _ _ (l₂ j)).hom ((α.s ![j, j₀])⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · refine congrArg (· ^ N) ((gs_appLE (r ≫ w) z _ _ _ hz _).trans ?_)
      exact (gs_unit (r ≫ w) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans hα (r ≫ w) z (l₂ j hz.1) (l₂ j' hz.2)]
      have h1 : gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) = 1 := gm_self hL _ z (h₀ z)
      have t₁ : trF (L := L) (K := Fin N) (fun _ => w) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1] (r ≫ w) z ![j, j₀] ![j', j₀] =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ e := by
        rw [trF, Fin.prod_univ_two]
        change gm ((r ≫ w) ≫ 𝟙 X) z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) *
          gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) ^ (-1 : ℤ) = _
        rw [h1, Category.comp_id]; simp
      rw [t₁, t₂]
      exact pow_aux _ _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => w) k := W.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_relAmple {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsProper A.hom] (L : LB A.left)
    (hL : L.IsLB) (hA : RelAmple A L) (m : A ⟶ A) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, m.left] ![(e : ℤ), -1])) (hα : α.IsGen) :
    IsFinite m.left := by
  have hm : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hm]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (A.hom y)) isOpen_univ
  obtain ⟨N, -, M, s, hcov, hs⟩ := hA U hU
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let r : m.left.fiber y ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι (m.left.fiberι y) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change A.hom (m.left.fiberι y z) ∈ U
      rw [← hm, Scheme.Hom.comp_apply, hy]
      exact hyU)
  have hr : r ≫ (A.hom ⁻¹ᵁ U).ι = m.left.fiberι y := IsOpenImmersion.lift_fac _ _ _
  have := isAffineHom_fromSpecResidueField A.left y
  have : IsAffineHom (r ≫ (A.hom ⁻¹ᵁ U).ι) := by
    rw [hr]; exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsAffineHom r := .of_comp r (A.hom ⁻¹ᵁ U).ι
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  have key := fun i => exists_fn L hL (A.hom ⁻¹ᵁ U).ι N (s i) m.left e he α hα r j₀ (fun z => by
    rw [← Scheme.Hom.comp_apply r, hr, hy]; exact hj₀)
  choose a ha using key
  have : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y) (m.left.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => r ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage r

theorem isFinite_mulA :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → PolBaseChangeSt → (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left := by
  intro h _ _ S P n hn
  have H := h S P n
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have := P.isAb.proper
  exact isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα

end GlobalTheory.MulFinite
