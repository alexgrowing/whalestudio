import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.CubeGen

section Field

variable {F : Type} [Field F] {X : Scheme.{0}}

theorem toStk_surjective (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

def ev (z : Sp F) : (Sp F).presheaf.stalk z ≃+* F :=
  (RingEquiv.ofBijective (toStk z) ⟨(toStk z).injective, toStk_surjective z⟩).symm

theorem ev_gs (x : Sp F ⟶ X) (z : Sp F) {U : X.Opens} (h : x z ∈ U) (f : Γ(X, U)) :
    ev z (gs x z U f) = valF x U f := by
  refine (RingEquiv.symm_apply_eq _).2 ?_
  have h' := (top_le_iff_mem x U z).2 h
  rw [valF, dif_pos h', gs_eq x z U h]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _))
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') z trivial _).symm

theorem ev_gm (x : Sp F ⟶ X) (z : Sp F) {U : X.Opens} (h : x z ∈ U) (f : Γ(X, U)ˣ) :
    ev z (gm x z U f).val = valF x U f.val := by
  rw [← gs_unit x z U h, ev_gs x z h]

theorem range_subset_iff (x : Sp F ⟶ X) (z : Sp F) (U : Set X) : Set.range x ⊆ U ↔ x z ∈ U := by
  refine ⟨fun h => h ⟨z, rfl⟩, fun h => ?_⟩
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum F) y z]

end Field

section Sections

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Z.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem gs_sec (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {i j : L.ι} (hi : r z ∈ L.U i) (hj : r z ∈ L.U j) :
    gs r z _ (θ.f i) = (gm r z _ (L.g i j)).val * gs r z _ (θ.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (θ.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

theorem mem_nonzeroLocus_iff (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {k : L.ι}
    (hk : r z ∈ L.U k) : r z ∈ Out.nonzeroLocus θ ↔ IsUnit (gs r z _ (θ.f k)) := by
  rw [isUnit_gs_iff r z _ hk]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨k, h⟩⟩
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ L.U j := X.basicOpen_le _ hj
  rw [← isUnit_gs_iff r z _ hk, gs_sec θ r z hk hj']
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj' _).2 hj)

theorem exists_gen_of_sec (θ : LB.Sec L) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : ∀ k y, φ k y ∈ Out.nonzeroLocus θ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      ∃ u : K → (Z.presheaf.stalk z)ˣ, (∀ k, (u k).val = gs (r ≫ φ k) z _ (θ.f (J (r ≫ φ k)))) ∧
        val t r z J = ∏ k, u k ^ ε k := by
  let f : ∀ (j : K → L.ι) (k : K), Γ(Y, LB.wchart L φ j) := fun j k =>
    (Y.presheaf.map (homOfLE (LB.wchart_le L φ j k)).op).hom (((φ k).app _).hom (θ.f (j k)))
  have hf : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, r z ∈ LB.wchart L φ j →
      gs r z _ (f j k) = gs (r ≫ φ k) z _ (θ.f (j k)) := fun Z r z j k hz =>
    (gs_res r z _ hz _).trans (gs_pull r (φ k) z _ (LB.wchart_le L φ j k hz) _)
  have hu : ∀ j k, IsUnit (f j k) := fun j k => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hf _ (𝟙 Y) y j k hy
    have := (mem_nonzeroLocus_iff θ (𝟙 Y ≫ φ k) y (LB.wchart_le L φ j k hy)).1 (h k y)
    rw [← e, gs_eq _ y _ hy] at this
    exact this
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, r z ∈ LB.wchart L φ j →
      (gm r z _ (hu j k).unit).val = gs (r ≫ φ k) z _ (θ.f (j k)) := fun Z r z j k hz =>
    (gs_unit r z _ hz _).symm.trans (hf Z r z j k hz)
  have hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j,
      gm r z (LB.wchart L φ j) (∏ k, (hu j k).unit ^ ε k) = ∏ k, gm r z _ (hu j k).unit ^ ε k := fun Z r z j => by
    simp only [map_prod, map_zpow]
  refine ⟨⟨fun j => ∏ k, (hu j k).unit ^ ε k⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J hJ =>
    ⟨fun k => gm r z _ (hu (fun k => J (r ≫ φ k)) k).unit, fun k => hv Z r z _ k (hJ.mem φ r), hp Z r z _⟩⟩
  refine ((gm_res _ y _ hy _).trans (hp _ _ y j)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hp _ _ y j'))).trans ?_)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  congr 1
  apply Units.ext
  rw [Units.val_mul, hv _ (𝟙 Y) y j k hy.1, hv _ (𝟙 Y) y j' k hy.2]
  exact (gs_sec θ _ y (LB.wchart_le L φ j k hy.1) (LB.wchart_le L φ j' k hy.2)).symm

end Sections

section Norms

variable {X Y Y' : Scheme.{0}} {L : LB X} {ν : Nrm L} {p : ℕ} [Fact p.Prime] {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {z : Sp (PadicAlgCl p)} {J : (Sp (PadicAlgCl p) ⟶ X) → L.ι}

def nv (ν : Nrm L) (t : LB.Gen (LB.LinComb L φ ε)) (q : Sp (PadicAlgCl p) ⟶ Y) (z : Sp (PadicAlgCl p))
    (J : (Sp (PadicAlgCl p) ⟶ X) → L.ι) : ℝ :=
  ‖ev z (val t q z J).val‖ * ∏ k, ν p (q ≫ φ k) (J (q ≫ φ k)) ^ ε k

theorem norm_ev_prod (u : K → ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ) :
    ‖ev z (∏ k, u k ^ ε k).val‖ = ∏ k, ‖ev z (u k).val‖ ^ ε k := by
  have e : ∀ v : ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ,
      ev z v.val = (Units.map (ev z).toMonoidHom v).val := fun _ => rfl
  rw [e, map_prod, Units.coe_prod, norm_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow, e]

theorem normOne_iff (hν : IsNrm L ν) (hJ : Good L z J) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (q : Sp (PadicAlgCl p) ⟶ Y) : NormOne ν t q ↔ nv ν t q z J = 1 := by
  have hm := hJ.mem φ q
  refine ⟨fun h => ?_, fun h j hj => ?_⟩
  · exact (congrArg (fun a => ‖a‖ * _) (ev_gm q z hm _)).trans (h _ ((range_subset_iff q z _).2 hm))
  · have hj' : q z ∈ LB.wchart L φ j := (range_subset_iff q z _).1 hj
    refine Eq.trans ?_ h
    have e : gm q z (LB.wchart L φ j) (t.s j) = _ * val t q z J := gen_trans ht q z hj' hm
    refine (congrArg (fun a => ‖a‖ * _) ((ev_gm q z hj' _).symm.trans (congrArg (fun a => ev z a.val) e))).trans ?_
    rw [nv, Units.val_mul, map_mul, norm_mul, trF, norm_ev_prod, mul_right_comm,
      mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have a : (q ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 hj' k
    have b := hJ (q ≫ φ k)
    rw [← mul_zpow, ev_gm (q ≫ φ k) z (U := L.U (j k) ⊓ L.U (J (q ≫ φ k))) ⟨a, b⟩,
      hν.trans p _ _ _ ((range_subset_iff _ z _).2 a) ((range_subset_iff _ z _).2 b)]

theorem nv_mul (hJ : Good L z J) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (q : Sp (PadicAlgCl p) ⟶ Y) : nv ν (LB.mulGen L φ ε φ' ε' t t') q z J = nv ν t q z J * nv ν t' q z J := by
  rw [nv, val_mul hJ, Units.val_mul, map_mul, norm_mul, Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
  rfl

theorem nv_pull (hJ : Good L z J) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (q : Sp (PadicAlgCl p) ⟶ Y') : nv ν (LB.pullGen L φ ε t h) q z J = nv ν t (q ≫ h) z J := by
  rw [nv, val_pull hJ, nv]
  simp only [Category.assoc]

theorem nv_form (hν : IsNrm L ν) (h : FormEq φ ε φ' ε') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Sp (PadicAlgCl p) ⟶ Y) (e : val t' q z J = val t q z J) :
    nv ν t' q z J = nv ν t q z J := by
  have := congrArg Units.val (h ℝˣ fun ψ => Units.mk0 (ν p (q ≫ ψ) (J (q ≫ ψ))) (hν.pos p _ _).ne')
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
  rw [nv, nv, e, this]

end Norms

section Cube

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']

def six {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (x b c : T ⟶ G) : Fin 6 → (T ⟶ G) :=
  ![x * b, x * c, b * c, x * b * c, b, c]

theorem six_map {T : Over S} {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) (x b c : T' ⟶ G') (i : Fin 6) :
    ρ (six x b c i) = six (ρ x) (ρ b) (ρ c) i := by
  fin_cases i <;> simp [six]

theorem six_comp {T T' : Over S} (r : T'.left ⟶ T.left) (x b c : T ⟶ G) (x' b' c' : T' ⟶ G)
    (hx : x'.left = r ≫ x.left) (hb : b'.left = r ≫ b.left) (hc : c'.left = r ≫ c.left) (i : Fin 6) :
    (six x' b' c' i).left = r ≫ (six x b c i).left := by
  let ρ : T' ⟶ T := Over.homMk r (by rw [← Over.w x, ← Category.assoc, ← hx, Over.w])
  have e := six_map (preHom (G := G) ρ) x b c i
  rw [show preHom ρ x = x' from Over.OverMorphism.ext hx.symm, show preHom ρ b = b' from Over.OverMorphism.ext hb.symm,
    show preHom ρ c = c' from Over.OverMorphism.ext hc.symm] at e
  rw [← e]
  rfl

theorem six_push {f : S' ⟶ S} {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S} {T' : Over S'}
    (r : T'.left ⟶ T.left) (x b c : T ⟶ G) (x' b' c' : T' ⟶ G')
    (hx : x'.left ≫ a = r ≫ x.left) (hb : b'.left ≫ a = r ≫ b.left) (hc : c'.left ≫ a = r ≫ c.left) (i : Fin 6) :
    (six x' b' c' i).left ≫ a = r ≫ (six x b c i).left :=
  (congrArg (fun q => q.left) (six_map (pushHom h T') x' b' c' i)).trans
    (six_comp (T' := Over.mk (T'.hom ≫ f)) r x b c _ _ _ hx hb hc i)

theorem exists_gen_cube (L : RigLB G) (cub : CubicalStr G L) (θ : LB.Sec L.L) {T : Over S} (x b c : T ⟶ G)
    (h : ∀ i y, (six x b c i).left y ∈ Out.nonzeroLocus θ) :
    ∃ g : LB.Gen (L.L.pull x.left), g.IsGen ∧ ∀ ν : Nrm L.L, IsNrm L.L ν → ∀ (p : ℕ) [Fact p.Prime]
      (q : Sp (PadicAlgCl p) ⟶ T.left) (δ : ℝ), 0 < δ → NormOne ν L.rig (q ≫ T.hom) →
      NormOne (φ := thφ G (x3 G)) (ε := thε) ν cub.t (q ≫ (lift x (lift b c)).left) →
      (∀ i j, Set.range (q ≫ (six x b c i).left) ⊆ L.L.U j →
        ‖valF (q ≫ (six x b c i).left) _ (θ.f j)‖ * ν p (q ≫ (six x b c i).left) j = δ) → NormOne ν g q := by
  obtain ⟨t, ht, hv⟩ := exists_gen_of_sec θ (fun i => (six x b c i).left) ![1, 1, 1, -1, -1, -1] h
  let t₁ := LB.pullGen L.L (thφ G (x3 G)) thε cub.t (lift x (lift b c)).left
  let t₂ := LB.pullGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig T.hom
  have e0 : T.hom ≫ eSec G = (1 : T ⟶ G).left := by
    show _ = (toUnit _ ≫ η[G]).left
    simp [eSec]
  have F : FormEq (Sum.elim (Sum.elim (fun k => (lift x (lift b c)).left ≫ thφ G (x3 G) k)
      (fun i => (six x b c i).left)) (fun _ : PUnit => T.hom ≫ eSec G))
      (Sum.elim (Sum.elim thε ![1, 1, 1, -1, -1, -1]) (fun _ => 1)) (fun _ : PUnit => x.left) (fun _ => 1) := by
    intro U _ f
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_cub x b c f, e0]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, six, ofMul_mul, ofMul_inv]
    abel
  obtain ⟨g, hg, hgv⟩ := exists_gen L.isLB F (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t₁ t) t₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cub.isGen _) ht)
      (DVR.pullGen_isGen _ _ _ _ L.rigGen _))
  refine ⟨g, hg, fun ν hν p _ q δ hδ hr hc hθ => ?_⟩
  let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  choose J hJ using fun χ : Sp (PadicAlgCl p) ⟶ G.left => exists_chart L.isLB (χ z)
  have hJ' : Good L.L z J := hJ
  have n₁ : nv ν t₁ q z J = 1 := (nv_pull hJ' _ _ _).trans ((normOne_iff hν hJ' cub.isGen _).1 hc)
  have n₂ : nv ν t₂ q z J = 1 := (nv_pull hJ' _ _ _).trans ((normOne_iff hν hJ' L.rigGen _).1 hr)
  have n₃ : nv ν t q z J = 1 := by
    obtain ⟨u, hu, e⟩ := hv _ q z J hJ'
    have a : ∀ i, ‖ev z (u i).val‖ * ν p (q ≫ (six x b c i).left) (J (q ≫ (six x b c i).left)) = δ := fun i => by
      rw [hu i, ev_gs _ z (hJ _)]
      exact hθ i _ ((range_subset_iff _ z _).2 (hJ _))
    rw [nv, e, norm_ev_prod, ← Finset.prod_mul_distrib]
    simp only [← mul_zpow, a]
    simp [Fin.prod_univ_succ]
    field_simp
  refine (normOne_iff hν hJ' hg q).2 ((nv_form hν F q (hgv _ q z J hJ')).trans ((nv_mul hJ' _ _ q).trans ?_))
  exact (congrArg₂ (· * ·) ((nv_mul hJ' t₁ t q).trans ((congrArg₂ (· * ·) n₁ n₃).trans (_root_.mul_one _))) n₂).trans
    (_root_.mul_one _)

end Cube

section Geometry

theorem exists_fac_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {Y : Scheme.{0}} (β : Sp R ⟶ Y) (V : Y.Opens)
    (h : β (IsLocalRing.closedPoint R) ∈ V) : ∃ β' : Sp R ⟶ V.toScheme, β' ≫ V.ι = β := by
  refine ⟨IsOpenImmersion.lift V.ι β ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : β ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp h
  exact (this.ge (Set.mem_univ x) : x ∈ β ⁻¹ᵁ V)

theorem exists_fac {Z Y Y' : Scheme.{0}} (β : Z ⟶ Y) (i : Y' ⟶ Y) [IsOpenImmersion i]
    (h : Set.range β ⊆ Set.range i) : ∃ β' : Z ⟶ Y', β' ≫ i = β :=
  ⟨IsOpenImmersion.lift i β h, IsOpenImmersion.lift_fac _ _ _⟩

def preInter {X Y : Scheme.{0}} {K : Type} [Finite K] (φ : K → (Y ⟶ X)) (O : Set X) (hO : IsOpen O) : Y.Opens :=
  ⟨⋂ k, φ k ⁻¹' O, isOpen_iInter_of_finite fun k => hO.preimage (φ k).continuous⟩

theorem mem_preInter {X Y : Scheme.{0}} {K : Type} [Finite K] {φ : K → (Y ⟶ X)} {O : Set X} {hO : IsOpen O} {y : Y} :
    y ∈ preInter φ O hO ↔ ∀ k, φ k y ∈ O := Set.mem_iInter

theorem intAt_mono {X Y : Scheme.{0}} {a : X ⟶ Y} {W : Set Y} {p : ℕ} [Fact p.Prime]
    {x : Sp (PadicAlgCl p) ⟶ X} (h : IntAt a W x) : IntAt a Set.univ x :=
  let ⟨b, hb, _⟩ := h; ⟨b, hb, trivial⟩

end Geometry

end GlobalTheory.ZJ.CubeGen

namespace GlobalTheory.ZJ

open CubeGen

theorem Core.exists_gen_normOne : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (W₀ : C.A.left.Opens) (gen₀ : LB.Gen (T.L.L.pull W₀.ι)), w ∈ W ∧ (W₀ : Set C.A.left).Nonempty ∧ gen₀.IsGen ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ C.a) W x → NormOne ν gen₀ x) := by
  intro C L T Om ν hOm hN h6 w hw
  letI := L.grp
  haveI := L.comm
  haveI := C.isOpenImmersion_a
  obtain ⟨N, b, c, K, _, t, x', b', c', hx', hb', hc', hsix⟩ := h6 w hw

  let X : C.G.toScheme.Opens := C.GG.hom ⁻¹ᵁ N
  let n : X.toScheme ⟶ N.toScheme := C.GG.hom ∣_ N
  have hn : n ≫ N.ι = X.ι ≫ C.GG.hom := morphismRestrict_ι _ _
  let TG : Over C.Z := Over.mk (X.ι ≫ C.GG.hom)
  let m : TG ⟶ Over.mk N.ι := Over.homMk n hn
  let xG : TG ⟶ C.GG := Over.homMk X.ι rfl
  let V : Fin 6 → (X.toScheme ⟶ C.G.toScheme) := fun i => (six xG (m ≫ b) (m ≫ c) i).left
  let W' : X.toScheme.Opens := preInter V Om hOm
  have hwW : w ∈ X.ι ''ᵁ W' := by
    let s : Sp K := IsLocalRing.closedPoint K
    have hs : x'.left s = w := by
      have : x'.left s ∈ Set.range x'.left := ⟨s, rfl⟩
      rwa [hx'] at this
    have hw' : x'.left ≫ C.GG.hom = t ≫ N.ι := Over.w x'
    obtain ⟨r, hr⟩ := exists_fac_of_closedPoint x'.left X (by
      change (x'.left ≫ C.GG.hom) s ∈ N
      rw [hw']
      exact (t s).2)
    have hrn : r ≫ n = t := by
      rw [← cancel_mono N.ι, Category.assoc, hn, ← Category.assoc, hr, hw']
    refine ⟨r s, mem_preInter.2 fun i => ?_, (congrArg (fun q => q s) hr).trans hs⟩
    have e := six_comp (T := TG) (T' := Over.mk (t ≫ N.ι)) r xG (m ≫ b) (m ≫ c) x' b' c' hr.symm
      (hb'.trans (by rw [← hrn]; exact Category.assoc _ _ _)) (hc'.trans (by rw [← hrn]; exact Category.assoc _ _ _)) i
    have : (six x' b' c' i).left s ∈ Om := hsix _ (by fin_cases i <;> simp [six]) ⟨s, rfl⟩
    rw [e] at this
    exact this

  let XA : C.A.left.Opens := C.a ⁻¹ᵁ X
  let ρ : XA.toScheme ⟶ X.toScheme := C.a ∣_ X
  have hρ : ρ ≫ X.ι = XA.ι ≫ C.a := morphismRestrict_ι _ _
  let TA : Over C.U.toScheme := Over.mk (XA.ι ≫ C.A.hom)
  let xA : TA ⟶ C.A := Over.homMk XA.ι rfl
  have lft : ∀ d : TG ⟶ C.GG, ∃ d' : TA ⟶ C.A, d'.left ≫ C.a = ρ ≫ d.left := fun d => by
    have sq : (ρ ≫ d.left) ≫ C.GG.hom = (XA.ι ≫ C.A.hom) ≫ C.U.ι := by
      rw [Category.assoc, Over.w d, Category.assoc, ← C.isPullback_a.w]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.GG.hom) hρ).trans (Category.assoc _ _ _))
    exact ⟨Over.homMk (C.isPullback_a.lift _ _ sq) (C.isPullback_a.lift_snd _ _ _), C.isPullback_a.lift_fst _ _ _⟩
  obtain ⟨bA, hbA⟩ := lft (m ≫ b)
  obtain ⟨cA, hcA⟩ := lft (m ≫ c)
  let VA : Fin 6 → (XA.toScheme ⟶ C.A.left) := fun i => (six xA bA cA i).left
  have hVA : ∀ i, VA i ≫ C.a = ρ ≫ V i := fun i =>
    six_push L.pull (T := TG) (T' := TA) ρ xG (m ≫ b) (m ≫ c) xA bA cA hρ.symm hbA hcA i
  have hVs : ∀ i, VA i ≫ C.A.hom = XA.ι ≫ C.A.hom := fun i => Over.w (six xA bA cA i)

  have key : ∀ (p : ℕ) [Fact p.Prime] (q : Sp (PadicAlgCl p) ⟶ XA.toScheme), IntAt (XA.ι ≫ C.a) (X.ι ''ᵁ W') q →
      (∀ i, IntAt C.a Om (q ≫ VA i)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i j, Set.range (q ≫ VA i) ⊆ T.L.L.U j →
        ‖valF (q ≫ VA i) _ (T.θ.f j)‖ * ν p (q ≫ VA i) j = δ := by
    intro p _ q ⟨β, hβ, y, hy, hyβ⟩
    obtain ⟨β', rfl⟩ := exists_fac_of_closedPoint β X (hyβ ▸ y.2)
    have e₁ : gPt p ≫ β' = q ≫ ρ := by
      rw [← cancel_mono X.ι, Category.assoc, hβ, Category.assoc, hρ]
    have e₂ : β' (cPt p) = y := X.ι.injective hyβ.symm
    have I : ∀ i, IntAt C.a Om (q ≫ VA i) := fun i => ⟨β' ≫ V i, by
      rw [← Category.assoc, e₁, Category.assoc, Category.assoc, hVA], by
      have := mem_preInter.1 hy i
      rwa [← e₂] at this⟩
    obtain ⟨δ, hδ, H⟩ := hN.theta p (q ≫ XA.ι ≫ C.A.hom)
    exact ⟨I, δ, hδ, fun i j hj => (H _ j (by rw [Category.assoc, hVs]) hj (intAt_mono (I i))).2.2 (I i)⟩
  let W₁ : XA.toScheme.Opens := preInter VA (Out.nonzeroLocus T.θ) (Out.nonzeroLocus T.θ).isOpen
  let W₀ : C.A.left.Opens := XA.ι ''ᵁ W₁
  have hne : (W₀ : Set C.A.left).Nonempty := by
    haveI := C.isIntegral_G
    obtain ⟨-, h₂, -, -, h₅, -⟩ := core_basic C
    haveI := C.lft
    obtain ⟨a₀⟩ := C.nonempty_A
    obtain ⟨p, _, β, hβ, hU⟩ := padicAlgCl_integral_points.1 C.G.toScheme (C.GG.hom ≫ C.π) w hw
      C.a.opensRange ⟨_, a₀, rfl⟩
    obtain ⟨q', hq'⟩ := exists_fac (gPt p ≫ β) C.a hU
    have hwX : w ∈ X := by
      obtain ⟨y, -, rfl⟩ := hwW
      exact y.2
    obtain ⟨β', hβ'⟩ := exists_fac_of_closedPoint β X (hβ ▸ hwX)
    let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    obtain ⟨q, rfl⟩ := exists_fac_of_closedPoint q' XA (by
      change (q' ≫ C.a) z ∈ X
      rw [hq', ← hβ']
      exact (β' (gPt p z)).2)
    obtain ⟨-, δ, hδ, H⟩ := key p q ⟨β, by rw [← hq', Category.assoc], hβ ▸ hwW⟩
    refine ⟨_, q z, mem_preInter.2 fun i => ?_, rfl⟩
    obtain ⟨j, hj⟩ := exists_chart T.L.isLB ((q ≫ VA i) z)
    have e := H i j ((range_subset_iff _ z _).2 hj)
    refine (mem_nonzeroLocus_iff T.θ (q ≫ VA i) z hj).2 ?_
    have h0 : ev z (gs (q ≫ VA i) z _ (T.θ.f j)) ≠ 0 := fun h0 => by
      rw [← ev_gs _ z hj, h0, norm_zero, zero_mul] at e
      exact hδ.ne e
    simpa using (IsUnit.mk0 _ h0).map (ev z).symm
  obtain ⟨k, hk⟩ := exists_fac W₀.ι XA.ι (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', -, e⟩ := y.2
    exact ⟨y', e⟩)
  have hk₁ : ∀ y, k y ∈ W₁ := fun y => by
    obtain ⟨y', h, e⟩ := y.2
    have : k y = y' := XA.ι.injective ((congrArg (fun q => q y) hk).trans e.symm)
    exact this ▸ h
  let T₀ : Over C.U.toScheme := Over.mk (W₀.ι ≫ C.A.hom)
  let κ : T₀ ⟶ TA := Over.homMk k ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.A.hom) hk))
  let x₀ : T₀ ⟶ C.A := Over.homMk W₀.ι rfl
  have h₀ : ∀ i, (six x₀ (κ ≫ bA) (κ ≫ cA) i).left = k ≫ VA i := fun i =>
    six_comp (T := TA) (T' := T₀) k xA bA cA _ _ _ hk.symm rfl rfl i
  obtain ⟨g, hg, H⟩ := exists_gen_cube T.L T.cub T.θ x₀ (κ ≫ bA) (κ ≫ cA) fun i y => by
    rw [h₀]
    exact mem_preInter.1 (hk₁ y) i
  refine ⟨X.ι ''ᵁ W', W₀, g, hwW, hne, hg, fun p _ q hq => ?_⟩
  obtain ⟨β, hβ, hβW⟩ := hq
  obtain ⟨I, δ, hδ, Hδ⟩ := key p (q ≫ k) ⟨β, by rw [hβ, ← hk]; simp only [Category.assoc], hβW⟩
  refine H ν hN.isNrm p q δ hδ (hN.rig p _ ⟨β ≫ C.GG.hom, ?_, trivial⟩) (hN.cube p _ fun i => ?_) fun i j hj => ?_
  · rw [← Category.assoc, hβ]
    simp only [Category.assoc]
    rw [C.isPullback_a.w]
    exact (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _)
  · have e : ∀ i, (q ≫ (lift x₀ (lift (κ ≫ bA) (κ ≫ cA))).left) ≫ (x3 C.A i).left =
        q ≫ (![x₀, κ ≫ bA, κ ≫ cA] i).left := fun i => by
      rw [Category.assoc, ← Over.comp_left]
      fin_cases i <;> simp [x3]
    rw [e]
    fin_cases i
    · exact ⟨β, hβ.trans (Category.assoc _ _ _).symm, trivial⟩
    · have := intAt_mono (I 4)
      rw [Category.assoc] at this
      exact this
    · have := intAt_mono (I 5)
      rw [Category.assoc] at this
      exact this
  · rw [h₀] at hj ⊢
    rw [← Category.assoc] at hj ⊢
    exact Hδ i j hj

end GlobalTheory.ZJ

end
