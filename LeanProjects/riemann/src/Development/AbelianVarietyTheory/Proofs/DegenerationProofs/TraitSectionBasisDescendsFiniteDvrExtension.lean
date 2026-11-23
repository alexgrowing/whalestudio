import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMoveMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OneBasis.TraitDescent

open GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise TopologicalSpace

section Algebra

variable {W K W' K' M₀ M₁ M₀' M₁' : Type} [CommRing W] [CommRing K] [CommRing W'] [CommRing K']
  [AddCommGroup M₀] [Module W M₀] [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₀'] [Module W' M₀']
  [AddCommGroup M₁'] [Module K' M₁'] {io : W →+* W'} {a : W →+* K} {a' : W' →+* K'} {io' : K →+* K'}

theorem exists_basis_of_square (p : M₀ →ₛₗ[io] M₀') (j : M₀ →ₛₗ[a] M₁) (q : M₁ →ₛₗ[io'] M₁') (j' : M₀' →ₛₗ[a'] M₁')
    (hr : ∀ y, io' (a y) = a' (io y)) (hio : Function.Injective io) (comm : ∀ x, j' (p x) = q (j x))
    (hj' : Function.Injective j') {m : ℕ} (β : Fin m → W') (u v : Fin m → W) (hu : ∑ k, io (u k) * β k = 1)
    (huv : ∑ k, v k * u k = 1) (hβ : ∀ y, ∃ c : Fin m → W, y = ∑ k, io (c k) * β k)
    (span : ∀ t, ∃ d : Fin m → M₀, t = ∑ k, β k • p (d k))
    (indp : ∀ d : Fin m → M₀, ∑ k, β k • p (d k) = 0 → ∀ k, d k = 0)
    (indq : ∀ d : Fin m → M₁, ∑ k, a' (β k) • q (d k) = 0 → ∀ k, d k = 0)
    {n : ℕ} (b' : Fin n → M₀') (s : Fin n → M₁) (hs : ∀ i, j' (b' i) = q (s i))
    (hb : ∀ t, ∃! c : Fin n → W', t = ∑ i, c i • b' i) :
    ∃ b : Fin n → M₀, (∀ i, j (b i) = s i) ∧ ∀ t, ∃! c : Fin n → W, t = ∑ i, c i • b i := by
  choose d hd using fun i => span (b' i)
  have h₁ : ∀ i k, j (d i k) = a (u k) • s i := fun i k => by
    refine sub_eq_zero.1 (indq (fun k => j (d i k) - a (u k) • s i) ?_ k)
    have e : ∑ k, a' (β k) • q (a (u k) • s i) = q (s i) := by
      simp only [map_smulₛₗ, smul_smul, hr, ← map_mul, mul_comm (β _)]
      rw [← Finset.sum_smul, ← map_sum, hu, map_one, one_smul]
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, e]
    rw [← hs, hd i, map_sum, sub_eq_zero]
    simp only [map_smulₛₗ, comm]
  have h₂ : ∀ i, j (∑ k, v k • d i k) = s i := fun i => by
    simp only [map_sum, map_smulₛₗ, h₁, smul_smul, ← map_mul]
    rw [← Finset.sum_smul, ← map_sum, huv, map_one, one_smul]
  obtain ⟨b, h₂⟩ : ∃ b : Fin n → M₀, ∀ i, j (b i) = s i := ⟨_, h₂⟩
  have h₃ : ∀ i, p (b i) = b' i := fun i => hj' (by rw [comm, h₂, hs])
  refine ⟨b, h₂, fun t => ?_⟩
  obtain ⟨c', hc', hun⟩ := hb (p t)
  have up : ∀ c : Fin n → W, t = ∑ i, c i • b i → (fun i => io (c i)) = c' := fun c hc => hun _ (by
    rw [hc, map_sum]; simp only [map_smulₛₗ, h₃])
  refine existsUnique_of_exists_of_unique ?_ fun c₁ c₂ e₁ e₂ =>
    funext fun i => hio (congrFun ((up _ e₁).trans (up _ e₂).symm) i)
  choose c hc using fun i => hβ (c' i)
  have h₄ : ∀ k, u k • t = ∑ i, c i k • b i := fun k => by
    refine sub_eq_zero.1 (indp (fun k => u k • t - ∑ i, c i k • b i) ?_ k)
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, map_sum, map_smulₛₗ, smul_smul, Finset.smul_sum, h₃,
      mul_comm (β _)]
    rw [← Finset.sum_smul, hu, one_smul, Finset.sum_comm, hc', sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_smul, ← hc]
  refine ⟨fun i => ∑ k, v k * c i k, ?_⟩
  simp only [Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, ← h₄]
  simp only [smul_smul]
  rw [← Finset.sum_smul, huv, one_smul]

theorem exists_basis_dvr {W W' : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W']
    (io : W →+* W') (hio : Function.Injective io) (hf : io.Finite) :
    ∃ (m : ℕ) (β : Fin m → W') (u v : Fin m → W), ∑ k, io (u k) * β k = 1 ∧ ∑ k, v k * u k = 1 ∧
      (∀ y, ∃ c : Fin m → W, y = ∑ k, io (c k) * β k) ∧
      ∀ c : Fin m → W, ∑ k, io (c k) * β k = 0 → ∀ k, c k = 0 := by
  classical
  let := io.toAlgebra
  have : Module.Finite W W' := hf
  have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
  let e := Module.finBasis W W'
  have hs : ∀ y, y = ∑ k, io (e.repr y k) * e k := fun y => (e.sum_repr y).symm
  have hk : ∃ k, IsUnit (e.repr 1 k) := by
    by_contra h
    push_neg at h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hd : ∀ k, ϖ ∣ e.repr 1 k := fun k => by
      rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]; exact h k
    have h1 : io ϖ ∣ 1 := by
      rw [hs 1]; exact Finset.dvd_sum fun k _ => (map_dvd io (hd k)).mul_right _
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap W W') ϖ).1 (isUnit_of_dvd_one h1))
  obtain ⟨k₀, w, hw⟩ := hk
  refine ⟨_, e, fun k => e.repr 1 k, Pi.single k₀ w.inv, (hs 1).symm, ?_, fun y => ⟨_, hs y⟩,
    fun c hc => Fintype.linearIndependent_iff.1 e.linearIndependent c hc⟩
  rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul]) (by simp), Pi.single_eq_same]
  exact (congrArg _ hw.symm).trans w.inv_val

end Algebra

section Flat

variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) {n : ℕ} (c : Fin n → F)

theorem gs_sub' {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a b : Γ(Y, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_comb {U : Y.Opens} (a : Fin n → FnOver π U) (y : Y') (hy : p y ∈ U) :
    gs (𝟙 Y') y (p ⁻¹ᵁ U) (∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) : FnOver π' _) =
      ∑ i, constVal π' y (c i) * gs p y U (a i) := by
  refine ((gs_eq (𝟙 Y') y (p ⁻¹ᵁ U) hy _).trans (by erw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
    (gs_eq (𝟙 Y') y (p ⁻¹ᵁ U) hy _).symm.trans ((gs_smul π' (𝟙 Y') y (p ⁻¹ᵁ U) hy _ _).trans ?_))
  rw [gs_pullFn H.w _ _ _ y hy, Category.id_comp, Category.id_comp]

theorem fn_span {U : Y.Opens} (hU : IsAffineOpen U) (hc : ∀ y, ∃ a : Fin n → S, y = ∑ i, fS (a i) * c i)
    (t : FnOver π' (p ⁻¹ᵁ U)) : ∃ a : Fin n → FnOver π U, t = ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have e : ∀ x, pullFn H.w (le_refl (p ⁻¹ᵁ U)) x = algebraMap (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) x := fun x => by
    show (Y'.presheaf.map (𝟙 _)).hom _ = _
    rw [CategoryTheory.Functor.map_id]; rfl
  simp only [e, Algebra.smul_def]
  induction t using hpo.out.inductionOn with
  | zero => exact ⟨0, by simp⟩
  | tmul y =>
    obtain ⟨a, rfl⟩ := hc y
    refine ⟨fun i => algebraMap S _ (a i), ?_⟩
    show algebraMap F _ _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, mul_comm, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S F]; rfl
  | smul r y hy =>
    obtain ⟨a, rfl⟩ := hy
    refine ⟨fun i => r * a i, ?_⟩
    rw [Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_left_comm]
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]⟩

variable [Flat π] (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
include H hi

theorem fn_unique {U : Y.Opens} (a b : Fin n → Γ(Y, U))
    (h : ∀ y, p y ∈ U → ∑ i, constVal π' y (c i) * gs p y U (a i) = ∑ i, constVal π' y (c i) * gs p y U (b i))
    (i : Fin n) : a i = b i := by
  refine fn_ext fun y hy => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  have hle : V ≤ U := hle
  have e := fn_indep H hV c hi (fun i => resFn π hle (a i - b i : Γ(Y, U))) (fn_ext fun z hz => by
    refine (gs_comb H c _ z hz).trans (Eq.trans ?_ (gs_zero' (𝟙 Y') z (p ⁻¹ᵁ V) hz).symm)
    refine (Finset.sum_congr rfl fun i _ => congrArg _ ((gs_res p z hle hz _).trans
      (gs_sub' p z U (hle hz) _ _))).trans ?_
    simp only [mul_sub, Finset.sum_sub_distrib, h z (hle hz), sub_self]) i
  exact sub_eq_zero.1 ((gs_sub' _ y U hy _ _).symm.trans ((gs_res (𝟙 Y) y hle hyV _).symm.trans
    ((congrArg (gs (𝟙 Y) y V) e).trans (gs_zero' _ y V hyV))))

variable (hc : ∀ y, ∃ a : Fin n → S, y = ∑ i, fS (a i) * c i)
include hc

theorem fn_span_open {U : Y.Opens} {U' : Y'.Opens} (hU : U' = p ⁻¹ᵁ U) (t : Γ(Y', U')) :
    ∃ a : Fin n → Γ(Y, U), ∀ y, p y ∈ U → gs (𝟙 Y') y U' t = ∑ i, constVal π' y (c i) * gs p y U (a i) := by
  subst hU
  let W : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U} → Y.Opens := fun V => V.1
  have loc : ∀ V, ∃ u : Fin n → Γ(Y, W V), ∀ y, p y ∈ W V →
      gs (𝟙 Y') y (p ⁻¹ᵁ U) t = ∑ i, constVal π' y (c i) * gs p y (W V) (u i) := fun V => by
    have hle : p ⁻¹ᵁ V.1 ≤ p ⁻¹ᵁ U := fun z hz => V.2.2 hz
    obtain ⟨u, hu⟩ := fn_span H c V.2.1 hc (resFn π' hle t)
    exact ⟨u, fun y hy => (gs_res (𝟙 Y') y hle hy t).symm.trans
      ((congrArg (gs (𝟙 Y') y _) hu).trans (gs_comb H c u y hy))⟩
  choose u hu using loc
  have cov : ∀ y ∈ U, ∃ V, y ∈ W V := fun y hy => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact ⟨⟨V, hV, hle⟩, hyV⟩
  have glue := fun i => (Y.sheaf.existsUnique_gluing' W U (fun V => homOfLE V.2.2)
    (fun y hy => Opens.mem_iSup.2 (cov y hy)) (fun V => u V i) (fun V V' =>
      fn_unique H c hi (U := W V ⊓ W V') (fun i => (Y.presheaf.map (homOfLE inf_le_left).op).hom (u V i))
        (fun i => (Y.presheaf.map (homOfLE inf_le_right).op).hom (u V' i)) (fun y hy => by
          simp only [gs_res p y _ hy]
          exact (hu V y hy.1).symm.trans (hu V' y hy.2)) i)).exists
  choose a ha using glue
  refine ⟨a, fun y hy => ?_⟩
  obtain ⟨V, hV⟩ := cov _ hy
  exact (hu V y hV).trans (Finset.sum_congr rfl fun i _ => congrArg _
    ((congrArg (gs p y (W V)) (ha i V)).symm.trans (gs_res p y V.2.2 hV _)))

theorem sec_span {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (hL : L.IsLB) (t : SecOver π' (LB.LinComb L φ' ε)) :
    ∃ d : Fin n → SecOver π (LB.LinComb L φ ε), t = ∑ i, c i • pullOver L ε H.w hφ (d i) := by
  choose a ha using fun j : K → L.ι => fn_span_open H c hi hc (wchart_eq hφ j) (LB.Sec.f t j)
  refine ⟨fun i => ⟨fun j => a j i, fun (j j' : K → L.ι) => fn_unique H c hi (U := LB.wchart L φ j ⊓ LB.wchart L φ j')
    (fun i => (Y.presheaf.map (homOfLE inf_le_left).op).hom (a j i))
    (fun i => (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') from ((LB.LinComb L φ ε).g j j').val) *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (a j' i))
    (fun y hy => ?_) i⟩, sec_ext' hL fun y J hJ => ?_⟩
  · have e : ∀ i, gs p y _ ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') from ((LB.LinComb L φ ε).g j j').val) *
        (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (a j' i)) =
        (Geo.Tor.trF φ ε p y j j').val * gs p y _ (a j' i) := fun i =>
      (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
        (congrArg Units.val (gm_linComb L φ ε p y j j' hy.1 hy.2))) (gs_res _ y _ hy _))
    have e' := sec_trans t (𝟙 Y') y ((wchart_eq hφ j).ge hy.1) ((wchart_eq hφ j').ge hy.2)
    rw [ha j y hy.1, ha j' y hy.2, trF_comp hφ, Category.id_comp, Finset.mul_sum] at e'
    refine (Finset.sum_congr rfl fun i _ => congrArg _ (gs_res p y _ hy _)).trans (e'.trans
      (Finset.sum_congr rfl fun i _ => ?_))
    exact (mul_left_comm _ _ _).trans (congrArg _ (e i).symm)
  · have hy := hJ.mem φ' (𝟙 Y')
    rw [sval_sum' hJ]
    refine (ha _ y ((wchart_eq hφ _).le hy)).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [sval_smul' hJ, Category.id_comp]
    exact congrArg _ ((gs_pullFn H.w _ _ (𝟙 Y') y hy).trans
      (congrArg (fun q => gs q y _ (a _ i)) (Category.id_comp p))).symm

end Flat

section Main

variable {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {R R' : Type} [CommRing R] [CommRing R']

abbrev str (χ : Sp R ⟶ Z) : (Over.mk χ ⊗ G).left ⟶ Spec (CommRingCat.of R) := (fst (Over.mk χ) G).left

abbrev Sc (χ : Sp R ⟶ Z) : Type :=
  SecOver (str G χ) (LB.LinComb L (K := Fin 1) (fun _ => (snd (Over.mk χ) G).left) (fun _ => (N : ℤ)))

theorem whisker_pb {χ : Sp R ⟶ Z} {χ' : Sp R' ⟶ Z} (g : R →+* R') (e : spMap g ≫ χ = χ') :
    IsPullback ((Over.homMk (spMap g) e : Over.mk χ' ⟶ Over.mk χ) ▷ G).left (str G χ') (str G χ)
      (Spec.map (CommRingCat.ofHom g)) := by
  refine IsPullback.of_right (h₁₂ := (snd (Over.mk χ) G).left) (v₁₃ := G.hom) (h₂₂ := χ) ?_ ?_
    (IsPullback.of_hasPullback χ G.hom).flip
  · rw [← Over.comp_left, whiskerRight_snd, e]
    exact (IsPullback.of_hasPullback χ' G.hom).flip
  · rw [← Over.comp_left, whiskerRight_fst]; rfl

theorem whisker_snd' {T T' : Over Z} (h : T' ⟶ T) (_k : Fin 1) :
    (snd T' G).left = (h ▷ G).left ≫ (snd T G).left := by rw [← Over.comp_left, whiskerRight_snd]

abbrev pb {χ : Sp R ⟶ Z} {χ' : Sp R' ⟶ Z} (g : R →+* R') (e : spMap g ≫ χ = χ') : Sc G L N χ →ₛₗ[g] Sc G L N χ' :=
  pullOver L (fun _ => (N : ℤ)) (whisker_pb G g e).w (whisker_snd' G _)

instance flat_str [Flat G.hom] (χ : Sp R ⟶ Z) : Flat (str G χ) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback χ G.hom).flip ‹_›

variable {G L N} (hL : L.IsLB)
include hL

theorem lin_iff_sum {T : Over Z} {χ' : Sp R' ⟶ Z} (h : Over.mk χ' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (t : Fin n → Sc G L N χ') (ht : ∀ i y J, Good L y J → sval (t i) (𝟙 _) y J =
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left y J)
    (c : Fin n → R') (s : Sc G L N χ') : Lin G L N h b (fun i => fnR (c i)) s ↔ s = ∑ i, c i • t i := by
  have e : ∀ y J, Good L y J → sval (∑ i, c i • t i : Sc G L N χ') (𝟙 _) y J = ∑ i, gs (str G χ') y ⊤ (fnR (c i)) *
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left y J :=
    fun y J hJ => by
      rw [sval_sum' hJ]
      exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, ht i y J hJ, Category.id_comp]; rfl
  exact ⟨fun H => sec_ext' hL fun y J hJ => (H y J hJ).trans (e y J hJ).symm,
    fun H y J hJ => H ▸ e y J hJ⟩

theorem basis_iff {χ : Sp R ⟶ Z} {n : ℕ} (b : Fin n → Sc G L N χ) :
    BasisAlong G L N (𝟙 (Over.mk χ)) b ↔ ∀ t : Sc G L N χ, ∃! c : Fin n → R, t = ∑ i, c i • b i := by
  refine forall_congr' fun t => ?_
  let e : R ≃ Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toEquiv
  refine ((Equiv.piCongrRight fun _ : Fin n => e).existsUnique_congr fun c => ?_).symm
  exact (lin_iff_sum hL (𝟙 _) b b (fun i y J _ => by rw [id_whiskerRight]; rfl) c t).symm

theorem lin_one_iff {χ : Sp R ⟶ Z} {χ' : Sp R' ⟶ Z} (g : R →+* R') (e : spMap g ≫ χ = χ') (b : Sc G L N χ)
    (s : Sc G L N χ') : Lin G L N (Over.homMk (spMap g) e : Over.mk χ' ⟶ Over.mk χ) (fun _ : Fin 1 => b) (fun _ => 1) s ↔
      s = pb G L N g e b := by
  have := lin_iff_sum hL (Over.homMk (spMap g) e : Over.mk χ' ⟶ Over.mk χ) (fun _ : Fin 1 => b)
    (fun _ => pb G L N g e b) (fun i y J hJ => (sval_pullOver _ _ _ _ hJ).trans (by rw [Category.id_comp])) (fun _ => 1) s
  rw [Fin.sum_univ_one, one_smul] at this
  refine Iff.trans ?_ this
  simp only [fnR, map_one]

theorem pb_pb {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {χ : Sp R ⟶ Z} {χ₁ : Sp R₁ ⟶ Z} {χ₂ : Sp R₂ ⟶ Z}
    (g : R →+* R₁) (e : spMap g ≫ χ = χ₁) (g' : R₁ →+* R₂) (e' : spMap g' ≫ χ₁ = χ₂) (k : R →+* R₂)
    (e'' : spMap k ≫ χ = χ₂) (hk : k = g'.comp g) (b : Sc G L N χ) :
    pb G L N g' e' (pb G L N g e b) = pb G L N k e'' b := by
  refine sec_ext' hL fun y J hJ => ?_
  rw [sval_pullOver _ _ _ _ hJ, sval_pullOver _ _ _ _ hJ, sval_pullOver _ _ _ _ hJ, Category.assoc, ← Over.comp_left,
    ← comp_whiskerRight]
  congr 4
  subst hk
  exact Over.OverMorphism.ext (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom g')).symm

end Main

theorem frameAt_of_finite : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), Flat G.hom → L.IsLB → ∀ (N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ Z) (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (io : W →+* W') (io' : FractionRing W →+* FractionRing W'), io.Finite → (∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) → ∀ (gam : K →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) (h' : spMap (io'.comp gam) ≫ x = jK W' ≫ spMap io ≫ χ) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), FrameAt G L N x (io'.comp gam) (spMap io ≫ χ) h' f → FrameAt G L N x gam χ h f := by
  intro Z G L hG hL N K _ x W W' _ _ _ _ _ _ io io' hf hr gam χ h h' n f ⟨b', hb', hs⟩
  have hio : Function.Injective io := fun y z e => IsFractionRing.injective W (FractionRing W)
    (io'.injective (by rw [hr, hr, e]))
  obtain ⟨m, β, u, v, hu, huv, hβ, hi⟩ := exists_basis_dvr io hio hf
  have hr' : io'.comp (algebraMap W _) = (algebraMap W' _).comp io := RingHom.ext hr
  have e₁ : spMap io' ≫ jK W ≫ χ = jK W' ≫ spMap io ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hr']
  have e₂ : spMap ((algebraMap W' (FractionRing W')).comp io) ≫ χ = jK W' ≫ spMap io ≫ χ := by
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  have hi' : ∀ a : Fin m → FractionRing W, ∑ k, io' (a k) * algebraMap W' _ (β k) = 0 → ∀ k, a k = 0 := fun a ha k => by
    obtain ⟨r, hr₀⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors W) a
    choose c hc using hr₀
    have := hi c (IsFractionRing.injective W' (FractionRing W') (by
      simp only [map_sum, map_mul, ← hr, hc, Algebra.smul_def, _root_.mul_assoc]
      rw [← Finset.mul_sum, ha, mul_zero, map_zero])) k
    have e := hc k
    rw [this, map_zero, Algebra.smul_def] at e
    exact (mul_eq_zero.1 e.symm).resolve_left
      ((map_ne_zero_iff _ (IsFractionRing.injective W _)).2 (nonZeroDivisors.coe_ne_zero r))
  obtain ⟨b, h₁, h₂⟩ := exists_basis_of_square (pb G L N io (χ := χ) rfl)
    (pb G L N (algebraMap W (FractionRing W)) (χ := χ) (χ' := jK W ≫ χ) rfl) (pb G L N io' e₁)
    (pb G L N (algebraMap W' (FractionRing W')) (χ := spMap io ≫ χ) (χ' := jK W' ≫ spMap io ≫ χ) rfl) hr hio
    (fun t => (pb_pb hL _ _ _ _ _ e₂ rfl t).trans (pb_pb hL _ _ _ _ _ e₂ hr'.symm t).symm)
    ((injective_iff_map_eq_zero _).2 fun t ht => sec_indep
      (whisker_pb G (algebraMap W' (FractionRing W')) rfl) _ _ (fun _ : Fin 1 => (1 : FractionRing W'))
      (fun a ha i => by
        rw [Fin.sum_univ_one, _root_.mul_one] at ha
        rw [Subsingleton.elim i 0]
        exact IsFractionRing.injective W' (FractionRing W') (ha.trans (map_zero _).symm)) (fun _ => t)
      (by rw [Fin.sum_univ_one, one_smul]; exact ht) 0)
    β u v hu huv hβ (sec_span (whisker_pb G io rfl) β hi hβ _ _ hL) (sec_indep (whisker_pb G io rfl) _ _ β hi)
    (sec_indep (whisker_pb G io' e₁) _ _ _ hi') b' (fun i => pb G L N gam h (f i))
    (fun i => by
      obtain ⟨s, s₁, s₂⟩ := hs i
      exact ((lin_one_iff hL _ _ _ _).1 s₂).symm.trans (((lin_one_iff hL _ _ _ _).1 s₁).trans
        (pb_pb hL _ _ _ _ _ _ rfl _).symm))
    ((basis_iff hL b').1 hb')
  exact ⟨b, (basis_iff hL b).2 h₂, fun i => ⟨pb G L N gam h (f i), (lin_one_iff hL _ _ _ _).2 rfl,
    (lin_one_iff hL _ _ _ _).2 (h₁ i).symm⟩⟩

end GlobalTheory.OneBasis.TraitDescent
