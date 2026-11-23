import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvWt

theorem top_le_preimage_of_fst {S : Type} [CommRing S] {X : Scheme.{0}} (w : Sp (DualNumber S) ⟶ X) (a : Sp S ⟶ X) (U : X.Opens)
    (h : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = a) (ha : ⊤ ≤ a ⁻¹ᵁ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro p _
  let p0 : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (DualNumber S)) p
  have hp : (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) p0 = p := by
    apply PrimeSpectrum.ext
    ext z
    show algebraMap S (DualNumber S) (TrivSqZeroExt.fst z) ∈ p.asIdeal ↔ z ∈ p.asIdeal
    have hz : TrivSqZeroExt.inr (TrivSqZeroExt.snd z) ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    constructor
    · intro h1
      rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      exact p.asIdeal.add_mem h1 hz
    · intro h1
      have e : TrivSqZeroExt.inl (TrivSqZeroExt.fst z) = z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) := by
        rw [eq_sub_iff_add_eq, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [e]
      exact p.asIdeal.sub_mem h1 hz
  have hm : p0 ∈ a ⁻¹ᵁ U := ha (Set.mem_univ _)
  rw [← h] at hm
  show w p ∈ U
  rw [← hp]
  exact hm

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext
  have e := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem exists_tan_over {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    {S : Type} [CommRing S] (φ : R →+* S) :
    ∃ v' : Over.mk (spMap ((algebraMap S (DualNumber S)).comp φ)) ⟶ G,
      v'.left = spMap (dualMap φ) ≫ (tv v).left ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = (1 : Over.mk (spMap φ) ⟶ G).left := by
  refine ⟨Over.homMk (spMap (dualMap φ) ≫ (tv v).left) ?_, rfl, ?_⟩
  · rw [Category.assoc, Over.w (tv v)]
    simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp]
  · let ψ : Over.mk (spMap φ) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) (by
        simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
        congr 1
        ext r
        simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hψ : ψ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • LinearMap.id)) = ψ := by
      apply Over.OverMorphism.ext
      show (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ spMap _ =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)
      simp only [spMap, ← Spec.map_comp, Category.assoc]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      simp [dualMap, CommRingCat.hom_comp, tm]
    have e := congrArg (·.left) (Formalism.L2.Pj.tan_pull (𝟙 (Sp R)) ψ hψ (tv v) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v))
    simpa [ψ] using e

theorem cv_pull_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T T' : Over (Sp R)} (k : T' ⟶ T) (x x' : T ⟶ Y.H) (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (k ≫ x')).s χ) (𝟙 _) y J =
        gm (𝟙 T'.left) y ⊤ (Units.map k.left.appTop.hom.toMonoidHom (u χ)) * val ((Y.Φ _ (k ≫ x)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have p' := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x')).2 χ y J hJ
  have p := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x)).2 χ y J hJ
  let g : LB.Gen (LB.LinComb Q.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top (u χ)⟩
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) z J', Good Q.P.L z J' → val g r z J' = gm r z ⊤ (u χ) :=
    fun Z r z J' hJ' => gm_res r z le_top (hJ'.mem PEmpty.elim r) (u χ)
  have hC := corr_of_val Q.P.isLB (t := (Y.Φ _ x').s χ) (t' := LB.mulGen Q.P.L _ _ _ _ g ((Y.Φ _ x).s χ))
    (fun y' J' hJ' => by rw [val_mul hJ', hg _ _ _ _ hJ']; exact h χ y' J' hJ')
  have e := val_corr hJ hC k.left
  rw [val_mul hJ, hg _ _ _ _ hJ] at e
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [p', p, e]
  congr 1
  have e2 := gm_pull (𝟙 _) k.left y ⊤ trivial (u χ)
  rw [Category.id_comp] at e2
  rw [← e2]
  rfl

theorem cv_mul_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T : Over (Sp R)} (X X' v : T ⟶ Y.H) (hq : X' ≫ Y.q = X ≫ Y.q)
    (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ X').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ X).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (X' * v)).s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ (X * v)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X v)).2 χ y J hJ
  have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X' v)).2 χ y J hJ
  rw [Y.Φ_b, Y.Φ_b] at h1 h2
  rw [hq] at h2
  have h3 := h χ y J hJ
  apply mul_right_cancel (b := DVR.th Q y J (DVR.cP Q _ χ) (X ≫ Y.q) (v ≫ Y.q))
  show GlobalTheory.TorusModel.cv _ χ y J * _ = _ * GlobalTheory.TorusModel.cv _ χ y J * _
  rw [h2, _root_.mul_assoc, h1, ← _root_.mul_assoc]
  congr 1

theorem _root_.GlobalTheory.Heat.IsInv.isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  intro R _ _ Q O _ _ _ oa Y v dd hinv α V f hf
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := exists_tan_over Y.H v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hW : ∀ z : Over.mk (spMap φ) ⟶ Y.H, ie ≫ (π ≫ z * v'') = z := by
    intro z
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a := by
    rw [ha]; exact congrArg (·.left) (hW x)
  have hWa' : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x' * v'').left = a' := by
    rw [ha']; exact congrArg (·.left) (hW x')
  have htr : ∀ z : Over.mk (spMap φ) ⟶ Y.H, IsTr Y.H φ z.left v (π ≫ z * v'').left := by
    intro z
    let e : tEpsG (z.left ≫ Y.H.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ z.left ≫ Y.H.hom
      rw [Over.w z]
      simp only [Over.mk_hom, Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ z, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ z.left = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  let c' : Q.X → (DualNumber S)ˣ := fun χ => Units.map (algebraMap S (DualNumber S)).toMonoidHom (c χ)
  have hqW : (π ≫ x' * v'') ≫ Y.q = (π ≫ x * v'') ≫ Y.q := by
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
  have hcW := cv_mul_of_unit Y (π ≫ x) (π ≫ x') v'' (by rw [Category.assoc, Category.assoc, hq])
    (fun χ => Units.map π.left.appTop.hom.toMonoidHom (unitOn (c χ))) (cv_pull_of_unit Y π x x' (fun χ => unitOn (c χ)) hc)
  have key := hf (DualNumber S) φε (π ≫ x * v'') (π ≫ x' * v'') c' _ _ rfl rfl
    (top_le_preimage_of_fst _ a V hWa hV) (top_le_preimage_of_fst _ a' V hWa' hV') hqW (fun χ y J hJ => by
      rw [hcW χ y J hJ]
      congr 2
      exact map_unitOn _ _)
  have e₁ := hinv.2 S φ a (π ≫ x * v'').left V f (by rw [ha]; exact Over.w x) hV (ha ▸ htr x)
  have e₂ := hinv.2 S φ a' (π ≫ x' * v'').left V f (by rw [ha']; exact Over.w x') hV' (ha' ▸ htr x')
  rw [← e₁, ← e₂, key]
  show ((c' α : DualNumber S) * _).snd = _
  rw [TrivSqZeroExt.snd_mul]
  simp [c', TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.Heat.InvWt
