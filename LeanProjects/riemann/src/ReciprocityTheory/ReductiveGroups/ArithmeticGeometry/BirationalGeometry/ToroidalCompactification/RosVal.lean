import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem gen_unique' {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t', ht', hv⟩ := exists_gen hM hF u' hu'
  have key := gen_unique hM p e he hp hu ht' (fun y J hJ => (h y J hJ).trans (hv _ e y J hJ).symm) Z r z J hJ
  exact key.trans (hv Z r z J hJ)

theorem gm_inj {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U U' : X.Opens} (h : κ z ∈ U) (h' : κ z ∈ U')
    {a : Γ(X, U)ˣ} {b : Γ(X, U')ˣ} (e : gm κ z U a = gm κ z U' b) :
    gm (𝟙 X) (κ z) U a = gm (𝟙 X) (κ z) U' b := by
  have key : ∀ (V : X.Opens) (hV : κ z ∈ V) (c : Γ(X, V)ˣ),
      (κ.stalkMap z).hom ((gm (𝟙 X) (κ z) V c : (X.presheaf.stalk (κ z))ˣ) : X.presheaf.stalk (κ z)) =
        ((gm κ z V c : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) := by
    intro V hV c
    have h1 : (𝟙 X : X ⟶ X) (κ z) ∈ V := hV
    simp only [gm, dif_pos hV, dif_pos h1, MonoidHom.comp_apply, Units.coe_map, pullU, MonoidHom.coe_coe]
    clear e h h' a b U U'
    first
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         rw [Scheme.Hom.germ_stalkMap_apply]; rfl)
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         simp [Scheme.Hom.germ_stalkMap_apply]; done)
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         clear * -; done)
  have hinj : Function.Injective (κ.stalkMap z).hom := by
    first
      | exact (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
      | exact (asIso (κ.stalkMap z)).commRingCatIsoToRingEquiv.injective
  apply Units.ext
  apply hinj
  rw [key U h a, key U' h' b]
  exact congrArg Units.val e

theorem exists_ext_unit {X Y : Scheme.{0}} (κ : Y ⟶ X) [IsOpenImmersion κ] (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    ∃ b : Γ(X, κ ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ κ) z (κ ''ᵁ V) b = gm r z V a := by
  refine ⟨Units.map (κ.appIso V).inv.hom.toMonoidHom a, fun Z r z hz => ?_⟩
  have hm : r z ∈ κ ⁻¹ᵁ (κ ''ᵁ V) := ⟨r z, hz, rfl⟩
  have e : pullU κ (κ ''ᵁ V) (Units.map (κ.appIso V).inv.hom.toMonoidHom a) = res (κ.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (κ.appIso_inv_app V))
  rw [← gm_pull r κ z _ hm, e, gm_res r z _ hm]

theorem glue_gen {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (t : ∀ s, LB.Gen (LB.LinComb M (fun k => (W s).ι ≫ φ k) ε)) (ht : ∀ s, (t s).IsGen)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z) (J), Good M z J →
      r ≫ (W s).ι = r' ≫ (W s').ι → val (t s) r z J = val (t s') r' z J) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z) (J), Good M z J →
      val u (r ≫ (W s).ι) z J = val (t s) r z J := by
  have glue : ∀ j : K → M.ι, ∃ a : Γ(Y, LB.wchart M φ j)ˣ, ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z),
      r z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j →
      gm (r ≫ (W s).ι) z _ a = gm r z (LB.wchart M (fun k => (W s).ι ≫ φ k) j) ((t s).s j) := by
    intro j
    choose b hb using fun s => exists_ext_unit (W s).ι (LB.wchart M (fun k => (W s).ι ≫ φ k) j) ((t s).s j)
    have le : ∀ s, (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j ≤ LB.wchart M φ j := by
      rintro s _ ⟨y, hy, rfl⟩
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    obtain ⟨a, ha⟩ := glue_unit (LB.wchart M φ j) _ le (fun y hy => by
        obtain ⟨s, hs⟩ := hW y
        exact Opens.mem_iSup.2 ⟨s, ⟨y, hs⟩, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, rfl⟩) b (fun s s' y hy => by
        obtain ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ := hy
        have hy₁ : y ∈ W s := e₁ ▸ y₁.2
        have hy₂ : y ∈ W s' := e₂ ▸ y₂.2
        let z : (W s ⊓ W s').toScheme := ⟨y, hy₁, hy₂⟩
        let r := Y.homOfLE (inf_le_left : W s ⊓ W s' ≤ W s)
        let r' := Y.homOfLE (inf_le_right : W s ⊓ W s' ≤ W s')
        have f₁ : r ≫ (W s).ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
        have f₂ : r' ≫ (W s').ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
        have hj : y ∈ LB.wchart M φ j := le s ⟨y₁, h₁, e₁⟩
        have m₁ : r z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j := Set.mem_iInter.2 fun k =>
          (congrArg (fun q => φ k (q z) ∈ M.U (j k)) f₁).mpr (Set.mem_iInter.1 hj k)
        have m₂ : r' z ∈ LB.wchart M (fun k => (W s').ι ≫ φ k) j := Set.mem_iInter.2 fun k =>
          (congrArg (fun q => φ k (q z) ∈ M.U (j k)) f₂).mpr (Set.mem_iInter.1 hj k)
        choose I hI using fun χ : (W s ⊓ W s').toScheme ⟶ X => exists_chart hM (χ z)
        have c₁ := gen_trans (ht s) r z m₁ (Good.mem hI _ r)
        have c₂ := gen_trans (ht s') r' z m₂ (Good.mem hI _ r')
        have c₃ : trF (fun k => (W s).ι ≫ φ k) ε r z j (fun k => I (r ≫ (W s).ι ≫ φ k)) =
            trF (fun k => (W s').ι ≫ φ k) ε r' z j (fun k => I (r' ≫ (W s').ι ≫ φ k)) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          have : r ≫ (W s).ι ≫ φ k = r' ≫ (W s').ι ≫ φ k := by rw [← Category.assoc, f₁, ← Category.assoc, f₂]
          show gm (r ≫ (W s).ι ≫ φ k) z (M.U (j k) ⊓ M.U (I (r ≫ (W s).ι ≫ φ k))) (M.g (j k) (I (r ≫ (W s).ι ≫ φ k))) ^ _ =
            gm (r' ≫ (W s').ι ≫ φ k) z (M.U (j k) ⊓ M.U (I (r' ≫ (W s').ι ≫ φ k))) (M.g (j k) (I (r' ≫ (W s').ι ≫ φ k))) ^ _
          rw [this]
        have b₁ := hb s _ r z m₁
        have b₂ := hb s' _ r' z m₂
        rw [f₁] at b₁
        rw [f₂] at b₂
        have n₁ : (W s ⊓ W s').ι z ∈ (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j := ⟨y₁, h₁, e₁⟩
        have n₂ : (W s ⊓ W s').ι z ∈ (W s').ι ''ᵁ LB.wchart M (fun k => (W s').ι ≫ φ k) j := ⟨y₂, h₂, e₂⟩
        exact gm_inj (W s ⊓ W s').ι z n₁ n₂ (b₁.trans (c₁.trans ((congrArg₂ (· * ·) c₃
          (agree s s' _ r r' z I hI (f₁.trans f₂.symm))).trans (c₂.symm.trans b₂.symm)))))
    refine ⟨a, fun s Z r z hz => ?_⟩
    have hm : (r ≫ (W s).ι) z ∈ (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j := ⟨r z, hz, rfl⟩
    exact (gm_res _ z (le s) hm a).symm.trans ((congrArg (gm _ z _) (ha s)).trans (hb s Z r z hz))
  choose a ha using glue
  refine ⟨⟨a⟩, fun j j' => unit_ext fun y hy => ?_, fun s Z r z J hJ => ?_⟩
  · obtain ⟨s, hs⟩ := hW y
    let z : (W s).toScheme := ⟨y, hs⟩
    have m₁ : (𝟙 _ : (W s).toScheme ⟶ _) z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
    have m₂ : (𝟙 _ : (W s).toScheme ⟶ _) z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j' :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    have a₁ := ha j s _ (𝟙 _) z m₁
    have a₂ := ha j' s _ (𝟙 _) z m₂
    rw [Category.id_comp] at a₁ a₂
    have hz : (W s).ι z ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hy
    refine gm_inj (W s).ι z hz hz (((gm_res _ z _ hz _).trans (a₁.trans (gen_trans (ht s) (𝟙 _) z m₁ m₂))).trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb M φ ε (W s).ι z j j' hz.1 hz.2).trans ?_)
      ((gm_res _ z _ hz _).trans a₂))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ (W s).ι) z J (fun k => J (r ≫ (W s).ι ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact ha _ s Z r z (hJ.mem _ r)

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem surj_snd (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (snd A T).left.appTop.hom := by
  have hB : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  exact (hG _ _ hB).2

theorem surj_comp {X Y Z : Scheme.{0}} {p : X ⟶ Y} {q : Y ⟶ Z} (hp : Function.Surjective p.appTop.hom)
    (hq : Function.Surjective q.appTop.hom) : Function.Surjective (p ≫ q).appTop.hom := by
  first
    | (rw [Scheme.Hom.comp_appTop]; exact hp.comp hq)
    | (rw [Scheme.comp_appTop]; exact hp.comp hq)
    | (simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
    | simpa using hp.comp hq

variable [IsCommMonObj A] {L : LB A.left}

def val₂ {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε)) {T : Over S}
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (x y : T ⟶ A) : (T.left.presheaf.stalk z)ˣ := val u (lift x y).left z J

theorem prod_ros (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ i, h ((lift x y).left ≫ rosatiφ A f g i) ^ rosatiε i =
      h ((x ≫ f) * y).left * (h (x ≫ f).left)⁻¹ * (h y.left)⁻¹ * (h (x * (y ≫ g)).left)⁻¹ * h x.left * h (y ≫ g).left := by
  have e : ∀ k : A ⊗ A ⟶ A, (lift x y).left ≫ k.left = (lift x y ≫ k).left := fun k => by
    rw [Over.comp_left]
  have m1 : ∀ a b : A ⊗ A ⟶ A, (lift x y ≫ padd A a b).left = ((lift x y ≫ a) * (lift x y ≫ b)).left := by
    intro a b
    first
      | (simp only [padd, comp_lift_assoc]; rfl)
      | (simp only [padd, ← Category.assoc, comp_lift]; rfl)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε, Matrix.cons_val_zero,
    Matrix.cons_val_succ, e, m1, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, zpow_one, zpow_neg,
    mul_one]
  first
    | ac_rfl
    | (simp only [mul_comm, mul_assoc, mul_left_comm]; done)
    | (rw [← mul_inv_eq_one]; simp only [mul_inv_rev, inv_inv, mul_comm, mul_assoc, mul_left_comm, inv_mul_cancel, mul_inv_cancel]; done)

theorem exists_ros (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A L f g) : ∃ u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) := by

  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (K := Fin 6)
      (fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) rosatiε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = b ≫ zero2 A → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    have z2 : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
    obtain ⟨n, n₁⟩ : ∃ n : ((A ⊗ A).hom ⁻¹ᵁ U).toScheme ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
        n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom ≫ zero2 A :=
      ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom ≫ zero2 A) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e := congrArg (fun q => q ((A ⊗ A).hom y.1)) z2
        exact (congrArg (· ∈ U) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    let T₀ : Over S := Over.mk (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (A ⊗ A).hom)
    have n₂ : n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = (lift (1 : T₀ ⟶ A) (1 : T₀ ⟶ A)).left := by
      have : lift (1 : T₀ ⟶ A) (1 : T₀ ⟶ A) = toUnit T₀ ≫ lift η[A] η[A] := by rw [comp_lift]; rfl
      rw [n₁, this, ← Category.assoc]; rfl
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) (ε' := rosatiε)
      (fun V _ k => by
        have p := prod_ros f g (1 : T₀ ⟶ A) (1 : T₀ ⟶ A) k
        rw [← n₂, MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
        refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
          (c := ∏ i, k (((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) ^ rosatiε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by rw [Category.assoc]; rfl).trans p))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc (zero2 A), z2]
      exact congrArg (b ≫ ·) (Category.id_comp _)
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc

  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ ((A ⊗ A).hom ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι = r' ≫ ((A ⊗ A).hom ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : Over S := Over.mk (U s ⊓ U s').ι
    let pr : A ⊗ A ⊗ V ⟶ A ⊗ A := lift (fst _ _) (snd _ _ ≫ fst _ _)
    have mk : ∀ W : S.Opens, U s ⊓ U s' ≤ W → ∃ m : (A ⊗ A ⊗ V).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ W).toScheme,
        m ≫ ((A ⊗ A).hom ⁻¹ᵁ W).ι = pr.left := fun W hW =>
      ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ W).ι pr.left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e := congrArg (fun q => q y) ((Over.w pr).trans (Over.w (snd A (A ⊗ V) ≫ snd A V)).symm)
        exact (congrArg (· ∈ W) e).mpr (hW ((snd A (A ⊗ V) ≫ snd A V).left y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e : V ⟶ A ⊗ A ⊗ V := lift 1 (lift 1 (𝟙 V))
    have he : e ≫ pr = toUnit V ≫ lift η[A] η[A] := by rw [comp_lift, comp_lift]; simp [e, Hom.one_def]
    let TZ : Over S := Over.mk ((r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι) ≫ (A ⊗ A).hom)
    let xy : TZ ⟶ A ⊗ A := Over.homMk (r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι) rfl
    let v : TZ ⟶ V := Over.homMk (IsOpenImmersion.lift (U s ⊓ U s').ι TZ.hom (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun q => (A ⊗ A).hom (q y) ∈ U s') hr).mpr (r' y).2⟩)) (IsOpenImmersion.lift_fac _ _ _)
    let ρ : TZ ⟶ A ⊗ A ⊗ V := lift (xy ≫ fst _ _) (lift (xy ≫ snd _ _) v)
    have hρ : ρ ≫ pr = xy := by ext <;> simp [ρ, pr]
    have hρ' : ρ.left ≫ pr.left = r ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι := congrArg (fun q => q.left) hρ
    have r₁ : ρ.left ≫ m = r := by rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ']
    have r₂ : ρ.left ≫ m' = r' := by rw [← cancel_mono ((A ⊗ A).hom ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ', hr]
    have key := gen_unique' hL (φ := fun i => m ≫ ((A ⊗ A).hom ⁻¹ᵁ U s).ι ≫ rosatiφ A f g i) (ε := rosatiε)
      (φ' := fun i => m' ≫ ((A ⊗ A).hom ⁻¹ᵁ U s').ι ≫ rosatiφ A f g i) (ε' := rosatiε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      ((snd A (A ⊗ V)).left ≫ (snd A V).left) e.left (by
        rw [← Over.comp_left, ← Over.comp_left]
        exact congrArg (fun q => q.left) (show e ≫ snd A (A ⊗ V) ≫ snd A V = 𝟙 V by simp [e]))
      (surj_comp (surj_snd hG hA _) (surj_snd hG hA _)) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        have he' : e.left ≫ pr.left = V.hom ≫ zero2 A := congrArg (fun q => q.left) he
        rw [val_pull hI, val_pull hI, hn s _ _ V.hom y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.hom y I hI (by rw [Category.assoc, hm', he'])]) Z ρ.left z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, hv⟩ := glue_gen hL (rosatiφ A f g) rosatiε (fun s => (A ⊗ A).hom ⁻¹ᵁ U s)
    (fun y => ⟨(A ⊗ A).hom y, hU _⟩) t ht agree
  refine ⟨u, hu, fun j j' c₁ _ _ => unit_ext fun y hy => ?_⟩

  have z2 : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
  let z : (U y).toScheme := ⟨y, hU y⟩
  obtain ⟨r, hr⟩ : ∃ r : (U y).toScheme ⟶ ((A ⊗ A).hom ⁻¹ᵁ U y).toScheme,
      r ≫ ((A ⊗ A).hom ⁻¹ᵁ U y).ι = (U y).ι ≫ zero2 A :=
    ⟨IsOpenImmersion.lift _ ((U y).ι ≫ zero2 A) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (· ∈ U y) (congrArg (fun m => m q.1) z2)).mpr q.2), IsOpenImmersion.lift_fac _ _ _⟩
  have all : ∀ a b, zero2 A ≫ rosatiφ A f g a = zero2 A ≫ rosatiφ A f g b := by
    have one : ∀ a, zero2 A ≫ rosatiφ A f g a = η[A].left := fun a => by
      have e : ∀ q : A ⊗ A ⟶ A, lift η[A] η[A] ≫ q = η[A] → zero2 A ≫ q.left = η[A].left := fun q hq =>
        congrArg (fun m => m.left) hq
      have o : lift η[A] η[A] ≫ μ[A] = η[A] := by simpa [Hom.one_def, Hom.mul_def] using
        (_root_.mul_one (1 : 𝟙_ (Over S) ⟶ A))
      fin_cases a <;> refine e _ ?_ <;> simp [padd, comp_lift_assoc, o]
    exact fun a b => (one a).trans (one b).symm
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun k => (U y).ι ≫ zero2 A ≫ rosatiφ A f g k) j
    (fun a b _ => c₁ a b (all a b)) (fun k => Set.mem_iInter.1 hy.1 k)
  have v := (val_pull hJ u (zero2 A) (U y).ι).trans (by rw [← hr, hv y _ r z J hJ, hn y _ r (U y).ι z J hJ hr] :
    val u ((U y).ι ≫ zero2 A) z J = 1)
  rw [val_of _ (U y).ι z J j eJ] at v
  have hz : (U y).ι z ∈ LB.wchart L (fun k => zero2 A ≫ rosatiφ A f g k) j ⊓ LB.wchart L PEmpty.elim j' := hy
  exact gm_inj (U y).ι z hz hz (((gm_res _ z _ hz _).trans v).trans ((gm_res _ z _ hz _).trans (map_one _)).symm)

variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem ros_add (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by
  let p₀ := x3 A 0
  let p₁ := x3 A 1
  let p₂ := x3 A 2
  have mf : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good Lr.L z J → ∀ a b : T ⟶ A,
      val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good Lr.L y J → val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
    have := val_corr hJ h₀ (𝟙 _)
    rw [val_pull hJ, Category.id_comp, val_one] at this
    rw [val₂, e]; exact this
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 A := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 A ⟶ A),
      (∀ (V : Type) [CommGroup V] (k : (G3 A ⟶ A) → V),
        (k (l₁ * l₂ * l₃) * (k (l₁ * l₂))⁻¹ * (k (l₁ * l₃))⁻¹ * (k (l₂ * l₃))⁻¹ * k l₁ * k l₂ * k l₃ * (k 1)⁻¹) *
          ((k ((a₁ ≫ f) * b₁) * (k (a₁ ≫ f))⁻¹ * (k b₁)⁻¹ * (k (a₁ * (b₁ ≫ g)))⁻¹ * k a₁ * k (b₁ ≫ g)) *
            (k ((a₂ ≫ f) * b₂) * (k (a₂ ≫ f))⁻¹ * (k b₂)⁻¹ * (k (a₂ * (b₂ ≫ g)))⁻¹ * k a₂ * k (b₂ ≫ g))) =
        (k ((a ≫ f) * b) * (k (a ≫ f))⁻¹ * (k b)⁻¹ * (k (a * (b ≫ g)))⁻¹ * k a * k (b ≫ g)) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 ∨ e ≫ l₂ = 1 →
      val₂ u z J (ρ ≫ a) (ρ ≫ b) * cubV c z J (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c z J (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) * (val₂ u z J (ρ ≫ a₁) (ρ ≫ b₁) * val₂ u z J (ρ ≫ a₂) (ρ ≫ b₂)) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good Lr.L z J →
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a b).left)
          (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift k₁ (lift k₂ k₃)).left)) σ.left z J =
          val₂ u z J (σ ≫ a) (σ ≫ b) * cubV c z J (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift l₁ (lift l₂ l₃)).left)
          (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a₁ b₁).left) (LB.pullGen Lr.L _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c z J (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val₂ u z J (σ ≫ a₁) (σ ≫ b₁) * val₂ u z J (σ ≫ a₂) (σ ≫ b₂)) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (val_cub c σ hJ _ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => ?_) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (DVR.prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub l₁ l₂ l₃ k)
        (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g a₁ b₁ k) (prod_ros f g a₂ b₂ k))).trans
        ((hF V fun q => k q.left).trans (DVR.prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros f g a b k)
          (prod_cub k₁ k₂ k₃ k)).symm)
    · have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, v1 hI, C.face]
      rcases hl with hl | hl
      · rw [hl, C.face]; simp
      · rw [hl, C.face₂]; simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ g) (p₀ ≫ f) (p₁ ≫ f) p₂ (fun V _ k => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (Or.inl (by rw [← Category.assoc, e₀, MonObj.one_comp]))
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ (p₀ ≫ g) (p₁ ≫ g) (p₂ ≫ f) p₀ p₁ (fun V _ k => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      have : (p₀ * p₁) ≫ g = (p₀ ≫ g) * (p₁ ≫ g) := mg _ _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (Or.inr e₀)
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
