import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

namespace GlobalTheory.GenTorsor

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

def pb (a : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (a.appLE U W h).hom

lemma pb_pb (b : Z ⟶ Y) (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb b V W h' (pb a U V h x) = pb (b ≫ a) U W (h'.trans (b.preimage_mono h)) x := by
  ext
  change ((a.appLE U V h ≫ b.appLE V W h').hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma pb_congr {a b : Y ⟶ X} (e : a = b) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U)
    (h' : W ≤ b ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb a U W h x = pb b U W h' x := by
  subst e; rfl

lemma res_pullU (a : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU a U x) = pb a U W h x := rfl

lemma res_eq_pb {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) : res h x = pb (𝟙 X) U W h x := rfl

lemma pb_id {U : X.Opens} (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb (𝟙 X) U U h x = x := by
  rw [← res_eq_pb (le_refl U)]
  ext
  change (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma res_pb (a : Y ⟶ X) {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (pb a U V h x) = pb a U W (le_trans h' h) x :=
  (pb_pb (𝟙 Y) a h h' x).trans (pb_congr (Category.id_comp a) _ _ _)

lemma pb_res (a : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (h' : W ≤ a ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb a V W h' (res h x) = pb a U W (h'.trans (a.preimage_mono h)) x :=
  (pb_pb a (𝟙 X) h h' x).trans (pb_congr (Category.comp_id a) _ _ _)

lemma res_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := pb_id h x

lemma pb_bijective (a : Y ⟶ X) [IsOpenImmersion a] {U : X.Opens} (hU : U ≤ a.opensRange)
    {W : Y.Opens} (h : W = a ⁻¹ᵁ U) : Function.Bijective (pb a U W h.le) := by
  subst h
  have := a.isIso_app U hU
  have e : a.appLE U (a ⁻¹ᵁ U) le_rfl = a.app U := (a.app_eq_appLE).symm
  have h2 : pb a U (a ⁻¹ᵁ U) le_rfl =
      (Units.mapEquiv (asIso (a.app U)).commRingCatIsoToRingEquiv.toMulEquiv).toMonoidHom := by
    ext x
    change (a.appLE U (a ⁻¹ᵁ U) le_rfl).hom _ = _
    rw [e]; rfl
  rw [h2]
  exact (Units.mapEquiv _).bijective

lemma unit_ext_opens {J : Type*} {V : X.Opens} (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) {u v : Γ(X, V)ˣ}
    (h : ∀ i, res (hW i) u = res (hW i) v) : u = v := by
  ext
  exact X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc _ _
    fun i => congrArg Units.val (h i)

lemma unit_glue_opens {J : Type*} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val)
    (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

lemma le_iSup_range (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (a i).opensRange := fun x hx => by
  obtain ⟨i, y, rfl⟩ := hc x
  exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩

lemma preimage_inf_range (i : J) (V : X.Opens) :
    a i ⁻¹ᵁ V = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := by
  ext y
  exact ⟨fun h => ⟨h, y, rfl⟩, fun h => h.1⟩

lemma unit_ext_cover (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {u v : Γ(X, V)ˣ}
    (h : ∀ i, pb (a i) V _ le_rfl u = pb (a i) V _ le_rfl v) : u = v := by
  refine unit_ext_opens _ (fun i => inf_le_left) (le_iSup_range a hc V) fun i => ?_
  apply (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).1
  rw [pb_res, pb_res]
  exact h i

lemma unit_glue_cover (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens)
    (u : ∀ i, Γ(T i, a i ⁻¹ᵁ V)ˣ)
    (h : ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j), b ≫ a i = c ≫ a j →
      ∀ (hb : ⊤ ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V) (hc : ⊤ ≤ c ⁻¹ᵁ a j ⁻¹ᵁ V),
        pb b _ ⊤ hb (u i) = pb c _ ⊤ hc (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, pb (a i) V _ le_rfl s = u i := by
  choose w hw using fun i => (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).2 (u i)
  obtain ⟨s, hs⟩ := unit_glue_opens V _ (fun i => inf_le_left) (le_iSup_range a hc V) w (by
    intro i j
    set W := V ⊓ (a i).opensRange ⊓ (V ⊓ (a j).opensRange) with hW
    have hi : Set.range W.ι ⊆ Set.range (a i) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.1.2
    have hj : Set.range W.ι ⊆ Set.range (a j) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.2.2
    have ei := IsOpenImmersion.lift_fac (a i) W.ι hi
    have ej := IsOpenImmersion.lift_fac (a j) W.ι hj
    have hT : (⊤ : W.toScheme.Opens) = W.ι ⁻¹ᵁ W := by simp
    have hV : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ V :=
      hT.le.trans (W.ι.preimage_mono (inf_le_left.trans inf_le_left))
    apply (pb_bijective W.ι (U := W) (by simp) hT).1
    have := h i j W _ _ (ei.trans ej.symm)
      (by rw [← Scheme.Hom.comp_preimage, ei]; exact hV)
      (by rw [← Scheme.Hom.comp_preimage, ej]; exact hV)
    rw [← hw, ← hw, pb_pb, pb_pb] at this
    rw [pb_res, pb_res]
    exact (pb_congr ei.symm _ _ _).trans (this.trans (pb_congr ej _ _ _)))
  refine ⟨s, fun i => ?_⟩
  rw [← hw, ← hs, pb_res]

end Cover

theorem exists_universal_units (K : Type) :
    ∃ (T : Scheme.{0}) (e : K → Γ(T, ⊤)ˣ), ∀ (Z : Scheme.{0}) (u : K → Γ(Z, ⊤)ˣ),
      ∃! c : Z ⟶ T, ∀ k, pb c ⊤ ⊤ le_rfl (e k) = u k := by
  let A := MonoidAlgebra ℤ (Multiplicative (FreeAbelianGroup K))
  let ε : K → Aˣ := fun k =>
    (MonoidAlgebra.of ℤ (Multiplicative (FreeAbelianGroup K))).toHomUnits
      (Multiplicative.ofAdd (FreeAbelianGroup.of k))
  have hext : ∀ (R : Type) [CommRing R] (φ ψ : A →+* R), (∀ k, φ (ε k) = ψ (ε k)) → φ = ψ := by
    intro R _ φ ψ h
    have : (φ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits =
        (ψ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits := by
      apply MonoidHom.toAdditiveRight.injective
      apply FreeAbelianGroup.lift.symm.injective
      funext k
      exact congrArg Additive.ofMul (Units.ext (h k))
    apply MonoidAlgebra.ringHom_ext
    · intro b; exact (eq_intCast (φ.comp MonoidAlgebra.singleOneRingHom) b).trans
        (eq_intCast (ψ.comp MonoidAlgebra.singleOneRingHom) b).symm
    · intro g
      exact congrArg (fun f => (f g : R)) this
  have hex : ∀ (R : Type) [CommRing R] (u : K → Rˣ), ∃ φ : A →+* R, ∀ k, φ (ε k) = u k := by
    intro R _ u
    refine ⟨(MonoidAlgebra.lift ℤ R _ ((Units.coeHom R).comp (MonoidHom.toAdditiveRight.symm
      (FreeAbelianGroup.lift fun k => Additive.ofMul (u k))))).toRingHom, fun k => ?_⟩
    simp [ε, A]
  let i := Scheme.ΓSpecIso (CommRingCat.of A)
  refine ⟨Spec (.of A), fun k => Units.map i.inv.hom (ε k), fun Z u => ?_⟩
  have hpb : ∀ (c : Z ⟶ Spec (.of A)) k,
      (pb c ⊤ ⊤ le_rfl (Units.map i.inv.hom (ε k))).val = (i.inv ≫ c.appTop).hom (ε k) := by
    intro c k
    have e : c.appLE ⊤ ⊤ le_rfl = c.appTop := (c.app_eq_appLE (U := ⊤)).symm
    change (c.appLE ⊤ ⊤ le_rfl).hom _ = _
    rw [e]; rfl
  obtain ⟨φ, hφ⟩ := hex _ u
  refine existsUnique_of_exists_of_unique ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), fun k => ?_⟩ ?_
  · apply Units.ext
    rw [hpb, ← hφ]
    have : i.inv ≫ (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
      simp [i, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [this]; rfl
  · intro c c' h h'
    apply ext_of_isAffine
    rw [← cancel_epi i.inv]
    ext1
    apply hext
    intro k
    rw [← hpb, ← hpb, h, h']

theorem isRepresentable_of_cover (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf

end GlobalTheory.GenTorsor
