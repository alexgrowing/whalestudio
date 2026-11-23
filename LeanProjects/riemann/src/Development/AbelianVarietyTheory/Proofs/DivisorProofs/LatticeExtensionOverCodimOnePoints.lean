import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMapOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeAndEigenDegrees

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.BadPt GlobalTheory.FlagLocal
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res pullback_map_app_pullbackSections app_app
  pullbackSections_smul)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul germ_resM)

namespace GlobalTheory.LatticeExt

local notation "pb" => Scheme.Modules.pullback
local notation "pf" => Scheme.Modules.pushforward

section Germ

variable {X S : Scheme.{0}}

def IsGerm (g : S ⟶ X) (x : X) : Prop :=
  (∀ W : X.Opens, x ∈ W → ⊤ ≤ g ⁻¹ᵁ W) ∧
    ∀ c : Γ(S, ⊤), ∃ (W : X.Opens) (_ : x ∈ W) (h : ⊤ ≤ g ⁻¹ᵁ W) (a : Γ(X, W)), g.appLE W ⊤ h a = c

theorem isGerm_fromSpecStalk (x : X) : IsGerm (X.fromSpecStalk x) x := by
  have h0 (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun q _ =>
    (show X.fromSpecStalk x q ⤳ x from (Scheme.range_fromSpecStalk (X := X) (x := x)).le ⟨q, rfl⟩).mem_open U.isOpen hx
  refine ⟨h0, fun c => ?_⟩
  obtain ⟨U, hx, a, ha⟩ := X.presheaf.exists_germ_eq ((Scheme.ΓSpecIso (X.presheaf.stalk x)).hom c)
  have e1 : (X.fromSpecStalk x).appLE U ⊤ (h0 U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg _ ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine ⟨U, hx, h0 U hx, a, ?_⟩
  rw [e1, CommRingCat.comp_apply, ha, ← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl

theorem IsGerm.of_comp {T : Scheme.{0}} {g : S ⟶ T} {j : T ⟶ X} [IsOpenImmersion j] {y : T}
    (h : IsGerm (g ≫ j) (j y)) : IsGerm g y := by
  have h0 (W : T.Opens) (hy : y ∈ W) : ⊤ ≤ g ⁻¹ᵁ W := by
    have := h.1 (j ''ᵁ W) ⟨y, hy, rfl⟩
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq] at this
  refine ⟨h0, fun c => ?_⟩
  obtain ⟨W, hy, hW, a, rfl⟩ := h.2 c
  refine ⟨j ⁻¹ᵁ W, hy, h0 _ hy, j.appLE W _ le_rfl a, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

variable {g : S ⟶ X} {F : X.Modules} {r : ℕ}

theorem IsGerm.exists_sec {x : X} (h : IsGerm g x) (hF : IsVB F r) (t : Γ((pb g).obj F, ⊤)) :
    ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(F, W)), pullbackSections g F (h.1 W hx) s = t := by
  have := hF.isQuasicoherent
  obtain ⟨U, e, hx, he⟩ := hF x
  obtain ⟨c, rfl⟩ := (he.pullback g ⊤ (h.1 U hx)).2 t
  choose W hW hW' a ha using fun i => h.2 (c i)
  let V : X.Opens := U ⊓ Finset.univ.inf W
  have hxV : x ∈ V := ⟨hx, by rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i) : V ≤ W i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  refine ⟨V, hxV, ∑ i, resG X (hV i) (a i) • resM F inf_le_left (e i), ?_⟩
  rw [map_sum, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pullbackSections_smul, ← ha]
  congr 1
  · exact congr($(g.map_appLE (h.1 V hxV) (homOfLE (hV i)).op) (a i))
  · exact (pullbackSections_res g F _ _ _).trans (res_pullbackSections g F _ _ _).symm

variable [IsIntegral X]

theorem eq_zero_of_res (hF : IsVB F r) {W W' : X.Opens} (h : W' ≤ W) (hη : genericPoint X ∈ W') {s : Γ(F, W)}
    (hs : resM F h s = 0) : s = 0 :=
  hF.isTorsionFree W (h hη) s (by rw [← germ_resM h hη, hs, map_zero])

theorem IsGerm.eq_zero [Nontrivial Γ(S, ⊤)] (h : IsGerm g (genericPoint X)) (hF : IsVB F r) {W : X.Opens}
    (hη : genericPoint X ∈ W) {s : Γ(F, W)} (hs : pullbackSections g F (h.1 W hη) s = 0) : s = 0 := by
  have := hF.isQuasicoherent
  obtain ⟨U, e, -, hx, hle, he⟩ := hF.exists_affine hη
  refine eq_zero_of_res hF hle hx ((he.basis le_rfl).repr.map_eq_zero_iff.1 (Finsupp.ext fun i => ?_))
  have h1 := he.pullback_basis_repr g le_rfl (h.1 U hx) (resM F hle s) i
  rw [pullbackSections_res, hs, map_zero] at h1
  by_contra hne
  set a := (he.basis le_rfl).repr (resM F hle s) i
  obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff a).1 hne)
  have hu := (RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace a).map
    (g.appLE (X.basicOpen a) ⊤ (h.1 _ (genericPoint_mem hy))).hom
  have e2 := congr($(g.map_appLE (h.1 _ (genericPoint_mem hy)) (homOfLE (X.basicOpen_le a)).op) a)
  exact not_isUnit_zero ((e2.trans h1.symm) ▸ hu)

end Germ

section Open

variable {X Y : Scheme.{0}} (a : Y ⟶ X) [IsOpenImmersion a]

theorem epi_pullback {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ W ≤ a.opensRange, ∀ t : Γ(G, W), ∀ y ∈ W, ∃ (W' : X.Opens) (h' : W' ≤ W), y ∈ W' ∧
      ∃ s, φ.app W' s = resM G h' t) : Epi ((pb a).map φ) := by
  refine ⟨fun {H} u v e => Scheme.Modules.hom_ext _ _ fun W => ?_⟩
  ext t
  change u.app W t = v.app W t
  have hW := (a.preimage_image_eq W).symm
  obtain ⟨t, rfl⟩ := (bijective_pullbackSections a G (a.image_le_opensRange W) hW).2 t
  choose W' hle hy s hs using fun y : W => h _ (a.image_le_opensRange W) t (a y) ⟨y, y.2, rfl⟩
  have hle' (y : W) : a ⁻¹ᵁ W' y ≤ W := (a.preimage_mono (hle y)).trans hW.ge
  refine Twist.sec_ext_of_cover (fun y => a ⁻¹ᵁ W' y) hle' (fun y h => Opens.mem_iSup.2 ⟨⟨y, h⟩, hy _⟩) fun y => ?_
  have : resM _ (hle' y) (pullbackSections a G hW.le t) =
      ((pb a).map φ).app _ (pullbackSections a F le_rfl (s y)) := by
    rw [pullback_map_app_pullbackSections, hs]
    exact (res_pullbackSections a G _ _ _).trans (pullbackSections_res a G _ _ _).symm
  rw [← app_resM, ← app_resM, this, app_app, app_app, e]

theorem exact_pullback {K : ShortComplex X.Modules} (h : K.Exact) : (K.map (pb a)).Exact :=
  haveI : (pb a).PreservesMonomorphisms := ⟨fun f _ => mono_pullback_of_isOpenImmersion a f⟩
  haveI := Functor.preservesHomology_of_preservesMonos_and_cokernels (pb a)
  h.map _

end Open

section Lattice

variable {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K] {f : Sp R ⟶ X} {j : T ⟶ X} {ξ : Sp K ⟶ T}
  (w : spMap (algebraMap R K) ≫ f = ξ ≫ j) {x : X} (hf : IsGerm f x)

include w hf in
theorem top_le {W : X.Opens} (hx : x ∈ W) : ⊤ ≤ ξ ⁻¹ᵁ j ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact fun q _ => hf.1 W hx trivial

def gen (M : T.Modules) {W : X.Opens} (hx : x ∈ W) : Γ((pf j).obj M, W) →+ Γ((pb ξ).obj M, ⊤) where
  toFun s := pullbackSections ξ M (top_le w hf hx) s
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

variable {M M' : T.Modules} {W W' : X.Opens}

theorem gen_res (h : W' ≤ W) (hx : x ∈ W') (s : Γ((pf j).obj M, W)) :
    gen w hf M hx (resM _ h s) = gen w hf M (h hx) s :=
  pullbackSections_res ξ M (top_le w hf hx) (j.preimage_mono h) s

theorem gen_smul (hx : x ∈ W) (a : Γ(X, W)) (s : Γ((pf j).obj M, W)) :
    gen w hf M hx (a • s) = (spMap (algebraMap R K)).appTop (f.appLE W ⊤ (hf.1 W hx) a) • gen w hf M hx s := by
  refine (pullbackSections_smul ξ M (top_le w hf hx) (j.app W a) s).trans ?_
  congr 1
  have e : j.app W ≫ ξ.appLE _ ⊤ (top_le w hf hx) = f.appLE W ⊤ (hf.1 W hx) ≫ (spMap (algebraMap R K)).appTop := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact w.symm
  exact congr($e a)

theorem gen_map (φ : M ⟶ M') (hx : x ∈ W) (s : Γ((pf j).obj M, W)) :
    gen w hf M' hx (((pf j).map φ).app W s) = ((pb ξ).map φ).app ⊤ (gen w hf M hx s) :=
  (pullback_map_app_pullbackSections ξ φ _ s).symm

theorem gen_unit (F : X.Modules) (hx : x ∈ W) (s : Γ(F, W)) :
    gen w hf _ hx ((tr (𝟙 ((pb j).obj F))).app W s) = resSec w F (pullbackSections f F (hf.1 W hx) s) := by
  rw [tr_app]
  exact (Vert.DivPull.pullbackSquare_app w F (hf.1 W hx) le_top le_rfl (top_le w hf hx) s).symm

variable (R) in

def IsLat {N : (Sp K).Modules} (L : Γ(N, ⊤) → Prop) : Prop :=
  L 0 ∧ (∀ s t, L s → L t → L (s + t)) ∧ ∀ (c : Γ(Sp R, ⊤)) s, L s → L ((spMap (algebraMap R K)).appTop c • s)

theorem isLat_inLat {N : (Sp K).Modules} {n : ℕ} (e : Fin n → Γ(N, ⊤)) : IsLat R (InLat R e) := by
  have hm (a b : K) : toFn (a * b) = toFn a * toFn b := map_mul _ _ _
  have ha (a b : K) : toFn (a + b) = toFn a + toFn b := map_add _ _ _
  have h0 : toFn (0 : K) = 0 := map_zero _
  refine ⟨⟨0, by simp [h0]⟩, ?_, ?_⟩
  · rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', by simp [ha, add_smul, Finset.sum_add_distrib]⟩
  · rintro c _ ⟨r, rfl⟩
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
    have e : (spMap (algebraMap R K)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c) = toFn (algebraMap R K c) :=
      congr($((Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))).symm) c)
    exact ⟨fun i => c * r i, by simp [e, hm, Finset.smul_sum, mul_smul]⟩

theorem isLat_resSec (F : X.Modules) : IsLat R fun s => ∃ t, s = resSec w F t := by
  refine ⟨⟨0, by rw [resSec, map_zero, map_zero]⟩, ?_, ?_⟩
  · rintro _ _ ⟨t, rfl⟩ ⟨t', rfl⟩
    exact ⟨t + t', by rw [resSec, resSec, resSec, map_add, map_add]⟩
  · rintro c _ ⟨t, rfl⟩
    refine ⟨c • t, ?_⟩
    rw [resSec, resSec, pullbackSections_smul, Scheme.Modules.Hom.app_smul, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl

variable {L : Γ((pb ξ).obj M, ⊤) → Prop} {L' : Γ((pb ξ).obj M', ⊤) → Prop}

def latSub (hL : IsLat R L) : Sub ((pf j).obj M) where
  sec W :=
    { carrier := {s | ∀ hx : x ∈ W, L (gen w hf M hx s)}
      add_mem' := fun hs ht hx => by rw [map_add]; exact hL.2.1 _ _ (hs hx) (ht hx)
      zero_mem' := fun hx => by rw [map_zero]; exact hL.1
      smul_mem' := fun a s hs hx => by rw [gen_smul]; exact hL.2.2 _ _ (hs hx) }
  res_mem h s hs hx := by rw [gen_res]; exact hs _
  mem_of_local H hx := by
    obtain ⟨W', h, hx', hs⟩ := H x hx
    have := hs hx'
    rwa [gen_res] at this

def latMap (hL : IsLat R L) (hL' : IsLat R L') (φ : M ⟶ M') (h : ∀ s, L s → L' (((pb ξ).map φ).app ⊤ s)) :
    (latSub w hf hL).toMod ⟶ (latSub w hf hL').toMod :=
  (latSub w hf hL').lift ((latSub w hf hL).incl ≫ (pf j).map φ) fun W s hx => by
    rw [← app_app, gen_map]
    exact h _ ((latSub w hf hL).incl_app_mem s hx)

@[reassoc] theorem latMap_incl (hL : IsLat R L) (hL' : IsLat R L') (φ : M ⟶ M')
    (h : ∀ s, L s → L' (((pb ξ).map φ).app ⊤ s)) :
    latMap w hf hL hL' φ h ≫ (latSub w hf hL').incl = (latSub w hf hL).incl ≫ (pf j).map φ := rfl

def latUnit (F : X.Modules) : F ⟶ (latSub w hf (isLat_resSec w F)).toMod :=
  Sub.lift _ (tr (𝟙 _)) fun _ s hx => ⟨_, gen_unit w hf F hx s⟩

@[reassoc] theorem latUnit_incl (F : X.Modules) : latUnit w hf F ≫ (latSub w hf (isLat_resSec w F)).incl = tr (𝟙 _) := rfl

variable [IsIntegral T] (hξ : IsGerm ξ (genericPoint T)) {r : ℕ}

include w hf in
theorem gen_mem (hx : x ∈ W) : genericPoint T ∈ j ⁻¹ᵁ W :=
  genericPoint_mem (x := ξ (IsLocalRing.closedPoint K)) (top_le w hf hx trivial)

include hξ in
theorem gen_injective (hM : IsVB M r) (hx : x ∈ W) : Function.Injective (gen w hf M hx) :=
  (injective_iff_map_eq_zero _).2 fun _ hs => hξ.eq_zero hM (gen_mem w hf hx) hs

variable (hT : ∀ W₀ : T.Opens, genericPoint T ∈ W₀ → ∃ W : X.Opens, x ∈ W ∧ j ⁻¹ᵁ W ≤ W₀)

include hξ hT in
theorem exists_gen_eq (hM : IsVB M r) (hx : x ∈ W) (t : Γ((pb ξ).obj M, ⊤)) :
    ∃ (W' : X.Opens) (_ : W' ≤ W) (hx' : x ∈ W') (s : Γ((pf j).obj M, W')), gen w hf M hx' s = t := by
  obtain ⟨W₀, h₀, s, rfl⟩ := hξ.exists_sec hM t
  obtain ⟨W', hx', hle⟩ := hT W₀ h₀
  exact ⟨W ⊓ W', inf_le_left, ⟨hx, hx'⟩, resM M ((j.preimage_mono inf_le_right).trans hle) s,
    pullbackSections_res ξ M _ _ s⟩

include w hf hξ hT in
theorem injective_fibre {r' : ℕ} (hM : IsVB M r) (hM' : IsVB M' r') (φ : M ⟶ M') [Mono φ] :
    Function.Injective (((pb ξ).map φ).app ⊤) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨W, -, hx, s, rfl⟩ := exists_gen_eq w hf hξ hT hM (W := ⊤) trivial t
  rw [← gen_map, ← map_zero (gen w hf M' hx)] at ht
  have : s = 0 := QCoh.injective_app_of_mono φ (j ⁻¹ᵁ W) ((gen_injective w hf hξ hM' hx ht).trans (map_zero _).symm)
  rw [this, map_zero]

variable [IsOpenImmersion j] [IsIntegral X] {V : X.Opens} (hV : ∀ y ∈ V, y ≠ x → y ∈ j.opensRange)

theorem mono_unit {F : X.Modules} (hF : IsVB F r) : Mono (tr (𝟙 ((pb j).obj F))) := by
  refine QCoh.mono_of_locally_app_injective _ fun W y hy => ⟨W, hy, le_rfl, (injective_iff_map_eq_zero _).2 fun s hs => ?_⟩
  refine eq_zero_of_res hF (W' := W ⊓ j.opensRange) inf_le_left
    ⟨genericPoint_mem hy, genericPoint_mem (x := j (genericPoint T)) ⟨_, rfl⟩⟩ ?_
  refine (bijective_tr (𝟙 ((pb j).obj F)) inf_le_right).1 ?_
  rw [app_resM, hs, map_zero, map_zero]

include hξ hV in

theorem isIso_latUnit {F : X.Modules} (hF : IsVB F r) : IsIso ((pb V.ι).map (latUnit w hf F)) := by
  haveI := mono_unit (j := j) hF
  haveI : Mono (latUnit w hf F) := mono_of_mono_fac (latUnit_incl w hf F)
  haveI := mono_pullback_of_isOpenImmersion V.ι (latUnit w hf F)
  haveI : Epi ((pb V.ι).map (latUnit w hf F)) := epi_pullback _ _ fun W hW t y hy => by
    rw [Scheme.Opens.opensRange_ι] at hW
    by_cases e : y = x
    · subst e
      obtain ⟨u, hu⟩ := Sub.incl_app_mem _ t hy
      obtain ⟨W', hx, s, rfl⟩ := hf.exists_sec hF u
      have hyW : y ∈ W ⊓ W' := ⟨hy, hx⟩
      refine ⟨W ⊓ W', inf_le_left, hyW, resM F inf_le_right s, Sub.incl_app_injective _ _
        (gen_injective w hf hξ (hF.pullback j) hyW ?_)⟩
      rw [app_app, latUnit_incl, gen_unit, app_resM, gen_res, hu, pullbackSections_res]
    · obtain ⟨s, hs⟩ := (bijective_tr (𝟙 ((pb j).obj F)) (inf_le_right : W ⊓ j.opensRange ≤ _)).2
        ((Sub.incl _).app _ (resM _ inf_le_left t))
      exact ⟨W ⊓ j.opensRange, inf_le_left, ⟨hy, hV y (hW hy) e⟩, s, Sub.incl_app_injective _ _ hs⟩
  exact isIso_of_mono_of_epi _

include hξ hT hV in

theorem exists_seq (hx : x ∉ j.opensRange) {A B : X.Modules} {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) (hM : IsVB M r)
    {a₀ : (pb j).obj A ⟶ M} {b₀ : M ⟶ (pb j).obj B} {w₀ : a₀ ≫ b₀ = 0} (h₀ : (ShortComplex.mk a₀ b₀ w₀).ShortExact)
    (hL : IsLat R L) (h : LatSeq w a₀ b₀ L) :
    ∃ (a : A ⟶ (latSub w hf hL).toMod) (b : (pb V.ι).obj (latSub w hf hL).toMod ⟶ (pb V.ι).obj B)
      (w₁ : (pb V.ι).map a ≫ b = 0), a ≫ (latSub w hf hL).incl = tr a₀ ∧
      b ≫ (pb V.ι).map (tr (𝟙 _)) = (pb V.ι).map ((latSub w hf hL).incl ≫ (pf j).map b₀) ∧
      (ShortComplex.mk _ b w₁).ShortExact := by
  haveI : Mono a₀ := h₀.mono_f
  haveI : Epi b₀ := h₀.epi_g
  let a' := latMap w hf (isLat_resSec w A) hL a₀ (by rintro _ ⟨t, rfl⟩; exact ((h.1 _).2 ⟨t, rfl⟩).1)
  let b' := latMap w hf hL (isLat_resSec w B) b₀ fun s hs => (h.2 _).1 ⟨s, hs, rfl⟩
  have ha' : a' ≫ Sub.incl _ = Sub.incl _ ≫ (pf j).map a₀ := rfl
  have hb' : b' ≫ Sub.incl _ = Sub.incl _ ≫ (pf j).map b₀ := rfl
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_mono (Sub.incl _), Category.assoc, hb', reassoc_of% ha', ← Functor.map_comp, w₀, Functor.map_zero,
      comp_zero, zero_comp]
  haveI : Mono a' := mono_of_mono_fac ha'
  have hex : (ShortComplex.mk a' b' w').Exact := DualExact.exact_of_locally _ fun W y hy => ⟨W, le_rfl, hy, fun t ht => by
    have h1 : ((pf j).map b₀).app W ((Sub.incl _).app W t) = 0 := by
      rw [app_app, ← hb', ← app_app]
      exact (congrArg _ ht).trans (map_zero _)
    obtain ⟨u, hu⟩ := (QCoh.exact_app_of_exact_of_mono h₀.exact (j ⁻¹ᵁ W) _).1 h1
    refine ⟨Sub.mkSec _ u fun hx => ?_, Sub.incl_app_injective _ _ hu⟩
    obtain ⟨t', ht'⟩ := (h.1 _).1 ⟨Sub.incl_app_mem _ t hx, by rw [← gen_map, h1, map_zero]⟩
    refine ⟨t', injective_fibre w hf hξ hT (hA.pullback j) hM a₀ ?_⟩
    rw [← ht', ← gen_map]
    exact congrArg _ hu⟩
  have hepi : Epi ((pb V.ι).map b') := epi_pullback _ _ fun W hW t y hy => by
    rw [Scheme.Opens.opensRange_ι] at hW
    by_cases e : y = x
    · subst e
      obtain ⟨s, hs, hs'⟩ := (h.2 _).2 (Sub.incl_app_mem _ t hy)
      obtain ⟨W', hle, hx', s, rfl⟩ := exists_gen_eq w hf hξ hT hM hy s
      refine ⟨W', hle, hx', Sub.mkSec _ s fun _ => hs, Sub.incl_app_injective _ _
        (gen_injective w hf hξ (hB.pullback j) hx' ?_)⟩
      rw [app_app, hb', ← app_app, gen_map, app_resM, gen_res, ← hs']
      rfl
    · obtain ⟨y, rfl⟩ := hV y (hW hy) e
      obtain ⟨W₀, hle, hy', s, hs⟩ := exists_app_eq_of_epi b₀ (V := j ⁻¹ᵁ W) ((Sub.incl _).app W t) hy
      have h2 : j ''ᵁ W₀ ≤ W := (j.image_mono hle).trans (j.image_preimage_le W)
      refine ⟨j ''ᵁ W₀, h2, ⟨y, hy', rfl⟩, Sub.mkSec _ (resM M (j.preimage_image_eq W₀).le s)
        fun h => absurd (j.image_le_opensRange _ h) hx, Sub.incl_app_injective _ _ ?_⟩
      rw [app_resM]
      refine (app_resM b₀ (j.preimage_image_eq W₀).le s).trans ?_
      rw [hs, resM_resM]
      rfl
  have hS : ((ShortComplex.mk a' b' w').map (pb V.ι)).ShortExact :=
    ShortComplex.ShortExact.mk' (exact_pullback _ hex) (mono_pullback_of_isOpenImmersion V.ι a') hepi
  haveI := isIso_latUnit w hf hξ hV hA
  haveI := isIso_latUnit w hf hξ hV hB
  refine ⟨latUnit w hf A ≫ a', (pb V.ι).map b' ≫ inv ((pb V.ι).map (latUnit w hf B)), ?_, ?_, ?_, ?_⟩
  · rw [← Functor.map_comp_assoc, Category.assoc, w', comp_zero, Functor.map_zero, zero_comp]
  · rw [Category.assoc, ha', latUnit_incl_assoc, ← tr_comp, Category.id_comp]
  · rw [← latUnit_incl w hf B, Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, hb']
  · exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := (ShortComplex.mk a' b' w').map (pb V.ι))
      (asIso ((pb V.ι).map (latUnit w hf A))).symm (Iso.refl _)
      (asIso ((pb V.ι).map (latUnit w hf B))).symm (by simp) (by simp)) hS

include hf hξ hT hV in

theorem exists_datum (hx : x ∉ j.opensRange) {O : Type} [CommRing O] {A B A' B' : X.Modules} {α : O →+* End A}
    {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {m n m' n' : ℕ} (hA : IsVB A m) (hB : IsVB B n)
    (hA' : IsVB A' m') (hB' : IsVB B' n') (d₀ : DatumOn α β α' β' r j) (h : HasLattice w d₀) {S : Scheme.{0}}
    {p : S ⟶ V} {q : S ⟶ T} (z : p ≫ V.ι = q ≫ j) : ∃ (d : DatumOn α β α' β' r V.ι) (ψ : _), Agree d d₀ z ψ := by
  obtain ⟨_, l, hρ, h₁, h₂⟩ := h
  have hL := isLat_inLat (R := R) l
  obtain ⟨a, b, w₁, ha, hb, e₁⟩ := exists_seq w hf hξ hT hV hx hA hB d₀.isVB d₀.exact₁ hL h₁
  obtain ⟨u, v, w₂, hu, hv, e₂⟩ := exists_seq w hf hξ hT hV hx hA' hB' d₀.isVB d₀.exact₂ hL h₂
  let N := latSub w hf hL
  let ρ : O → (N.toMod ⟶ N.toMod) := fun c => latMap w hf hL hL (act d₀.ρ c) (hρ c)
  have hρ' (c : O) : ρ c ≫ N.incl = N.incl ≫ (pf j).map (act d₀.ρ c) := rfl
  let ρ₀ : O →+* End N.toMod :=
    { toFun := ρ
      map_one' := show ρ 1 = 𝟙 _ by
        rw [← cancel_mono N.incl, hρ', show act d₀.ρ 1 = 𝟙 _ from map_one d₀.ρ]; simp
      map_mul' := fun c c' => show ρ (c * c') = ρ c' ≫ ρ c by
        rw [← cancel_mono N.incl, hρ', show act d₀.ρ (c * c') = act d₀.ρ c' ≫ act d₀.ρ c from map_mul d₀.ρ c c',
          Category.assoc, hρ', reassoc_of% hρ' c', Functor.map_comp]
      map_zero' := show ρ 0 = (0 : N.toMod ⟶ N.toMod) by
        rw [← cancel_mono N.incl, hρ', show act d₀.ρ 0 = 0 from map_zero d₀.ρ]; simp
      map_add' := fun c c' => show ρ (c + c') = (ρ c + ρ c' : N.toMod ⟶ N.toMod) by
        rw [← cancel_mono N.incl, hρ', show act d₀.ρ (c + c') = act d₀.ρ c + act d₀.ρ c' from map_add d₀.ρ c c',
          Preadditive.add_comp, hρ', hρ', Functor.map_add, Preadditive.comp_add] }
  obtain ⟨e, he⟩ := tr_surjective N.incl
  haveI : IsIso e := isIso_of_tr e fun W hW => he ▸
    ⟨N.incl_app_injective W, fun s => ⟨N.mkSec s fun h => absurd (hW h) hx, rfl⟩⟩
  have ein {F : X.Modules} {σ : O →+* End F} {g : F ⟶ N.toMod} {g₀ : (pb j).obj F ⟶ d₀.D} (hg : g ≫ N.incl = tr g₀)
      (h : IsEquivariant (pullAct σ j) d₀.ρ g₀) : IsEquivariant (pullAct σ V.ι) (pullAct ρ₀ V.ι) ((pb V.ι).map g) := by
    refine IsEquivariant.pullback (fun c => show act σ c ≫ g = g ≫ ρ c from ?_) _
    rw [← cancel_mono N.incl, Category.assoc, Category.assoc, hρ', hg, reassoc_of% hg, comp_tr, ← tr_comp, ← h c,
      act_pullAct]
  have eout {F : X.Modules} {s : ℕ} (hF : IsVB F s) {σ : O →+* End F} {g : (pb V.ι).obj N.toMod ⟶ (pb V.ι).obj F}
      {g₀ : d₀.D ⟶ (pb j).obj F} (hg : g ≫ (pb V.ι).map (tr (𝟙 _)) = (pb V.ι).map (N.incl ≫ (pf j).map g₀))
      (h : IsEquivariant d₀.ρ (pullAct σ j) g₀) : IsEquivariant (pullAct ρ₀ V.ι) (pullAct σ V.ι) g := fun c => by
    haveI := mono_unit (j := j) hF
    haveI := mono_pullback_of_isOpenImmersion V.ι (tr (𝟙 ((pb j).obj F)))
    have h1 : act σ c ≫ tr (𝟙 _) = tr (𝟙 _) ≫ (pf j).map (act (pullAct σ j) c) := by
      rw [comp_tr, ← tr_comp, Category.comp_id, Category.id_comp, act_pullAct]
    rw [← cancel_mono ((pb V.ι).map (tr (𝟙 ((pb j).obj F)))), Category.assoc, Category.assoc, hg, act_pullAct,
      act_pullAct, ← Functor.map_comp, ← Functor.map_comp, h1, Functor.map_comp _ (tr _), reassoc_of% hg,
      ← Functor.map_comp, Category.assoc, ← Functor.map_comp, ← h c, Functor.map_comp (pf j), ← reassoc_of% hρ' c]
    rfl
  have ain {F : X.Modules} {g : F ⟶ N.toMod} {g₀ : (pb j).obj F ⟶ d₀.D} (hg : g ≫ N.incl = tr g₀) :
      (pb p).map ((pb V.ι).map g) ≫ (sqIso z).hom.app _ ≫ (pb q).map e = (sqIso z).hom.app F ≫ (pb q).map g₀ := by
    have h1 : (pb j).map g ≫ e = g₀ := tr_injective (by rw [← comp_tr, he, hg])
    rw [← h1, Functor.map_comp]
    exact (sqIso z).hom.naturality_assoc g _
  have aout {F : X.Modules} {g : (pb V.ι).obj N.toMod ⟶ (pb V.ι).obj F}
      {g₀ : d₀.D ⟶ (pb j).obj F} (hg : g ≫ (pb V.ι).map (tr (𝟙 _)) = (pb V.ι).map (N.incl ≫ (pf j).map g₀)) :
      ((sqIso z).hom.app _ ≫ (pb q).map e) ≫ (pb q).map g₀ = (pb p).map g ≫ (sqIso z).hom.app F := by
    obtain ⟨ε, hε⟩ := tr_surjective (𝟙 ((pf j).obj ((pb j).obj F)))
    have h1 : (pb j).map (tr (𝟙 _)) ≫ ε = 𝟙 _ := tr_injective (by rw [← comp_tr, hε, Category.comp_id])
    have h2 : (pb j).map (N.incl ≫ (pf j).map g₀) ≫ ε = e ≫ g₀ :=
      tr_injective (by rw [← comp_tr, hε, Category.comp_id, tr_comp, he])
    have h3 := (sqIso z).hom.naturality (tr (𝟙 ((pb j).obj F)))
    have h4 := (sqIso z).hom.naturality (N.incl ≫ (pf j).map g₀)
    rw [Functor.comp_map, Functor.comp_map] at h3 h4
    rw [Category.assoc, ← Functor.map_comp, ← h2, Functor.map_comp, ← reassoc_of% h4, ← hg, Functor.map_comp,
      Category.assoc, reassoc_of% h3, ← Functor.map_comp, h1, CategoryTheory.Functor.map_id, Category.comp_id]
  have hr : r = m + n :=
    d₀.isVB.rank_unique (VBExt.isVB_X₂_of_shortExact _ _ m n d₀.exact₁ (hA.pullback j) (hB.pullback j))
  refine ⟨{ D := (pb V.ι).obj N.toMod, ρ := pullAct ρ₀ V.ι, a := (pb V.ι).map a, b := b, u := (pb V.ι).map u, v := v
            w₁ := w₁, w₂ := w₂
            isVB := hr ▸ VBExt.isVB_X₂_of_shortExact _ _ m n e₁ (hA.pullback _) (hB.pullback _)
            exact₁ := e₁, exact₂ := e₂
            equiv_a := ein ha d₀.equiv_a
            equiv_b := eout hB hb d₀.equiv_b
            equiv_u := ein hu d₀.equiv_u
            equiv_v := eout hB' hv d₀.equiv_v },
    (sqIso z).app N.toMod ≪≫ (pb q).mapIso (asIso e), fun c => ?_, ain ha, aout hb, ain hu, aout hv⟩
  refine (ain (g := ρ c) (g₀ := e ≫ act d₀.ρ c) (by rw [tr_comp, he, hρ'])).trans ?_
  rw [Functor.map_comp, ← Category.assoc]
  rfl

end Lattice

theorem exists_punctured {X : Scheme.{0}} [IsIntegral X] [NoetherianSpace X] (hd : topologicalKrullDim X = 1)
    {U : X.Opens} (hU : genericPoint X ∈ U) (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∀ y ∈ V, y ≠ x → y ∈ U := by
  have h : ((U : Set X)ᶜ \ {x}).Finite :=
    (ProperCurve.finite_of_isClosed hd U.isOpen.isClosed_compl (not_not.2 hU)).subset Set.diff_subset
  have hc : IsClosed ((U : Set X)ᶜ \ {x}) := by
    rw [← Set.biUnion_of_singleton ((U : Set X)ᶜ \ {x})]
    exact h.isClosed_biUnion fun y hy => ProperCurve.isClosed_singleton hd (by rintro rfl; exact hy.1 hU)
  exact ⟨⟨_, hc.isOpen_compl⟩, fun h => h.2 rfl, fun y hy e => not_not.1 fun h => hy ⟨h, e⟩⟩

theorem exists_extension (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] [IsIntegral X]
    (hX : IsSmoothProjCurve k X) (O : Type) [CommRing O] (A B A' B' : X.Modules) (α : O →+* End A) (β : O →+* End B)
    (α' : O →+* End A') (β' : O →+* End B') (r a b a' b' : ℕ) (hA : IsVB A a) (hB : IsVB B b) (hA' : IsVB A' a')
    (hB' : IsVB B' b') (U : X.Opens) (hU : genericPoint X ∈ U) (d₀ : DatumOn α β α' β' r U.ι) (h : HasLatticesDvr d₀)
    (x : X) (hx : x ∉ U) : ∃ V : X.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧ ∃ d : DatumOn α β α' β' r V.ι, ∃ ψ,
      Agree (b := X.homOfLE (inf_le_left : V ⊓ U ≤ V)) (c := X.homOfLE (inf_le_right : V ⊓ U ≤ U)) d d₀ (by simp) ψ := by
  haveI := hX.toIsProjCurve.isNoetherian
  haveI := hX.smooth
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  have hne : x ≠ genericPoint X := by rintro rfl; exact hx hU
  obtain ⟨V, hxV, hV⟩ := exists_punctured hX.dim_eq hU x
  refine ⟨V, hxV, hV, ?_⟩
  have hη : U.ι (genericPoint U) = genericPoint X := genericPoint_eq_of_isOpenImmersion U.ι
  have hg := isGerm_fromSpecStalk (genericPoint X)
  let ξ : Sp X.functionField ⟶ U := IsOpenImmersion.lift U.ι (X.fromSpecStalk (genericPoint X)) (by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg.1 U hU trivial)
  have hξ : ξ ≫ U.ι = X.fromSpecStalk (genericPoint X) := IsOpenImmersion.lift_fac _ _ _
  have w : spMap (algebraMap (X.presheaf.stalk x) X.functionField) ≫ X.fromSpecStalk x = ξ ≫ U.ι :=
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).trans hξ.symm
  haveI := hX.isPrincipalIdealRing_stalk x
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) := ⟨fun h0 => by
    have := ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)
    rw [ringKrullDim_stalk_eq_coheight] at this
    have h2 : IsMax x := Order.coheight_eq_zero.1 (by exact_mod_cast this)
    have h1 : x ⤳ genericPoint X := h2 (show x ≤ genericPoint X from genericPoint_specializes x)
    exact hne (h1.antisymm (genericPoint_specializes x)).eq⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField (X.presheaf.stalk x)) := IsAlgClosed.of_ringEquiv k _
    (residueFieldIsoBase (strHom k X) x (ProperCurve.isClosed_singleton hX.dim_eq hne)).commRingCatIsoToRingEquiv.symm
  refine exists_datum w (isGerm_fromSpecStalk x) (IsGerm.of_comp (by rw [hξ, hη]; exact hg)) (fun W₀ h₀ => ?_)
    (by rwa [Scheme.Opens.opensRange_ι]) (by rwa [Scheme.Opens.opensRange_ι]) hA hB hA' hB' d₀ (h _ _ _ _ w) _
  obtain ⟨W, hxW, hW⟩ := exists_punctured hX.dim_eq (U := U.ι ''ᵁ W₀) ⟨_, h₀, hη⟩ x
  refine ⟨W, hxW, fun y hy => ?_⟩
  rw [← U.ι.preimage_image_eq W₀]
  exact hW _ hy fun e => hx (e ▸ y.2)

end GlobalTheory.LatticeExt
