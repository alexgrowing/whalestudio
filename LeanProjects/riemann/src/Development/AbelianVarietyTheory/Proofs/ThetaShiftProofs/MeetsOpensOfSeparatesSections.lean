import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatchCoord

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleSpan GlobalTheory.ThetaScalar

variable {F : Type} [Field F] {X X' Y : Scheme.{0}} {J : Type*}

section Values

abbrev pt (F : Type) [Field F] : Sp F := IsLocalRing.closedPoint F

theorem mem_of_le {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : x (pt F) ∈ U := (top_le_iff_mem x U _).1 h

theorem le_of_mem {x : Sp F ⟶ X} {U : X.Opens} (h : x (pt F) ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := (top_le_iff_mem x U _).2 h

variable {x : Sp F ⟶ X} {U V : X.Opens}

def valHom (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : valF x U a = valHom h a := dif_pos h

theorem valF_mul (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valF x U (a * b) = valF x U a * valF x U b := by
  simp only [valF_eq h, map_mul]

theorem valF_add (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valF x U (a + b) = valF x U a + valF x U b := by
  simp only [valF_eq h, map_add]

theorem valF_sub (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF_eq h, map_sub]

theorem valF_one' (h : ⊤ ≤ x ⁻¹ᵁ U) : valF x U 1 = 1 := by simp only [valF_eq h, map_one]

theorem valF_zero' (h : ⊤ ≤ x ⁻¹ᵁ U) : valF x U 0 = 0 := by simp only [valF_eq h, map_zero]

theorem stk_valF (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : toStk (pt F) (valF x U a) = gs x (pt F) U a :=
  toStk_valF_gs x U _ (mem_of_le h) a

theorem valF_res (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V (resG X e a) = valF x U a :=
  (toStk (pt F)).injective ((stk_valF h _).trans ((gs_res x _ e (mem_of_le h) a).trans
    (stk_valF (le_of_mem (e (mem_of_le h))) a).symm))

theorem valF_appLE (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) :
    valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a :=
  (toStk (pt F)).injective ((stk_valF h _).trans ((gs_appLE f W U e x _ (mem_of_le h) a).trans
    (stk_valF (x := x ≫ f) (le_of_mem (e (mem_of_le h))) a).symm))

theorem valF_ne_zero_iff (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  rw [top_le_iff_mem x _ (pt F), ← isUnit_gs_iff x _ U (mem_of_le h), ← stk_valF h]
  exact ⟨fun e => (Ne.isUnit e).map _, fun u e => by rw [e, map_zero] at u; exact not_isUnit_zero u⟩

theorem valF_sec_ne_zero_iff {H : LB X} (t : H.Sec) {k : H.ι} (h : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U k) (t.f k) ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ nonzeroLocus t := by
  rw [valF_ne_zero_iff h, top_le_iff_mem x _ (pt F), top_le_iff_mem x _ (pt F),
    mem_nonzeroLocus_iff_gs t x _ (mem_of_le h), isUnit_gs_iff x _ _ (mem_of_le h)]

theorem valF_ratio {H : LB X} {s t : H.Sec} {r : Γ(X, nonzeroLocus t)} (hr : IsRatio s t r) {k : H.ι}
    (ht : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus t) (h : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U k) (s.f k) = valF x _ r * valF x (H.U k) (t.f k) :=
  (toStk (pt F)).injective (by
    rw [map_mul, stk_valF h, stk_valF h, stk_valF ht]
    exact hr.gs x _ (mem_of_le ht) (mem_of_le h))

end Values

section Dense

def MeetsOpens (x : J → (Sp F ⟶ X)) : Prop := ∀ (U : X.Opens) (y : X), y ∈ U → ∃ j, ⊤ ≤ x j ⁻¹ᵁ U

variable {x : J → (Sp F ⟶ X)} {x' : J → (Sp F ⟶ X')}

theorem MeetsOpens.fn_ext [IsReduced X] (hx : MeetsOpens x) {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ j, ⊤ ≤ x j ⁻¹ᵁ U → valF (x j) U a = valF (x j) U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨j, hj⟩ := hx _ y hy
  have hU : ⊤ ≤ x j ⁻¹ᵁ U := le_of_mem (X.basicOpen_le _ (mem_of_le hj))
  exact absurd (by rw [valF_sub hU, h j hU, sub_self]) ((valF_ne_zero_iff hU _).2 hj)

theorem MeetsOpens.hom_ext_of_open [IsReduced X] [X'.IsSeparated] (hx : MeetsOpens x) (u : Y ⟶ X)
    [IsOpenImmersion u] {f g : Y ⟶ X'} (h : ∀ j (y : Sp F ⟶ Y), y ≫ u = x j → y ≫ f = y ≫ g) : f = g := by
  have : IsReduced Y := isReduced_of_isOpenImmersion u
  suffices IsDominant (equalizer.ι f g) from ext_of_isDominant (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨dense_iff_inter_open.2 ?_⟩
  rintro U hU ⟨y₀, hy₀⟩
  obtain ⟨j, hj⟩ := hx (u ''ᵁ ⟨U, hU⟩) (u y₀) ⟨y₀, hy₀, rfl⟩
  obtain ⟨y₁, hy₁, e⟩ := mem_of_le hj
  have hr : Set.range (x j) ⊆ Set.range u := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, -, hb⟩ := hj (Set.mem_univ a)
    exact ⟨b, hb⟩
  have e₁ := IsOpenImmersion.lift_fac u (x j) hr
  refine ⟨y₁, hy₁, equalizer.lift _ (h j _ e₁) (pt F), ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
  refine u.isOpenEmbedding.injective ?_
  rw [← Scheme.Hom.comp_apply, e₁]
  exact e.symm

theorem MeetsOpens.hom_ext [IsReduced X] [X'.IsSeparated] (hx : MeetsOpens x) {f g : X ⟶ X'}
    (h : ∀ j, x j ≫ f = x j ≫ g) : f = g :=
  hx.hom_ext_of_open (𝟙 X) fun j y e => by rw [Category.comp_id] at e; rw [e, h]

theorem MeetsOpens.exists_fn [IsReduced X] (hx : MeetsOpens x) (W : X.Opens) (v : J → F) {K : Type}
    (a b : K → Γ(X, W)) (hb : ∀ y ∈ W, ∃ k, y ∈ X.basicOpen (b k))
    (h : ∀ j k, ⊤ ≤ x j ⁻¹ᵁ W → valF (x j) W (a k) = v j * valF (x j) W (b k)) :
    ∃ w : Γ(X, W), ∀ j, ⊤ ≤ x j ⁻¹ᵁ W → valF (x j) W w = v j := by
  have hu : ∀ k, IsUnit (resG X (X.basicOpen_le (b k)) (b k)) := fun k =>
    X.toRingedSpace.isUnit_res_basicOpen (b k)
  obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X, X.basicOpen (b k)), ∀ k j, ⊤ ≤ x j ⁻¹ᵁ X.basicOpen (b k) →
      valF (x j) _ (u k) = v j := by
    refine ⟨fun k => resG X (X.basicOpen_le (b k)) (a k) * ((hu k).unit⁻¹).val, fun k j hj => ?_⟩
    have hW : ⊤ ≤ x j ⁻¹ᵁ W := le_of_mem (X.basicOpen_le _ (mem_of_le hj))
    rw [valF_mul hj, valF_res _ hj, h j k hW, ← valF_res (X.basicOpen_le (b k)) hj (b k), _root_.mul_assoc,
      ← valF_mul hj,
      IsUnit.mul_val_inv, valF_one' hj, _root_.mul_one]
  obtain ⟨w, hw, -⟩ := X.sheaf.existsUnique_gluing' (fun k => X.basicOpen (b k)) W
    (fun k => homOfLE (X.basicOpen_le (b k))) (fun y hy => Opens.mem_iSup.2 (hb y hy)) u
    (fun k l => hx.fn_ext (U := X.basicOpen (b k) ⊓ X.basicOpen (b l)) fun j hj =>
      ((valF_res inf_le_left hj _).trans (hu k j (le_of_mem (mem_of_le hj).1))).trans
        ((valF_res inf_le_right hj _).trans (hu l j (le_of_mem (mem_of_le hj).2))).symm)
  refine ⟨w, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := hb _ (mem_of_le hj)
  rw [← hu k j (le_of_mem hk), ← hw k]
  exact (valF_res (X.basicOpen_le (b k)) (le_of_mem hk) w).symm

theorem comp_fromSpec (U : X.Opens) {D : X'.Opens} (hD : IsAffineOpen D) (r : Γ(X', D) →+* Γ(X, U))
    (y : Sp F ⟶ U.toScheme) (q : Sp F ⟶ X') (hy : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ D)
    (h : ∀ φ, valF (y ≫ U.ι) U (r φ) = valF q D φ) :
    y ≫ U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) ≫ hD.fromSpec = q := by
  have e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = q.appLE D ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    ext φ
    have := h φ
    rw [valF_eq hy, valF_eq hq] at this
    exact this
  have e2 : (isAffineOpen_top (Sp F)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy) := by
    rw [IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp]
    congr 2
    rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have : IsIso (isAffineOpen_top (Sp F)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top (Sp F)).fromSpec, ← hD.SpecMap_appLE_fromSpec q _ hq, ← e1,
    reassoc_of% e2, Spec.map_comp_assoc]

theorem MeetsOpens.exists_hom [IsReduced X] [X'.IsSeparated] (hx : MeetsOpens x) {K : Type} (U : K → X.Opens)
    (D : K → X'.Opens) (hU : ⨆ k, U k = ⊤) (hD : ∀ k, IsAffineOpen (D k))
    (hm : ∀ k j, ⊤ ≤ x j ⁻¹ᵁ U k → ⊤ ≤ x' j ⁻¹ᵁ D k)
    (h : ∀ k (φ : Γ(X', D k)), ∃ ρ : Γ(X, U k), ∀ j, ⊤ ≤ x j ⁻¹ᵁ U k → valF (x j) _ ρ = valF (x' j) _ φ) :
    ∃ β : X ⟶ X', ∀ j, x j ≫ β = x' j := by
  choose r hr using h
  have loc : ∀ k, ∃ m : (U k).toScheme ⟶ X', ∀ j (z : Sp F ⟶ (U k).toScheme), z ≫ (U k).ι = x j → z ≫ m = x' j :=
    fun k => by
    let ρ : Γ(X', D k) →+* Γ(X, U k) :=
      { toFun := r k
        map_one' := hx.fn_ext fun j hj => by rw [hr k _ j hj, valF_one' hj, valF_one' (hm k j hj)]
        map_mul' := fun a b => hx.fn_ext fun j hj => by
          rw [hr k _ j hj, valF_mul hj, valF_mul (hm k j hj), hr k _ j hj, hr k _ j hj]
        map_zero' := hx.fn_ext fun j hj => by rw [hr k _ j hj, valF_zero' hj, valF_zero' (hm k j hj)]
        map_add' := fun a b => hx.fn_ext fun j hj => by
          rw [hr k _ j hj, valF_add hj, valF_add (hm k j hj), hr k _ j hj, hr k _ j hj] }
    refine ⟨(U k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ) ≫ (hD k).fromSpec, fun j z hz => ?_⟩
    have hz' : ⊤ ≤ (z ≫ (U k).ι) ⁻¹ᵁ U k := le_of_mem (z (pt F)).2
    have hj : ⊤ ≤ x j ⁻¹ᵁ U k := hz ▸ hz'
    exact comp_fromSpec (U k) (hD k) ρ z _ hz' (hm k j hj) fun φ => by rw [hz]; exact hr k φ j hj
  choose m hm using loc
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  have hc : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ m k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ m l := fun k l =>
    hx.hom_ext_of_open (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k) fun j y e => by
      refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
      refine (hm k j _ ((Category.assoc _ _ _).trans e)).trans (hm l j _ ?_).symm
      rw [pullback.condition] at e
      exact (Category.assoc _ _ _).trans e
  refine ⟨𝒰.glueMorphisms m hc, fun j => ?_⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ (x j (pt F))))
  have hr : Set.range (x j) ⊆ Set.range (U k).ι := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact le_of_mem hk (Set.mem_univ a)
  have e := IsOpenImmersion.lift_fac (U k).ι (x j) hr
  have e2 : (U k).ι ≫ 𝒰.glueMorphisms m hc = m k := 𝒰.ι_glueMorphisms m hc k
  refine Eq.trans ?_ (hm k j _ e)
  rw [← e2, ← Category.assoc, e]

end Dense

section Embed

variable {x : J → (Sp F ⟶ X)} {x' : J → (Sp F ⟶ X')}

theorem MeetsOpens.exists_hom_of_embedsBy [IsReduced X] [X'.IsSeparated] (hx : MeetsOpens x) {S : Scheme.{0}}
    (f : X ⟶ S) (f' : X' ⟶ S) (hf : ∀ j, x j ≫ f = x' j ≫ f') {H : LB X} {H' : LB X'} {I₁ : Type}
    (t : I₁ → H.Sec) (t' : I₁ → H'.Sec) (hcov : ⨆ i, nonzeroLocus (t i) = ⊤) (he : EmbedsBy f' t')
    (h : ∀ j, ∃ k k', ⊤ ≤ x j ⁻¹ᵁ H.U k ∧ ⊤ ≤ x' j ⁻¹ᵁ H'.U k' ∧ ∃ (c c' : F) (v : I₁ → F), c ≠ 0 ∧ c' ≠ 0 ∧
      ∀ i, valF (x j) _ ((t i).f k) = v i * c ∧ valF (x' j) _ ((t' i).f k') = v i * c') :
    ∃ β : X ⟶ X', ∀ j, x j ≫ β = x' j := by
  choose k k' hk hk' c c' v hc hc' hv using h
  choose haff r' hr' hsurj using he.2
  choose r hr using fun i l => exists_isRatio (t l) (t i)
  have hm : ∀ i j, ⊤ ≤ x j ⁻¹ᵁ nonzeroLocus (t i) → v j i ≠ 0 ∧ ⊤ ≤ x' j ⁻¹ᵁ nonzeroLocus (t' i) := fun i j hj => by
    have e := (valF_sec_ne_zero_iff (t i) (hk j)).2 hj
    rw [(hv j i).1] at e
    refine ⟨left_ne_zero_of_mul e, (valF_sec_ne_zero_iff (t' i) (hk' j)).1 ?_⟩
    rw [(hv j i).2]
    exact mul_ne_zero (left_ne_zero_of_mul e) (hc' j)
  refine hx.exists_hom (fun i => nonzeroLocus (t i)) (fun i => nonzeroLocus (t' i)) hcov haff
    (fun i j hj => (hm i j hj).2) fun i φ => ?_
  obtain ⟨p, rfl⟩ := hsurj i φ
  refine ⟨MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (t i)) le_top).hom (r i) p, fun j hj => ?_⟩
  obtain ⟨hv0, hj'⟩ := hm i j hj
  induction p using MvPolynomial.induction_on with
  | C b =>
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact (valF_appLE f ⊤ le_top hj b).trans ((congrArg (valF · ⊤ b) (hf j)).trans (valF_appLE f' ⊤ le_top hj' b).symm)
  | add p q hp hq => rw [map_add, map_add, valF_add hj, valF_add hj', hp, hq]
  | mul_X p l hp =>
    rw [map_mul, map_mul, valF_mul hj, valF_mul hj', hp, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    congr 1
    have e := valF_ratio (hr i l) hj (hk j)
    have e' := valF_ratio (hr' i l) hj' (hk' j)
    rw [(hv j l).1, (hv j i).1, ← _root_.mul_assoc] at e
    rw [(hv j l).2, (hv j i).2, ← _root_.mul_assoc] at e'
    exact mul_right_cancel₀ hv0 ((mul_right_cancel₀ (hc j) e).symm.trans (mul_right_cancel₀ (hc' j) e'))

variable {L : LB X} {L' : LB X'}

abbrev chart (L : LB X) (a : L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) fun _ => a

theorem le_chart {a : L.ι} : L.U a ≤ chart L a := fun _ h => Set.mem_iInter.2 fun _ => h

theorem top_le_chart {y : Sp F ⟶ X} {a : L.ι} (h : ⊤ ≤ y ⁻¹ᵁ L.U a) : ⊤ ≤ y ⁻¹ᵁ chart L a :=
  le_of_mem (le_chart (mem_of_le h))

def SeparatesSections (L : LB X) (x : J → (Sp F ⟶ X)) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ u : H0 L m, (∀ j a, ⊤ ≤ x j ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) a →
    valF (x j) (LB.wchart L (fun _ : Fin 1 => 𝟙 X) a) (u.f a) = 0) → ∀ a, u.f a = 0

theorem SeparatesSections.meetsOpens (hL : IsAmpleLB L) (h : SeparatesSections L x) : MeetsOpens x := by
  intro U y hy
  by_contra hne
  obtain ⟨n, hn, s, hs, hle, -⟩ := hL.exists_affine_le hy
  let a : ChartPull (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) (lbPow L n) (𝟙 X) :=
    { idx := fun j _ => j 0
      le := fun j y hy => mem_powChart.2 (Set.mem_iInter.1 hy 0)
      g := fun y j j' hj hj' => by
        refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
          (Eq.trans ?_ (gm_lbPow_g n (𝟙 X) y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
            (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
        rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast] }
  have e : nonzeroLocus (chartSec a s) = nonzeroLocus s := nonzeroLocus_chartSec_id a s fun _ J hJ =>
    ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩
  have h0 := h n hn (chartSec a s) fun j b hb => by
    by_contra h₁
    exact hne ⟨j, le_of_mem (hle (e.le (mem_of_le ((valF_sec_ne_zero_iff (chartSec a s) (k := b) hb).1 h₁))))⟩
  obtain ⟨b, hb⟩ := Opens.mem_iSup.1 (e.ge hs)
  rw [h0 b] at hb
  exact (Scheme.basicOpen_zero _ _).le hb

theorem MeetsOpens.separatesSections [IsReduced X] (hx : MeetsOpens x) (L : LB X) : SeparatesSections L x :=
  fun _ _ _ h a => hx.fn_ext fun j hj => (h j a hj).trans (valF_zero' hj).symm

def IsFrameAt (L : LB X) (y : Sp F ⟶ X) (τ : L.ι → F) : Prop :=
  (∀ a, ⊤ ≤ y ⁻¹ᵁ L.U a → τ a ≠ 0) ∧ ∀ a b, ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b →
    τ a = valF y (L.U a ⊓ L.U b) (L.g a b).val * τ b

def HasValueAt {N : ℕ} (s : H0 L N) (y : Sp F ⟶ X) (τ : L.ι → F) (c : F) : Prop :=
  ∀ a, ⊤ ≤ y ⁻¹ᵁ L.U a → valF y (chart L a) (s.f fun _ => a) = c * τ a ^ N

theorem stk_valF_g {y : Sp F ⟶ X} {a b : L.ι} (ha : ⊤ ≤ y ⁻¹ᵁ L.U a) (hb : ⊤ ≤ y ⁻¹ᵁ L.U b) :
    toStk (pt F) (valF y (L.U a ⊓ L.U b) (L.g a b).val) = (gm y (pt F) _ (L.g a b)).val :=
  toStk_valF y (L.U a ⊓ L.U b) _ ⟨mem_of_le ha, mem_of_le hb⟩ _

theorem exists_isFrameAt (hL : L.IsLB) (y : Sp F ⟶ X) {a : L.ι} (ha : ⊤ ≤ y ⁻¹ᵁ L.U a) {c : F} (hc : c ≠ 0) :
    ∃ τ, IsFrameAt L y τ ∧ τ a = c := by
  refine ⟨fun b => valF y (L.U b ⊓ L.U a) (L.g b a).val * c, ⟨fun b hb => mul_ne_zero (fun e => ?_) hc,
    fun b b' hb hb' => ?_⟩, ?_⟩
  · have := stk_valF_g hb ha
    rw [e, map_zero] at this
    exact Units.ne_zero _ this.symm
  · rw [← _root_.mul_assoc]
    refine congrArg (· * c) ((toStk (pt F)).injective ?_)
    rw [map_mul, stk_valF_g hb ha, stk_valF_g hb hb', stk_valF_g hb' ha, ← Units.val_mul,
      gm_cocycle hL y _ (mem_of_le hb) (mem_of_le hb') (mem_of_le ha)]
  · refine (congrArg (· * c) ((toStk (pt F)).injective (a₂ := 1) ?_)).trans (_root_.one_mul c)
    rw [stk_valF_g ha ha, gm_self hL y _ (mem_of_le ha), map_one, Units.val_one]

theorem HasValueAt.of_chart {N : ℕ} {s : H0 L N} {y : Sp F ⟶ X} {τ : L.ι → F} (hτ : IsFrameAt L y τ) {c : F}
    {b : L.ι} (hb : ⊤ ≤ y ⁻¹ᵁ L.U b) (h : valF y (chart L b) (s.f fun _ => b) = c * τ b ^ N) :
    HasValueAt s y τ c := fun a ha => by
  rw [hτ.2 a b ha hb, mul_pow, mul_left_comm, ← h]
  refine (toStk (pt F)).injective ?_
  rw [map_mul, map_pow, stk_valF_g ha hb]
  refine (stk_valF (top_le_chart ha) _).trans ((sec_trans s y _ (le_chart (mem_of_le ha))
    (le_chart (mem_of_le hb))).trans (congrArg₂ (· * ·) ?_ (stk_valF (top_le_chart hb) _).symm))
  rw [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]

def genCoord {y : Sp F ⟶ X} (τ : LB.Gen (L.pull y)) (a : L.ι) : F := valF (𝟙 (Sp F)) _ (τ.s fun _ => a).val

theorem isFrameAt_genCoord {y : Sp F ⟶ X} {τ : LB.Gen (L.pull y)} (hτ : τ.IsGen) : IsFrameAt L y (genCoord τ) := by
  have val : ∀ a, ⊤ ≤ y ⁻¹ᵁ L.U a → toStk (pt F) (genCoord τ a) = (gm (𝟙 _) (pt F) _ (τ.s fun _ => a)).val :=
    fun a ha => toStk_valF _ _ _ (mem_pull.2 (mem_of_le ha)) _
  refine ⟨fun a ha e => ?_, fun a b ha hb => (toStk (pt F)).injective ?_⟩
  · have := val a ha
    rw [e, map_zero] at this
    exact Units.ne_zero _ this.symm
  · rw [map_mul, val a ha, val b hb, stk_valF_g ha hb, ← Units.val_mul]
    refine congrArg Units.val ((gen_trans hτ (𝟙 _) (pt F) (mem_pull.2 (mem_of_le ha))
      (mem_pull.2 (mem_of_le hb))).trans (congrArg (· * _) ?_))
    rw [trF, Fintype.prod_unique, Category.id_comp, zpow_one]

theorem MeetsOpens.exists_lbIso [IsReduced X] (hx : MeetsOpens x) (β : X ⟶ X') (hβ : ∀ j, x j ≫ β = x' j)
    {τ : J → L.ι → F} {τ' : J → L'.ι → F} (hτ : ∀ j, IsFrameAt L (x j) (τ j)) (hτ' : ∀ j, IsFrameAt L' (x' j) (τ' j))
    {N M : ℕ} (hM : M = N + 1) {I₁ κ : Type} (s : I₁ → H0 L N) (s' : I₁ → H0 L' N) (t : κ → H0 L M) (t' : κ → H0 L' M)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (hs' : ⨆ i, nonzeroLocus (s' i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) (ht' : ⨆ i, nonzeroLocus (t' i) = ⊤)
    (vs : ∀ i j, ∃ c, HasValueAt (s i) (x j) (τ j) c ∧ HasValueAt (s' i) (x' j) (τ' j) c)
    (vt : ∀ i j, ∃ c, HasValueAt (t i) (x j) (τ j) c ∧ HasValueAt (t' i) (x' j) (τ' j) c) :
    ∃ w : LB.Iso L (L'.pull β), w.IsGen ∧ ∀ j a a', ⊤ ≤ x j ⁻¹ᵁ L.U a → ⊤ ≤ x' j ⁻¹ᵁ L'.U a' →
      valF (x j) _ (w.s (fun _ => a', a)).val * τ j a = τ' j a' := by
  subst hM
  choose c hc hc' using vs
  choose d hd hd' using vt
  let W : L'.ι → L.ι → X.Opens := fun a' a => (L'.pull β).U (fun _ => a') ⊓ L.U a
  have mem : ∀ {j a' a}, ⊤ ≤ x j ⁻¹ᵁ W a' a ↔ ⊤ ≤ x j ⁻¹ᵁ L.U a ∧ ⊤ ≤ x' j ⁻¹ᵁ L'.U a' := fun {j a' a} => by
    rw [← hβ]
    exact ⟨fun h => ⟨le_of_mem (mem_of_le h).2, le_of_mem (mem_pull.1 (mem_of_le h).1)⟩,
      fun h => le_of_mem ⟨mem_pull.2 (mem_of_le h.2), mem_of_le h.1⟩⟩
  have loc : ∀ a' a, ∃ w : Γ(X, W a' a)ˣ, ∀ j, ⊤ ≤ x j ⁻¹ᵁ W a' a → valF (x j) _ w.val = τ' j a' / τ j a := by
    intro a' a
    have l : W a' a ≤ chart L a := inf_le_right.trans le_chart
    have l' : W a' a ≤ β ⁻¹ᵁ chart L' a' := fun _ h => le_chart (mem_pull.1 h.1)
    let A : ∀ {n : ℕ}, H0 L n → Γ(X, W a' a) := fun u => resG X l (u.f fun _ => a)
    let B : ∀ {n : ℕ}, H0 L' n → Γ(X, W a' a) := fun u => (β.appLE _ _ l').hom (u.f fun _ => a')
    have vA : ∀ {n : ℕ} {u : H0 L n} {j e}, HasValueAt u (x j) (τ j) e → ⊤ ≤ x j ⁻¹ᵁ W a' a →
        valF (x j) _ (A u) = e * τ j a ^ n := fun h hj => (valF_res l hj _).trans (h a (mem.1 hj).1)
    have vB : ∀ {n : ℕ} {u : H0 L' n} {j e}, HasValueAt u (x' j) (τ' j) e → ⊤ ≤ x j ⁻¹ᵁ W a' a →
        valF (x j) _ (B u) = e * τ' j a' ^ n := fun h hj =>
      (valF_appLE β _ l' hj _).trans (by rw [hβ]; exact h a' (mem.1 hj).2)
    have cov : ∀ {n n' : ℕ} {I₁ κ : Type} (u : I₁ → H0 L n) (u' : κ → H0 L' n'), ⨆ i, nonzeroLocus (u i) = ⊤ →
        ⨆ i, nonzeroLocus (u' i) = ⊤ → ∀ y ∈ W a' a, ∃ p : I₁ × κ, y ∈ X.basicOpen (A (u p.1) * B (u' p.2)) :=
      fun u u' hu hu' y hy => by
        obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ y))
        obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hu'.ge (Set.mem_univ (β y)))
        refine ⟨(i, k), (isUnit_gs_iff (𝟙 X) y _ hy _).1 ?_⟩
        refine (congrArg IsUnit ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y l hy _)
          ((gs_appLE β _ _ l' (𝟙 X) y hy _).trans (congrArg (gs · y _ _) (Category.id_comp β)))))).mpr ?_
        exact ((mem_nonzeroLocus_iff_gs (u i) (𝟙 X) y (k := fun _ => a) (l hy)).1 hi).mul
          ((mem_nonzeroLocus_iff_gs (u' k) β y (k := fun _ => a') (l' hy)).1 hk)
    obtain ⟨w, hw⟩ := hx.exists_fn (W a' a) (fun j => τ' j a' / τ j a) (fun p : κ × I₁ => A (s p.2) * B (t' p.1))
      (fun p => A (t p.1) * B (s' p.2)) (cov t s' ht hs') fun j p hj => by
        have := (hτ j).1 a (mem.1 hj).1
        rw [valF_mul hj, valF_mul hj, vA (hc _ j) hj, vA (hd _ j) hj, vB (hc' _ j) hj, vB (hd' _ j) hj]
        field_simp
        ring
    obtain ⟨w', hw'⟩ := hx.exists_fn (W a' a) (fun j => τ j a / τ' j a') (fun p : I₁ × κ => A (t p.2) * B (s' p.1))
      (fun p => A (s p.1) * B (t' p.2)) (cov s t' hs ht') fun j p hj => by
        have := (hτ' j).1 a' (mem.1 hj).2
        rw [valF_mul hj, valF_mul hj, vA (hc _ j) hj, vA (hd _ j) hj, vB (hc' _ j) hj, vB (hd' _ j) hj]
        field_simp
        ring
    have e : w * w' = 1 := hx.fn_ext fun j hj => by
      have := (hτ j).1 a (mem.1 hj).1
      have := (hτ' j).1 a' (mem.1 hj).2
      rw [valF_mul hj, hw j hj, hw' j hj, valF_one' hj]
      field_simp
    exact ⟨⟨w, w', e, (mul_comm _ _).trans e⟩, hw⟩
  choose w hw using loc
  refine ⟨⟨fun p => w (p.1 PUnit.unit) p.2⟩, ?_, fun j a a' ha ha' => ?_⟩
  · rintro ⟨I, a⟩ ⟨I', b⟩
    obtain ⟨a', rfl⟩ : ∃ a', I = fun _ => a' := ⟨I PUnit.unit, rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b', I' = fun _ => b' := ⟨I' PUnit.unit, rfl⟩
    refine Units.ext (hx.fn_ext (U := W a' a ⊓ W b' b) fun j hj => ?_)
    have h₁ : ⊤ ≤ x j ⁻¹ᵁ W a' a := le_of_mem (mem_of_le hj).1
    have h₂ : ⊤ ≤ x j ⁻¹ᵁ W b' b := le_of_mem (mem_of_le hj).2
    have g : valF (x j) (W a' a ⊓ W b' b) ((LB.div (L'.pull β) L).g (fun _ => a', a) (fun _ => b', b)).val *
        valF (x j) (L.U a ⊓ L.U b) (L.g a b).val = valF (x' j) (L'.U a' ⊓ L'.U b') (L'.g a' b').val := by
      refine (toStk (pt F)).injective ?_
      rw [map_mul, stk_valF_g (mem.1 h₁).1 (mem.1 h₂).1,
        stk_valF_g (mem.1 h₁).2 (mem.1 h₂).2, ← hβ]
      refine (congrArg (· * _) (toStk_valF (x j) (W a' a ⊓ W b' b) _ (mem_of_le hj) _)).trans ?_
      exact congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (gm_div_g (x j) (pt F) a' b' a b
        (mem_pull.1 (mem_of_le h₁).1) (mem_pull.1 (mem_of_le h₂).1) (mem_of_le h₁).2 (mem_of_le h₂).2))
    refine ((valF_res inf_le_left hj _).trans (hw a' a j h₁)).trans (Eq.trans ?_ ((valF_mul hj _ _).trans
      (congrArg (_ * ·) ((valF_res inf_le_right hj _).trans (hw b' b j h₂)))).symm)
    have n₁ := (hτ j).1 a (mem.1 h₁).1
    have n₂ := (hτ j).1 b (mem.1 h₂).1
    rw [div_eq_iff n₁, (hτ' j).2 a' b' (mem.1 h₁).2 (mem.1 h₂).2, ← g, (hτ j).2 a b (mem.1 h₁).1 (mem.1 h₂).1]
    field_simp
  · exact (congrArg (· * _) (hw a' a j (mem.2 ⟨ha, ha'⟩))).trans (div_mul_cancel₀ _ ((hτ j).1 a ha))

end Embed

section Abelian

variable (P P' : PolAV (Spec (CommRingCat.of F)))

theorem isSeparated_left : P.A.left.IsSeparated :=
  have := P.isAb.proper
  ⟨by rw [← terminal.comp_from P.A.hom]; infer_instance⟩

theorem meetsOpens_of_separatesSections {x : J → (Sp F ⟶ P.A.left)} (h : SeparatesSections P.L x) : MeetsOpens x :=
  h.meetsOpens (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample)

theorem hom_ext_of_separatesSections {x : J → (baseOver (Spec (CommRingCat.of F)) ⟶ P.A)}
    (h : SeparatesSections (F := F) P.L fun j => (x j).left) {f g : P.A ⟶ P'.A} (e : ∀ j, x j ≫ f = x j ≫ g) :
    f = g :=
  have := isIntegral_left_of_isAbelianScheme_field P.A P.isAb
  have := isSeparated_left P'
  Over.OverMorphism.ext ((meetsOpens_of_separatesSections P h).hom_ext fun j => congrArg CommaMorphism.left (e j))

variable {P P'} {x : J → (baseOver (Spec (CommRingCat.of F)) ⟶ P.A)}
  {x' : J → (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A)} {τ : J → P.L.ι → F} {τ' : J → P'.L.ι → F}

theorem exists_over_hom (hτ : ∀ j, IsFrameAt (F := F) P.L (x j).left (τ j))
    (hτ' : ∀ j, IsFrameAt (F := F) P'.L (x' j).left (τ' j)) {N : ℕ} {I : Type} (s : I → H0 P.L N)
    (s' : I → H0 P'.L N) (hs : EmbedsBy P.A.hom s) (hs' : EmbedsBy P'.A.hom s')
    (vs : ∀ i j, ∃ c, HasValueAt (F := F) (s i) (x j).left (τ j) c ∧ HasValueAt (F := F) (s' i) (x' j).left (τ' j) c)
    (dense : SeparatesSections (F := F) P.L fun j => (x j).left) : ∃ β : P.A ⟶ P'.A, ∀ j, x j ≫ β = x' j := by
  have := isIntegral_left_of_isAbelianScheme_field P.A P.isAb
  have := isSeparated_left P'
  have hx := meetsOpens_of_separatesSections P dense
  have hf : ∀ j, (x j).left ≫ P.A.hom = (x' j).left ≫ P'.A.hom := fun j => (Over.w (x j)).trans (Over.w (x' j)).symm
  choose c hc hc' using vs
  obtain ⟨β, hβ⟩ := hx.exists_hom_of_embedsBy (x' := fun j => (x' j).left) P.A.hom P'.A.hom hf s s' hs.1 hs'
    fun j => by
      obtain ⟨a, ha⟩ := exists_chart P.isLB ((show Sp F ⟶ _ from (x j).left) (pt F))
      obtain ⟨a', ha'⟩ := exists_chart P'.isLB ((show Sp F ⟶ _ from (x' j).left) (pt F))
      have hb := le_of_mem ha
      have hb' := le_of_mem ha'
      exact ⟨fun _ => a, fun _ => a', top_le_chart hb, top_le_chart hb', τ j a ^ N, τ' j a' ^ N, fun i => c i j,
        pow_ne_zero _ ((hτ j).1 a hb), pow_ne_zero _ ((hτ' j).1 a' hb'), fun i => ⟨hc i j a hb, hc' i j a' hb'⟩⟩
  have hw : β ≫ P'.A.hom = P.A.hom := hx.hom_ext fun j =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P'.A.hom) (hβ j)).trans (hf j).symm)
  exact ⟨Over.homMk β hw, fun j => Over.OverMorphism.ext (hβ j)⟩

theorem exists_iso_of_frames (hA : AmpleSt) {j₀ : J} (h₀ : x j₀ = 1) (h₀' : x' j₀ = 1)
    (hτ : ∀ j, IsFrameAt (F := F) P.L (x j).left (τ j)) (hτ' : ∀ j, IsFrameAt (F := F) P'.L (x' j).left (τ' j))
    {N M : ℕ} (hN : 4 ≤ N) (hM : M = N + 1) {I K : Type} [Fintype I] [Fintype K]
    (s : I → H0 P.L N) (s' : I → H0 P'.L N) (t : K → H0 P.L M) (t' : K → H0 P'.L M)
    (hs : ∀ u, InSpan P.A.hom s u) (hs' : ∀ u, InSpan P'.A.hom s' u)
    (ht : ∀ u, InSpan P.A.hom t u) (ht' : ∀ u, InSpan P'.A.hom t' u)
    (vs : ∀ i j, ∃ c, HasValueAt (F := F) (s i) (x j).left (τ j) c ∧ HasValueAt (F := F) (s' i) (x' j).left (τ' j) c)
    (vt : ∀ i j, ∃ c, HasValueAt (F := F) (t i) (x j).left (τ j) c ∧ HasValueAt (F := F) (t' i) (x' j).left (τ' j) c)
    (dense : SeparatesSections (F := F) P.L fun j => (x j).left)
    (dense' : SeparatesSections (F := F) P'.L fun j => (x' j).left) :
    ∃ β : P.A ≅ P'.A, IsMonHom β.hom ∧ (∀ j, x j ≫ β.hom = x' j) ∧
      ∃ w : LB.Iso P.L (P'.L.pull β.hom.left), w.IsGen ∧ ∀ j a a', ⊤ ≤ (x j).left ⁻¹ᵁ P.L.U a →
        ⊤ ≤ (x' j).left ⁻¹ᵁ P'.L.U a' → valF (F := F) (x j).left _ (w.s (fun _ => a', a)).val * τ j a = τ' j a' := by
  have := isIntegral_left_of_isAbelianScheme_field P.A P.isAb
  have es := polarized_abelian_embeds_by_sections hA P hN s hs
  have es' := polarized_abelian_embeds_by_sections hA P' hN s' hs'
  obtain ⟨β, hβ⟩ := exists_over_hom hτ hτ' s s' es es' vs dense
  obtain ⟨δ, hδ⟩ := exists_over_hom hτ' hτ s' s es' es (fun i j => (vs i j).imp fun _ h => h.symm) dense'
  refine ⟨⟨β, δ, hom_ext_of_separatesSections P P dense fun j => ?_,
    hom_ext_of_separatesSections P' P' dense' fun j => ?_⟩, rigidity_holds _ _ _ P.isAb P'.isAb β ?_, hβ, ?_⟩
  · rw [← Category.assoc, hβ, hδ, Category.comp_id]
  · rw [← Category.assoc, hδ, hβ, Category.comp_id]
  · have e := hβ j₀
    rw [h₀, h₀', Hom.one_def, Hom.one_def, Category.assoc] at e
    have : IsIso (toUnit (baseOver (Spec (CommRingCat.of F)))) :=
      isIso_of_isTerminal Over.mkIdTerminal isTerminalTensorUnit _
    exact (cancel_epi _).1 e
  · exact (meetsOpens_of_separatesSections P dense).exists_lbIso (x' := fun j => (x' j).left) β.left
      (fun j => congrArg CommaMorphism.left (hβ j)) hτ hτ' hM s s' t t' es.1 es'.1
      (polarized_abelian_embeds_by_sections hA P (by omega) t ht).1 (polarized_abelian_embeds_by_sections hA P' (by omega) t' ht').1 vs vt

theorem _root_.GlobalTheory.polAV_iso_of_matching_values (hA : AmpleSt) (P P' : PolAV (Spec (CommRingCat.of F)))
    (x : J → (baseOver (Spec (CommRingCat.of F)) ⟶ P.A)) (x' : J → (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A))
    (j₀ : J) (h₀ : x j₀ = 1) (h₀' : x' j₀ = 1)
    (τ : ∀ j, LB.Gen (P.L.pull (Y := Sp F) (x j).left)) (τ' : ∀ j, LB.Gen (P'.L.pull (Y := Sp F) (x' j).left))
    (hτ : ∀ j, (τ j).IsGen) (hτ' : ∀ j, (τ' j).IsGen) {I K : Type} [Fintype I] [Fintype K]
    (s : I → H0 P.L 4) (s' : I → H0 P'.L 4) (t : K → H0 P.L 5) (t' : K → H0 P'.L 5)
    (hs : ∀ u, InSpan P.A.hom s u) (hs' : ∀ u, InSpan P'.A.hom s' u)
    (ht : ∀ u, InSpan P.A.hom t u) (ht' : ∀ u, InSpan P'.A.hom t' u)
    (vs : ∀ i j, ∃ c : F, HasValueAt (s i) (x j).left (genCoord (τ j)) c ∧
      HasValueAt (s' i) (x' j).left (genCoord (τ' j)) c)
    (vt : ∀ i j, ∃ c : F, HasValueAt (t i) (x j).left (genCoord (τ j)) c ∧
      HasValueAt (t' i) (x' j).left (genCoord (τ' j)) c)
    (dense : SeparatesSections (F := F) P.L fun j => (x j).left)
    (dense' : SeparatesSections (F := F) P'.L fun j => (x' j).left) :
    ∃ β : P.A ≅ P'.A, IsMonHom β.hom ∧ (∀ j, x j ≫ β.hom = x' j) ∧
      (∃ w : LB.Iso P.L (P'.L.pull β.hom.left), w.IsGen ∧ ∀ j, GenRel (F := F) w (τ j) (τ' j) 1) ∧
      ∀ (f : P.A ⟶ P.A) (f' : P'.A ⟶ P'.A) (r : J → J), (∀ j, x j ≫ f = x (r j)) → (∀ j, x' j ≫ f' = x' (r j)) →
        f ≫ β.hom = β.hom ≫ f' := by
  obtain ⟨β, hm, hβ, w, hw, hv⟩ := exists_iso_of_frames hA h₀ h₀' (fun j => isFrameAt_genCoord (hτ j))
    (fun j => isFrameAt_genCoord (hτ' j)) le_rfl rfl s s' t t' hs hs' ht ht' vs vt dense dense'
  refine ⟨β, hm, hβ, ⟨w, hw, fun j => ⟨fun _ => congrArg CommaMorphism.left (hβ j), fun a a' h => ?_⟩⟩,
    fun f f' r hf hf' => hom_ext_of_separatesSections P P' dense fun j => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ b, a = fun _ => b := ⟨a PUnit.unit, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ b, a' = fun _ => b := ⟨a' PUnit.unit, rfl⟩
    have hm := mem_of_le (h PUnit.unit)
    have ha' : ⊤ ≤ (x' j).left ⁻¹ᵁ P'.L.U a' := by
      rw [← hβ]; exact le_of_mem (x := (x j).left ≫ β.hom.left) (mem_pull.1 hm.1)
    have e := hv j a a' (le_of_mem hm.2) ha'
    have n := left_ne_zero_of_mul (e.trans_ne ((isFrameAt_genCoord (hτ' j)).1 a' ha'))
    rw [Fintype.prod_unique, _root_.one_mul, zpow_neg, zpow_one]
    exact (eq_inv_mul_iff_mul_eq₀ n).2 e
  · rw [← Category.assoc, hf, hβ, ← Category.assoc, hβ, hf']

end Abelian

end GlobalTheory.MatchCoord
