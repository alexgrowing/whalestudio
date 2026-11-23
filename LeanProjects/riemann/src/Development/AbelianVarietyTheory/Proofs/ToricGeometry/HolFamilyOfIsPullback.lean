import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem holFamily_of_affine
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (Z : Scheme.{0}) (c : E → (Sp ℂ ⟶ Z))
    (hc : ∀ w ∈ W, ∃ V : Z.Opens, IsAffineOpen V ∧ ⊤ ≤ c w ⁻¹ᵁ V ∧ IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∧
      ∀ g : Γ(Z, V), DifferentiableOn ℂ (fun w => valAt' (c w) V g) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun Y x O => (hv Y x).1 O

  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U}, ∃ N : Set E, IsOpen N ∧ w₀ ∈ N ∧
      N ⊆ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (c w) U f) N := by
    rintro w₀ ⟨hw₀, hU₀⟩
    obtain ⟨V, hVa, hV₀, hVo, hVd⟩ := hc w₀ hw₀
    obtain ⟨g, hgU, hg₀⟩ := hVa.exists_basicOpen_le (V := U)
      ⟨c w₀ (default : PrimeSpectrum ℂ), (hpt _ _ _).1 hU₀⟩ ((hpt _ _ _).1 hV₀)
    have hDV : Z.basicOpen g ≤ V := Z.basicOpen_le g
    let := hVa.isLocalization_basicOpen g
    obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, hh⟩ := IsLocalization.surj (Submonoid.powers g) (resG Z hgU f)
    have hh' : resG Z hgU f * resG Z hDV g ^ n = resG Z hDV h := by
      rw [← map_pow]
      exact hh
    refine ⟨{w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ,
      (hVd g).continuousOn.isOpen_inter_preimage hVo isOpen_compl_singleton, ?_, ?_, ?_⟩
    · refine ⟨⟨hw₀, hV₀⟩, ?_⟩
      exact ((hv Z (c w₀)).2.2.2.2.1 V g).1 ((hpt _ _ _).2 hg₀)
    · rintro w ⟨⟨hw, -⟩, hg⟩
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg
      exact ⟨hw, (hpt _ _ _).2 (hgU ((hpt _ _ _).1 hD))⟩
    · have hq : DifferentiableOn ℂ (fun w => valAt' (c w) V h * (valAt' (c w) V g ^ n)⁻¹)
          ({w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ) :=
        by
        apply DifferentiableOn.fun_mul
        · exact (hVd h).mono Set.inter_subset_left
        · apply DifferentiableOn.fun_inv
          · exact ((hVd g).mono Set.inter_subset_left).fun_pow n
          · intro w hw
            exact pow_ne_zero _ hw.2
      refine hq.congr fun w ⟨⟨hw, hwV⟩, hg⟩ => ?_
      have hg' : valAt' (c w) V g ≠ 0 := hg
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg'
      obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hD
      have h1 := (hv Z (c w)).2.2.1 U _ hgU f hD
      have h2 := (hv Z (c w)).2.2.1 V _ hDV g hD
      have h3 := (hv Z (c w)).2.2.1 V _ hDV h hD
      rw [he] at h1 h2 h3
      have h4 := congrArg e hh'
      rw [map_mul, map_pow, h1, h2, h3] at h4
      rw [← div_eq_mul_inv]
      exact eq_div_of_mul_eq (pow_ne_zero _ hg') h4
  refine ⟨isOpen_iff_forall_mem_open.2 fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨N, hNo, hwN, hNs, -⟩ := key w hw
    exact ⟨N, hNs, hNo, hwN⟩
  · obtain ⟨N, hNo, hwN, -, hNd⟩ := key w hw
    exact (hNd.differentiableAt (hNo.mem_nhds hwN)).differentiableWithinAt

theorem holFamily_of_isPullback
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) {S X Y Z : Scheme.{0}} [IsAffine S]
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) (c : E → (Sp ℂ ⟶ Z))
    (ha : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U})
    (hb : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (T : Scheme.{0}) (x : Sp ℂ ⟶ T) (O : T.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun T x O => (hv T x).1 O
  refine holFamily_of_affine hv W Z c (fun w hw => ?_) U f
  obtain ⟨VX, hVXa, hVX₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (p (c w (default : PrimeSpectrum ℂ))))
  obtain ⟨VY, hVYa, hVY₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (q (c w (default : PrimeSpectrum ℂ))))
  have hSX : VX ≤ s ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have hST : VY ≤ t ⁻¹ᵁ (⊤ : S.Opens) := le_top

  have hmem : ∀ x : Sp ℂ ⟶ Z, ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) ↔
      ⊤ ≤ (x ≫ p) ⁻¹ᵁ VX ∧ ⊤ ≤ (x ≫ q) ⁻¹ᵁ VY := by
    intro x
    show ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX) ⊓ x ⁻¹ᵁ (q ⁻¹ᵁ VY) ↔ _
    exact le_inf_iff
  have hPO := (isIso_pushoutSection_iff H hST hSX (UY := p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hST hSX rfl (isAffineOpen_top S) hVYa hVXa)
  have hVa : IsAffineOpen (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) := by
    have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
    have : IsAffine VY := hVYa
    have : IsAffine VX := hVXa
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hST hSX rfl).isoPullback.hom

  have hNo : IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} := by
    convert (ha VX 0).1.inter (hb VY 0).1 using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hmem]
    tauto

  let T : Subring Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) :=
    { carrier := {g | DifferentiableOn ℂ (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) g)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)}}
      mul_mem' := fun {a b} ha' hb' => (ha'.fun_mul hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_mul]
      one_mem' := (differentiableOn_const (1 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_one]
      add_mem' := fun {a b} ha' hb' => (ha'.fun_add hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_add]
      zero_mem' := (differentiableOn_const (0 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_zero]
      neg_mem' := fun {a} ha' => ha'.fun_neg.congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_neg] }

  have hXT : ∀ a : Γ(X, VX), (p.appLE VX (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_left).hom a ∈ T := by
    intro a
    refine ((ha VX a).2.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).1⟩).congr fun w hw => ?_
    have h1 := (hv Z (c w)).2.2.1 (p ⁻¹ᵁ VX) _ inf_le_left ((p.app VX).hom a) hw.2
    have h2 := (hv Z (c w)).2.2.2.1 X p VX a
    exact h1.trans h2
  have hYT : ∀ b : Γ(Y, VY), (q.appLE VY (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_right).hom b ∈ T := by
    intro b
    refine ((hb VY b).2.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).2⟩).congr fun w hw => ?_
    have h1 := (hv Z (c w)).2.2.1 (q ⁻¹ᵁ VY) _ inf_le_right ((q.app VY).hom b) hw.2
    have h2 := (hv Z (c w)).2.2.2.1 Y q VY b
    exact h1.trans h2

  let φX : Γ(X, VX) ⟶ CommRingCat.of T := CommRingCat.ofHom ((p.appLE VX _ inf_le_left).hom.codRestrict T hXT)
  let φY : Γ(Y, VY) ⟶ CommRingCat.of T := CommRingCat.ofHom ((q.appLE VY _ inf_le_right).hom.codRestrict T hYT)
  have hw' : s.appLE ⊤ VX hSX ≫ φX = t.appLE ⊤ VY hST ≫ φY := by
    ext x
    exact congrArg (fun k => k.hom x) hPO.w
  have hid : hPO.desc φX φY hw' ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    refine hPO.hom_ext ?_ ?_
    · rw [← Category.assoc, hPO.inl_desc, Category.comp_id]
      rfl
    · rw [← Category.assoc, hPO.inr_desc, Category.comp_id]
      rfl
  refine ⟨_, hVa, (hmem _).2 ⟨(hpt _ _ _).2 hVX₀, (hpt _ _ _).2 hVY₀⟩, hNo, fun g => ?_⟩
  have h1 := congrArg (fun k => k.hom g) hid
  have h2 : ((hPO.desc φX φY hw').hom g : Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)) = g := h1
  rw [← h2]
  exact ((hPO.desc φX φY hw').hom g).2

theorem holFamily_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) := by
  intro hv E _ _ W X Y a b ha hb U f

  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hfa : ∀ w, (lift (a w) (b w)).left ≫ (fst X Y).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have hfb : ∀ w, (lift (a w) (b w)).left ≫ (snd X Y).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  exact holFamily_of_isPullback hv W H (fun w => (lift (a w) (b w)).left)
    (fun U' f' => by simpa only [hfa] using ha U' f')
    (fun U' f' => by simpa only [hfb] using hb U' f') U f

end GlobalTheory
