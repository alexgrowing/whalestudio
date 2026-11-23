import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem basicOpen_eq (O : Type) [CommRing O] (s : X ⟶ Sp O) (a : O) :
    (X.basicOpen (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) : Set X) =
      s ⁻¹' {x : Sp O | a ∉ x.asIdeal} := by
  have e := Scheme.preimage_basicOpen s (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
  rw [basicOpen_eq_of_affine] at e
  exact congrArg (fun U : X.Opens => (U : Set X)) e.symm

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem cocycle_of_pull {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (hL : (L.pull f).IsLB) (y : Y) {i j k : L.ι}
    (hi : f y ∈ L.U i) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gm (𝟙 X) (f y) _ (L.g i j) * gm (𝟙 X) (f y) _ (L.g j k) = gm (𝟙 X) (f y) _ (L.g i k) := by
  have hi' : y ∈ (L.pull f).U (fun _ => i) := mem_pull.2 hi
  have hj' : y ∈ (L.pull f).U (fun _ => j) := mem_pull.2 hj
  have hk' : y ∈ (L.pull f).U (fun _ => k) := mem_pull.2 hk
  have e := gm_cocycle hL (𝟙 Y) y hi' hj' hk'
  rw [gm_pull_g L f (𝟙 Y) y _ _ hi' hj', gm_pull_g L f (𝟙 Y) y _ _ hj' hk', gm_pull_g L f (𝟙 Y) y _ _ hi' hk',
    Category.id_comp] at e
  apply Units.ext
  apply stalkMap_injective f y
  rw [Units.val_mul, map_mul, ← gm_val_stalkMap f y _ (show f y ∈ L.U i ⊓ L.U j from ⟨hi, hj⟩),
    ← gm_val_stalkMap f y _ (show f y ∈ L.U j ⊓ L.U k from ⟨hj, hk⟩),
    ← gm_val_stalkMap f y _ (show f y ∈ L.U i ⊓ L.U k from ⟨hi, hk⟩), ← Units.val_mul, e]

theorem isLB_of_germ (L : LB X) (hc : ∀ x : X, ∃ i, x ∈ L.U i)
    (h : ∀ (x : X) i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 (hc x)
  g_self i := unit_ext fun x hx => by
    refine (gm_res (𝟙 X) x _ hx _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h x i i i hx hx hx)
  cocycle i j k := unit_ext fun x hx =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) x _ hx _) (gm_res (𝟙 X) x _ hx _))).trans
      ((h x i j k hx.1.1 hx.1.2 hx.2).trans (gm_res (𝟙 X) x _ hx _).symm)

theorem isLB_of_pull {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (L : LB X) (hL : ∀ i, (L.pull (u i)).IsLB) (hc : ∀ x : X, ∃ i y, u i y = x) : L.IsLB := by
  refine isLB_of_germ L (fun x => ?_) fun x a b c ha hb hc' => ?_
  · obtain ⟨i, y, rfl⟩ := hc x
    obtain ⟨J, hJ⟩ := exists_chart (hL i) y
    exact ⟨J PUnit.unit, mem_pull.1 hJ⟩
  · obtain ⟨i, y, rfl⟩ := hc x
    exact cocycle_of_pull (u i) (hL i) y ha hb hc'

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

theorem exists_affine_of_pull [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    [IsOpenImmersion f] (r : Γ(X, ⊤)) (hr : X.basicOpen r = f.opensRange) (h : IsAmpleLB (L.pull f)) (y : Y) :
    ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, f y ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨n, hn, t, hty, hta⟩ := h.exists_affine y
  have hs₀ : nonzeroLocus (secOfFn L r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn L r)) hs₀ t
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn L r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : Y) (J : PUnit → L.ι), f y' ∈ powChart L J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t) := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn L r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy, gs_res (𝟙 X) (f y') _ hy] at e
    rw [mem_nonzeroLocus_iff_powFn u hJ, e, IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  have hloc : nonzeroLocus (secMul u (secOfFn L r)) = f ''ᵁ nonzeroLocus t := by
    rw [nonzeroLocus_secMul]
    ext x
    constructor
    · rintro ⟨hx, hx₀⟩
      obtain ⟨y', rfl⟩ : ∃ y', f y' = x := by
        have : x ∈ f.opensRange := hs₀ ▸ hx₀
        exact this
      obtain ⟨i, hi⟩ := exists_chart hL (f y')
      exact ⟨y', (key y' (fun _ => i) (mem_powChart.2 hi)).1 hx, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨i, hi⟩ := exists_chart hL (f y')
      exact ⟨(key y' (fun _ => i) (mem_powChart.2 hi)).2 hy', hs₀ ▸ ⟨y', rfl⟩⟩
  refine ⟨n + 0 * N + 0, by omega, secMul u (secOfFn L r), ?_, ?_⟩
  · rw [hloc]
    exact ⟨y, hty, rfl⟩
  · rw [hloc]
    exact hta.image_of_isOpenImmersion f

theorem isAmpleLB_of_basicOpen_cover : ∀ {X : Scheme.{0}} {O : Type} [CommRing O] {I : Type} [Finite I]
    {Y : I → Scheme.{0}} (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X),
    CompactSpace X → QuasiSeparatedSpace X → Ideal.span (Set.range a) = ⊤ → (∀ i, IsOpenImmersion (u i)) →
    (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) → (∀ i, GlobalTheory.IsAmpleLB (L.pull (u i))) →
    GlobalTheory.IsAmpleLB L := by
  intro X O _ I _ Y s u a L hX hXs hspan hu hrange hamp
  have hc : ∀ x : X, ∃ i y, u i y = x := fun x => by
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hne
      push Not at hne
      apply (s x).isPrime.ne_top
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    obtain ⟨i, hi⟩ := this
    have hx : x ∈ Set.range (u i) := by
      rw [hrange i]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  have hL : L.IsLB := isLB_of_pull u L (fun i => (hamp i).isLB) hc
  refine ⟨hL, hX, fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := hc x
  have hr : X.basicOpen ((s.appTop) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv (a i))) = (u i).opensRange := by
    apply SetLike.coe_injective
    rw [basicOpen_eq O s (a i), ← hrange i]
    rfl
  exact exists_affine_of_pull hL (u i) _ hr (hamp i) y

end GlobalTheory.AmpleOverBase
