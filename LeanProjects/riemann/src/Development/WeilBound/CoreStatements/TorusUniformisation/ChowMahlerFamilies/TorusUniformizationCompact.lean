import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.Xgn.TorusUniformizationCompact

open GlobalTheory.CompanionTheory.Ar.RootHt

def ev {S : Scheme.{0}} (U : S.Opens) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : Γ(S, U) →+* ℂ :=
  (S.presheaf.germ U (centre z) hz ≫ Scheme.stalkClosedPointTo z).hom

theorem ev_apply {S : Scheme.{0}} (U : S.Opens) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) (t : Γ(S, U)) :
    ev U z hz t = (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz t) := rfl

theorem ev_res {S : Scheme.{0}} {U V : S.Opens} (h : V ≤ U) (z : Sp ℂ ⟶ S) (hz : centre z ∈ V) (t : Γ(S, U)) :
    ev V z hz (S.presheaf.map (homOfLE h).op t) = ev U z (h hz) t := by
  rw [ev_apply, ev_apply, TopCat.Presheaf.germ_res_apply]

theorem ev_appLE {S T : Scheme.{0}} (g : T ⟶ S) {U : S.Opens} {V : T.Opens} (h : V ≤ g ⁻¹ᵁ U) (z : Sp ℂ ⟶ T)
    (hz : centre z ∈ V) (hz' : centre (z ≫ g) ∈ U) (t : Γ(S, U)) :
    ev V z hz (g.appLE U V h t) = ev U (z ≫ g) hz' t := by
  have e1 := ArchC.germ_closedPoint (R := .of ℂ) z V hz
  have e2 := ArchC.germ_closedPoint (R := .of ℂ) (z ≫ g) U hz'
  have e3 : g.appLE U V h ≫ (T.presheaf.germ V (centre z) hz ≫ Scheme.stalkClosedPointTo z) =
      S.presheaf.germ U (centre (z ≫ g)) hz' ≫ Scheme.stalkClosedPointTo (z ≫ g) := by
    refine (congrArg (fun q => g.appLE U V h ≫ q) e1).trans (Eq.trans ?_ e2.symm)
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun q => q.hom t) e3

theorem mem_basicOpen_iff {S : Scheme.{0}} {U : S.Opens} (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) (g : Γ(S, U)) :
    centre z ∈ S.basicOpen g ↔ ev U z hz g ≠ 0 := by
  rw [Scheme.mem_basicOpen S g (centre z) hz, ev_apply, ← isUnit_iff_ne_zero]
  exact ⟨fun h => h.map _, fun h => (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit _ h⟩

def bdd {S : Scheme.{0}} {β : Type} (F : Filter β) (p : β → (Sp ℂ ⟶ S)) (U : S.Opens) : Subring Γ(S, U) where
  carrier := {t | ∃ C : ℝ, ∀ᶠ i in F, ∀ h : centre (p i) ∈ U, ‖ev U (p i) h t‖ ≤ C}
  mul_mem' := by
    rintro a b ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, ?_⟩
    filter_upwards [hA, hB] with i h1 h2 h
    rw [map_mul, norm_mul]
    exact mul_le_mul (h1 h) (h2 h) (norm_nonneg _) ((norm_nonneg _).trans (h1 h))
  one_mem' := ⟨1, Eventually.of_forall fun i h => by simp⟩
  add_mem' := by
    rintro a b ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, ?_⟩
    filter_upwards [hA, hB] with i h1 h2 h
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (h1 h) (h2 h))
  zero_mem' := ⟨0, Eventually.of_forall fun i h => by simp⟩
  neg_mem' := by
    rintro a ⟨A, hA⟩
    refine ⟨A, ?_⟩
    filter_upwards [hA] with i h1 h
    rw [map_neg, norm_neg]
    exact h1 h

theorem mem_bdd {S : Scheme.{0}} {β : Type} {F : Filter β} {p : β → (Sp ℂ ⟶ S)} {U : S.Opens} {t : Γ(S, U)} :
    t ∈ bdd F p U ↔ ∃ C : ℝ, ∀ᶠ i in F, ∀ h : centre (p i) ∈ U, ‖ev U (p i) h t‖ ≤ C := Iff.rfl

theorem bdd_appLE {S T : Scheme.{0}} (g : T ⟶ S) {U : S.Opens} {V : T.Opens} (h : V ≤ g ⁻¹ᵁ U)
    {β : Type} {F : Filter β} {p : β → (Sp ℂ ⟶ T)} {t : Γ(S, U)} (ht : t ∈ bdd F (fun i => p i ≫ g) U) :
    g.appLE U V h t ∈ bdd F p V := by
  obtain ⟨C, hC⟩ := ht
  refine ⟨C, ?_⟩
  filter_upwards [hC] with i hi hV
  rw [ev_appLE g h (p i) hV (h hV)]
  exact hi _

theorem bdd_of_integral {S : Scheme.{0}} {β : Type} {F : Filter β} {p : β → (Sp ℂ ⟶ S)} {U : S.Opens}
    {R : Type} [CommRing R] (φ : R →+* Γ(S, U)) (hφ : ∀ r, φ r ∈ bdd F p U) {t : Γ(S, U)}
    (ht : φ.IsIntegralElem t) : t ∈ bdd F p U := by
  obtain ⟨P, hP, h0⟩ := ht
  choose C hC using fun r => mem_bdd.1 (hφ r)
  refine ⟨∑ k ∈ Finset.range P.natDegree, |C (P.coeff k)| + 1, ?_⟩
  have hall : ∀ᶠ i in F, ∀ k ∈ Finset.range P.natDegree, ∀ h : centre (p i) ∈ U,
      ‖ev U (p i) h (φ (P.coeff k))‖ ≤ C (P.coeff k) :=
    (eventually_all_finset _).2 fun k _ => hC _
  filter_upwards [hall] with i hi h
  set ψ := (ev U (p i) h).comp φ with hψ
  have hm : (P.map ψ).Monic := hP.map ψ
  have hr : (P.map ψ).IsRoot (ev U (p i) h t) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, hψ, ← Polynomial.hom_eval₂, h0, map_zero]
  have hb := Polynomial.IsRoot.norm_lt_cauchyBound hm.ne_zero hr
  rw [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hP.natDegree_map] at hb
  have hnn : 0 ≤ ∑ k ∈ Finset.range P.natDegree, |C (P.coeff k)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs : (Finset.range P.natDegree).sup (fun k => ‖(P.map ψ).coeff k‖₊) ≤
      (⟨∑ k ∈ Finset.range P.natDegree, |C (P.coeff k)|, hnn⟩ : NNReal) := by
    refine Finset.sup_le fun k hk => ?_
    refine NNReal.coe_le_coe.1 ?_
    rw [coe_nnnorm, Polynomial.coeff_map]
    exact ((hi k hk h).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun k => |C (P.coeff k)|) (fun _ _ => abs_nonneg _) hk)
  have := hb.le.trans (add_le_add hs le_rfl)
  exact_mod_cast this

theorem bdd_rat {β : Type} {F : Filter β} {p : β → (Sp ℂ ⟶ Sp ℚ)} (t : Γ(Sp ℚ, ⊤)) : t ∈ bdd F p ⊤ := by
  let e := (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv
  refine ⟨‖((e t : ℚ) : ℂ)‖, Eventually.of_forall fun i h => le_of_eq ?_⟩
  congr 1
  have := eq_ratCast ((ev ⊤ (p i) h).comp (e.symm.toRingHom : ℚ →+* Γ(Sp ℚ, ⊤))) (e t)
  rw [← this]
  exact congrArg (ev ⊤ (p i) h) (e.symm_apply_apply t).symm

theorem bdd_XQ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {β : Type} {F : Filter β}
    {p : β → (Sp ℂ ⟶ XQ X)} (h : ∀ t, t ∈ bdd F (fun i => p i ≫ XQ.fst X) U) (t : Γ(XQ X, XQ.fst X ⁻¹ᵁ U)) :
    t ∈ bdd F p (XQ.fst X ⁻¹ᵁ U) := by
  have H : IsPullback (XQ.fst X) (XQ.snd X) (toZ X) (toZ (Sp ℚ)) := IsPullback.of_hasPullback _ _
  have hI := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) (UY := XQ.fst X ⁻¹ᵁ U)
    le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H _ _ _).1 hI
  have hc := CommRingCat.closure_range_union_range_eq_top_of_isPushout hP
  have : (⊤ : Subring _) ≤ bdd F p (XQ.fst X ⁻¹ᵁ U) := by
    rw [← hc, Subring.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact bdd_appLE _ _ (h s)
    · exact bdd_appLE _ _ (bdd_rat s)
  exact this trivial

theorem limit {S : Scheme.{0}} {W : S.Opens} (hW : IsAffineOpen W) (F : Ultrafilter (Sp ℂ ⟶ S))
    (hF : ∀ᶠ z in (F : Filter (Sp ℂ ⟶ S)), centre z ∈ W) (hb : ∀ t, t ∈ bdd (F : Filter _) id W) :
    ∃ z, (F : Filter _) ≤ @nhds _ (anTop S) z := by
  classical
  let val : Γ(S, W) → (Sp ℂ ⟶ S) → ℂ := fun t z => if h : centre z ∈ W then ev W z h t else 0
  have hval : ∀ t z (h : centre z ∈ W), val t z = ev W z h t := fun t z h => dif_pos h
  have hconv : ∀ t, ∃ a, Tendsto (val t) F (𝓝 a) := by
    intro t
    obtain ⟨C, hC⟩ := hb t
    obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds (F.map (val t)) (by
      rw [le_principal_iff, Ultrafilter.coe_map, mem_map]
      filter_upwards [hC, hF] with z h1 h2
      rw [Set.mem_preimage, mem_closedBall_zero_iff, hval t z h2]
      exact h1 h2)
    exact ⟨a, ha⟩
  choose a ha using hconv
  let g : Γ(S, W) →+* ℂ :=
    { toFun := a
      map_one' := tendsto_nhds_unique (ha 1) (tendsto_const_nhds.congr' (by
        filter_upwards [hF] with z h
        rw [hval _ z h, map_one]))
      map_zero' := tendsto_nhds_unique (ha 0) (tendsto_const_nhds.congr' (by
        filter_upwards [hF] with z h
        rw [hval _ z h, map_zero]))
      map_mul' := fun s t => tendsto_nhds_unique (ha (s * t)) (((ha s).mul (ha t)).congr' (by
        filter_upwards [hF] with z h
        rw [hval _ z h, hval _ z h, hval _ z h, map_mul]))
      map_add' := fun s t => tendsto_nhds_unique (ha (s + t)) (((ha s).add (ha t)).congr' (by
        filter_upwards [hF] with z h
        rw [hval _ z h, hval _ z h, hval _ z h, map_add])) }
  obtain ⟨hc, hg⟩ := ArchC.point_of_ringHom hW g
  set z₀ : Sp ℂ ⟶ S := Spec.map (CommRingCat.ofHom g) ≫ hW.fromSpec with hz₀
  have hg' : ∀ t, ev W z₀ hc t = a t := hg
  refine ⟨z₀, ?_⟩
  refine (TopologicalSpace.tendsto_nhds_generateFrom_iff (m := id)).2 ?_
  rintro _ ⟨U, f, V, hV, rfl⟩ ⟨hU, hf⟩
  obtain ⟨d, hdU, hd⟩ := hW.exists_basicOpen_le (V := U) ⟨centre z₀, hU⟩ hc
  have hloc := hW.isLocalization_basicOpen d
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers d)
    (S.presheaf.map (homOfLE hdU).op f : Γ(S, S.basicOpen d))
  have key : ∀ (z : Sp ℂ ⟶ S) (h : centre z ∈ W), ev W z h d ≠ 0 →
      ∃ hz : centre z ∈ U, evalAt U f z hz = ev W z h b / ev W z h d ^ n := by
    intro z h hne
    have hz := (mem_basicOpen_iff z h d).2 hne
    refine ⟨hdU hz, ?_⟩
    have e := congrArg (ev _ z hz) hbn
    have r : ∀ s : Γ(S, W), ev _ z hz (algebraMap Γ(S, W) Γ(S, S.basicOpen d) s) = ev W z h s :=
      fun s => ev_res (S.basicOpen_le d) z hz s
    rw [map_mul, r, r, ev_res, map_pow] at e
    rw [eq_div_iff (pow_ne_zero n hne)]
    exact e
  have hne : a d ≠ 0 := by
    rw [← hg']
    exact (mem_basicOpen_iff z₀ hc d).1 hd
  obtain ⟨_, e0⟩ := key z₀ hc (by rwa [hg'])
  rw [e0, hg', hg'] at hf
  have ht := ((ha b).div ((ha d).pow n) (pow_ne_zero n hne)).eventually (hV.mem_nhds hf)
  have ht2 := (ha d).eventually_ne hne
  filter_upwards [ht, ht2, hF] with z h1 h2 h
  rw [hval _ z h] at h2
  obtain ⟨hz, e⟩ := key z h h2
  refine ⟨hz, ?_⟩
  show evalAt U f z hz ∈ V
  rw [e, ← hval _ z h, ← hval _ z h]
  exact h1

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {κ : Type} {x : κ → Ω}

def Best (ξ : Sp Ω ⟶ X) (x : κ → Ω) (c : κ) (z : Sp ℂ ⟶ X) : Prop :=
  x c ≠ 0 ∧ ∀ j, ∃ r : ℂ, ValAt ξ z (x j / x c) r ∧ ‖r‖ ≤ 1

theorem exists_best [Finite κ] (hall : ∀ q : X, genPt ξ ⤳ q) (tie : CoordTie ℤ ξ x) (z : Sp ℂ ⟶ X) :
    ∃ c, Best ξ x c z := by
  obtain ⟨c₀, h0, hreg⟩ := tie.cover ⟨centre z, hall _⟩
  choose r hr using fun j => ArchB.val_exists (z := z) (hreg j)
  have : Nonempty κ := ⟨c₀⟩
  obtain ⟨c, hc⟩ := Finite.exists_max fun j => ‖r j‖
  have h1 : r c₀ = 1 := by
    have := hr c₀
    rw [div_self h0] at this
    exact ArchB.val_unique tie.gen this (ArchB.val_one (hall _))
  have hpos : 0 < ‖r c‖ := by
    have := hc c₀
    rw [h1, norm_one] at this
    linarith
  have hne : r c ≠ 0 := norm_pos_iff.1 hpos
  have hx : x c ≠ 0 := (div_ne_zero_iff.1 (ArchB.val_ne_zero tie.gen (r := Units.mk0 _ hne) (hr c))).1
  refine ⟨c, hx, fun j => ⟨r j * (r c)⁻¹, ?_, ?_⟩⟩
  · have h := ArchB.val_mul (hr j) (ArchB.val_inv₀ hne (hr c))
    convert h using 1
    field_simp
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpos]
    exact hc j

theorem best_bound (hall : ∀ q : X, genPt ξ ⤳ q) (c : κ) (a : Ω)
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :
    ∃ C : ℝ, ∀ z, Best ξ x c z → ∃ r : ℂ, ValAt ξ z a r ∧ ‖r‖ ≤ C := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    exact ⟨1, fun z hz => hz.2 j⟩
  | algebraMap n => exact ⟨‖(n : ℂ)‖, fun z _ => ⟨n, by simpa using ArchC.val_int (hall _) n, le_rfl⟩⟩
  | add a b _ _ iha ihb =>
    obtain ⟨A, hA⟩ := iha
    obtain ⟨B, hB⟩ := ihb
    refine ⟨A + B, fun z hz => ?_⟩
    obtain ⟨r, hr, hr'⟩ := hA z hz
    obtain ⟨s, hs, hs'⟩ := hB z hz
    exact ⟨r + s, ArchB.val_add hr hs, (norm_add_le _ _).trans (add_le_add hr' hs')⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨A, hA⟩ := iha
    obtain ⟨B, hB⟩ := ihb
    refine ⟨A * B, fun z hz => ?_⟩
    obtain ⟨r, hr, hr'⟩ := hA z hz
    obtain ⟨s, hs, hs'⟩ := hB z hz
    refine ⟨r * s, ArchB.val_mul hr hs, ?_⟩
    rw [norm_mul]
    exact mul_le_mul hr' hs' (norm_nonneg _) ((norm_nonneg _).trans hr')

theorem chart [Finite κ] (hall : ∀ q : X, genPt ξ ⤳ q) (tie : CoordTie ℤ ξ x) {β : Type} (F : Ultrafilter β)
    (p : β → (Sp ℂ ⟶ X)) : ∃ U : X.Opens, IsAffineOpen U ∧ (∀ᶠ i in (F : Filter β), centre (p i) ∈ U) ∧
      ∀ t, t ∈ bdd (F : Filter β) p U := by
  obtain ⟨c, hc⟩ := Ultrafilter.eventually_exists_iff.1
    (Eventually.of_forall (f := (F : Filter β)) fun i => exists_best hall tie (p i))
  obtain ⟨i₀, hi₀⟩ := hc.exists
  have hx := hi₀.1
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hin : ∀ z, Best ξ x c z → centre z ∈ U := by
    intro z hz
    refine (hmem _).2 ⟨hall _, hx, fun j => ?_⟩
    obtain ⟨r, hr, -⟩ := hz.2 j
    exact (ArchB.val_spec hr).2
  refine ⟨U, hU, hc.mono fun i hi => hin _ hi, fun t => ?_⟩
  have hp₀ := hin _ hi₀
  let e : Ω := genMap ξ ⟨centre (p i₀), hall _⟩ (X.presheaf.germ U _ hp₀ t)
  have he : ∀ {q : X} (hq : q ∈ U), genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq t) = e := by
    intro q hq
    show _ = genMap ξ ⟨centre (p i₀), hall _⟩ (X.presheaf.germ U _ hp₀ t)
    rw [ArchC.genMap_germ U (hall q) hq t, ArchC.genMap_germ U (hall _) hp₀ t]
  have hA : e ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
    (tie.ring c hx e).2 fun q hq => ⟨X.presheaf.germ U q.1 ((hmem q.1).2 ⟨q.2, hq⟩) t, he _⟩
  obtain ⟨C, hC⟩ := best_bound hall c e hA
  refine ⟨C, ?_⟩
  filter_upwards [hc] with i hi h
  obtain ⟨r, hr, hr'⟩ := hC _ hi
  have hv : ValAt ξ (p i) e (ev U (p i) h t) := ⟨hall _, _, he h, rfl⟩
  rw [ArchB.val_unique tie.gen hv hr]
  exact hr'

end Chart

end PositivityTheory.Xgn.TorusUniformizationCompact

end

theorem PositivityTheory.Xgn.torus_uniformization_compact : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') := by
  intro X Ω _ K _ J _ y ξ hall tie Z' f hf
  classical
  let _ := anTop Z'
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun F _ => ?_⟩
  obtain ⟨U, hU, hFU, hb⟩ := PositivityTheory.Xgn.TorusUniformizationCompact.chart hall tie F
    (fun z => (z ≫ f) ≫ XQ.fst X)
  have haff : IsAffineHom (XQ.fst X) :=
    (isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (toZ X) (toZ (Sp ℚ))).flip inferInstance :)
  have hW : IsAffineOpen (XQ.fst X ⁻¹ᵁ U) := hU.preimage _
  have hW' : IsAffineOpen (f ⁻¹ᵁ (XQ.fst X ⁻¹ᵁ U)) := hW.preimage _
  have h1 := PositivityTheory.Xgn.TorusUniformizationCompact.bdd_XQ hU (p := fun z => z ≫ f) hb
  obtain ⟨z, hz⟩ := PositivityTheory.Xgn.TorusUniformizationCompact.limit hW' F hFU (fun t =>
    PositivityTheory.Xgn.TorusUniformizationCompact.bdd_of_integral (f.app _).hom (fun r => by
      rw [Scheme.Hom.app_eq_appLE]
      exact PositivityTheory.Xgn.TorusUniformizationCompact.bdd_appLE f le_rfl (h1 r))
      ((IsFinite.finite_app f _ hW).to_isIntegral t))
  exact ⟨z, Set.mem_univ _, hz⟩
