import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem frameLieBC_loc {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G] [Smooth G.hom] {d : ℕ}
    {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) {k : Type} [CommRing k] [IsLocalRing k] (φ : S →+* k)
    {G' : Over (Spec (CommRingCat.of k))} [GrpObj G'] {F : G'.left ⟶ G.left}
    (h : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φ) F) {u' : Fin d → (Geo.Tor.epsR k ⟶ G')}
    (hu' : ∀ i, (u' i).left ≫ F = Geo.Tor.spMap (dualMapR φ) ≫ (u i).left) : Geo.Tor.IsLieBasis u' := by
  classical
  set p := (IsLocalRing.maximalIdeal k).comap φ with hp
  haveI : p.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal k)
  have hunit : ∀ y : p.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).mpr hy)
  let φp : Localization.AtPrime p →+* k := IsLocalization.lift hunit
  have hφ : φp.comp (algebraMap S (Localization.AtPrime p)) = φ := IsLocalization.lift_comp hunit
  have hsp : Geo.Tor.spMap φ = Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime p) := by
    rw [← hφ, Geo.Tor.spMap_comp]
  have h2 : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime p)) F :=
    h.congr hsp rfl
  haveI hGs : ∀ s : S, Smooth (Gs G s).hom := fun s => by
    show Smooth (pullback.snd G.hom (fB S (Localization.Away s)))
    infer_instance
  haveI : Smooth ((Over.pullback (fB S (Localization.AtPrime p))).obj G).hom := by
    show Smooth (pullback.snd G.hom (fB S (Localization.AtPrime p)))
    infer_instance
  have h3 := isGrpPullback_factor (fB S (Localization.AtPrime p)) (Geo.Tor.spMap φp) h2
  refine isLieBasis_baseChange φp h3 (isLieBasis_local (p := p) hu) (fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hu' i, Category.assoc, ← pushR_left, pushR_resP, ← hφ,
      dualMapR_comp, Geo.Tor.spMap_comp, Category.assoc]
    rfl
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc,
      show (resP p (u i)).left ≫ pullback.snd G.hom (fB S (Localization.AtPrime p)) = _ from
        Over.w (resP p (u i))]
    simp
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
    congr 1
    ext x <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem eq_of_loc {S : Type} [CommRing S] {a b : S}
    (h : ∀ (p : Ideal S) [p.IsMaximal], algebraMap S (Localization.AtPrime p) a = algebraMap S _ b) : a = b := by
  have key : ∀ p : Ideal S, p.IsMaximal → ∃ m ∉ p, m * (a - b) = 0 := by
    intro p hp
    have h1 := @h p hp
    rw [← sub_eq_zero, ← map_sub] at h1
    obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp h1
    exact ⟨m, hm, hm'⟩
  let I : Ideal S := LinearMap.ker (LinearMap.mulRight S (a - b))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨m, hm, hm'⟩ := key p hp
    exact hm (hIp (LinearMap.mem_ker.mpr (by simpa using hm')))
  have h1 : (1 : S) ∈ I := hI ▸ Submodule.mem_top
  have h2 := LinearMap.mem_ker.mp h1
  simpa [sub_eq_zero] using h2

theorem isLieBasis_of_local {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (hadd : ∀ (a b : S) (w : sp (R₀ := S) (DualNumber S) ⟶ G), IsTan w →
      spMap (scaleD (a + b)) ≫ w = (spMap (scaleD a) ≫ w) * (spMap (scaleD b) ≫ w)) {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)}
    (hT : ∀ i, IsTan (u i)) (hu : ∀ (p : Ideal S) [p.IsPrime], Geo.Tor.IsLieBasis (G := Gp (G := G) p) fun i => resP p (u i)) :
    Geo.Tor.IsLieBasis u := by
  have : ∀ s : S, Smooth (Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  have add : ∀ a b : Fin d → S, prodPts (a + b) u = prodPts a u * prodPts b u := fun a b => by
    simp only [prodPts, List.prod_ofFn, Pi.add_apply, hadd _ _ _ (hT _), Finset.prod_mul_distrib]
  refine ⟨fun i => (isTan_iff _).1 (hT i), fun w hw => ?_⟩
  have hw' : IsTan w := (isTan_iff _).2 hw
  let I : Ideal S :=
    { carrier := {t | ∃ a, spMap (scaleD t) ≫ w = prodPts a u}
      add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [hadd _ _ _ hw', ha, hb, add]⟩
      zero_mem' := ⟨0, by
        have h₁ := hadd 0 0 w hw'
        have h₂ := add 0 0
        rw [add_zero] at h₁ h₂
        rw [mul_eq_left.1 h₁.symm, mul_eq_left.1 h₂.symm]⟩
      smul_mem' := fun r t ⟨a, ha⟩ => ⟨r • a, by
        rw [← scale_prodPts, ← ha]; exact (scale_scale (S := S) r t w).symm⟩ }
  have top : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨c, hc, -⟩ := (hu p).2 (resP p w) ((isTan_iff _).1 ((isTan_iff_tanS p _).2 (by
      rw [pushR_resP]; exact tanS_restrict _ hw')))
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin d)) c
    choose a ha using fun i => hqi i (Finset.mem_univ _)
    have e : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ (spMap (scaleD q) ≫ w) =
        spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts a u := by
      rw [← pushR_prodPts_resP, show (fun i => algebraMap S (Localization.AtPrime p) (a i)) =
        algebraMap S (Localization.AtPrime p) q • c from funext fun i => (ha i).trans (Algebra.smul_def _ _),
        ← scale_prodPts, ← (isLieComb_iff _ _ _).1 hc, pushR_spMap, pushR_resP]
      exact res_scale (Algebra.ofId S (Localization.AtPrime p)) q w
    obtain ⟨r, hr, hs⟩ := tan_prime_uniq p (w := (spMap (scaleD q) ≫ w) * (prodPts a u)⁻¹) (by
      rw [TanS, MonObj.comp_mul, GrpObj.comp_inv, show spMap (TrivSqZeroExt.fstHom S S S) ≫ spMap (scaleD q) ≫ w = 1 from
        tanS_scale (S := S) q hw', show spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts a u = 1 from tanS_prodPts a hT,
        inv_one, _root_.mul_one]) (by rw [MonObj.comp_mul, GrpObj.comp_inv, e, mul_inv_cancel])
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one] at hs
    exact p.primeCompl.mul_mem hr hq (hI ⟨r • a, (scale_scale (S := S) r q w).symm.trans (hs.trans (scale_prodPts r a u))⟩)
  obtain ⟨a, ha⟩ : (1 : S) ∈ I := top ▸ Submodule.mem_top
  have e : w = prodPts a u := by
    rw [← ha, show scaleD (1 : S) = AlgHom.id S _ from scaleS_one (S := S), spMap_id, Category.id_comp]
  refine ⟨a, (isLieComb_iff _ _ _).2 e, fun b hb => funext fun i => ?_⟩
  refine eq_of_loc fun p _ => ?_
  have k : prodPts (fun i => algebraMap S (Localization.AtPrime p) (b i)) (fun i => resP p (u i)) =
      prodPts (fun i => algebraMap S (Localization.AtPrime p) (a i)) (fun i => resP p (u i)) := by
    apply pushR_inj G
    rw [pushR_prodPts_resP, pushR_prodPts_resP, ← e, ← (isLieComb_iff _ _ _).1 hb]
  have t : Geo.Tor.IsTangent (prodPts (fun i => algebraMap S (Localization.AtPrime p) (b i)) fun i => resP p (u i)) :=
    (isTan_iff _).1 (tanS_prodPts _ fun i => (isTan_iff _).2 ((hu p).1 i))
  exact congrFun (((hu p).2 _ t).unique ((isLieComb_iff _ _ _).2 rfl) ((isLieComb_iff _ _ _).2 k)) i

theorem frameLieBCR {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G] [Smooth G.hom] {d : ℕ}
    {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) {k : Type} [CommRing k] (φ : S →+* k)
    {G' : Over (Spec (CommRingCat.of k))} [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left}
    (h : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φ) F)
    (hadd : ∀ (a b : k) (w : sp (R₀ := k) (DualNumber k) ⟶ G'), IsTan w →
      spMap (scaleD (a + b)) ≫ w = (spMap (scaleD a) ≫ w) * (spMap (scaleD b) ≫ w)) {u' : Fin d → (Geo.Tor.epsR k ⟶ G')}
    (hT : ∀ i, Geo.Tor.IsTangent (u' i))
    (hu' : ∀ i, (u' i).left ≫ F = Geo.Tor.spMap (dualMapR φ) ≫ (u i).left) : Geo.Tor.IsLieBasis u' := by
  have : Smooth G'.hom := MorphismProperty.of_isPullback (P := @Smooth) h.1 ‹_›
  refine isLieBasis_of_local hadd (fun i => (isTan_iff _).2 (hT i)) fun p _ => ?_
  have c := (Geo.Tor.isGrpPullback_pullback G' (fB k (Localization.AtPrime p))).comp h
  refine frameLieBC_loc G hu ((algebraMap k (Localization.AtPrime p)).comp φ) (by rw [Geo.Tor.spMap_comp]; exact c) fun i => ?_
  have e := congrArg (fun q => Over.Hom.left q) (pushR_resP (G := G') p (u' i))
  simp only [pushR_left, Over.comp_left] at e
  rw [← Category.assoc, e, Category.assoc, hu', ← Category.assoc, dualMapR_comp, Geo.Tor.spMap_comp]
  rfl

end ReciprocityTheory.ChartRestriction.G.Chart

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

theorem globalSections_rank_one_local (hT : SecTwistSt) {K : Type} [CommRing K] [IsLocalRing K] (P : PolAV (Sp K)) :
    ∃ b : LB.Sec P.L, ∀ s : LB.Sec P.L, ∃! a : K, ∀ i, s.f i = constFn P.A.hom _ a * b.f i := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ P 1 le_rfl K (𝟙 _) 1
  let T : Over (Sp K) := Over.mk (𝟙 _)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have sq : (snd T P.A).left ≫ P.A.hom = (fst T P.A).left := pullback.condition.symm.trans (Category.comp_id _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (sq.trans (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have one : ∀ a : Fin (1 ^ P.g), a = i₀ := fun a => Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (one a) h) (by simp)
  let φ : Fin 2 → ((T ⊗ P.A).left ⟶ P.A.left) := ![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left]
  let ε : Fin 2 → ℤ := ![((1 : ℕ) : ℤ) - 1, 1]
  obtain ⟨β, hβ⟩ := exists_sec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun U _ h => by
    rw [Fin.prod_univ_two, Fin.prod_univ_one]
    show h _ ^ (((1 : ℕ) : ℤ) - 1) * h (ρ.left ≫ (translPt P.A (1 : T ⟶ P.A)).left) ^ (1 : ℤ) = _
    rw [e, ρ₂]; simp) (pullSec P.L φ ε (b i₀) ρ.left)
  refine ⟨secOfH0 β, fun s => ?_⟩
  obtain ⟨t, ht⟩ := exists_sec P.isLB (φ' := φ) (ε' := ε) (fun U _ h => by simp [φ, ε, e])
    (pullSec P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => ((1 : ℕ) : ℤ)) (toH0 s) (snd T P.A).left)
  have sp : ∀ {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
      (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') z J, Good L z J →
      sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := fun {X Y Y' Z L K _ φ ε} s h r z J hJ => by
    have m := hJ.mem (fun k => h ≫ φ k) r
    exact ((gs_res r z (wchart_comp_le L φ h _) m _).trans (gs_pull r h z _ (wchart_comp_le L φ h _ m) _)).trans
      (sval_of s (r ≫ h) z J _ fun k => by rw [Category.assoc]).symm
  have key : ∀ a : K, (∀ i, s.f i = constFn P.A.hom _ a * (secOfH0 β).f i) ↔
      ∀ k, t.f k = constFn (fst T P.A).left _ a * (b i₀).f k := fun a => by
    refine (sec_eq_iff _ _ _ _).trans (Iff.trans ⟨fun h k z hz => ?_, fun h i y hy => ?_⟩
      (sec_eq_iff (L := LB.LinComb P.L φ ε) (fst T P.A).left t (b i₀) a).symm)
    · choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
      have m := hJ ((𝟙 _ ≫ (snd T P.A).left) ≫ 𝟙 _)
      have k₁ := gs_of_id (𝟙 _ ≫ (snd T P.A).left) z (by simpa using m) (h _ _ (by simpa using m))
      have a₁ : sval t (𝟙 _) z J = _ := ((ht _ _ z J hJ).trans (sp _ _ _ z J hJ)).trans
        (gs_res _ z (h0_le fun _ => J ((𝟙 _ ≫ (snd T P.A).left) ≫ 𝟙 _)) (Good.mem hJ (fun _ : Fin 1 => 𝟙 _) _) _)
      have a₂ := (gs_res (𝟙 _ ≫ (snd T P.A).left) z (chart_le_weighted_chart_single (J ((𝟙 _ ≫ (snd T P.A).left) ≫ 𝟙 _))) (by simpa using m) _).trans
        ((hβ _ _ z J hJ).trans (sp _ _ _ z J hJ))
      replace a₂ := a₂.trans (congrArg (sval (L := P.L) (φ := φ) (ε := ε) (b i₀) · z J)
        (show (𝟙 _ ≫ (snd T P.A).left) ≫ ρ.left = 𝟙 _ by rw [Category.assoc, ρ₃, Category.comp_id]))
      replace k₁ := k₁.trans (congrArg (fun q => cst q z a * _)
        (show (𝟙 _ ≫ (snd T P.A).left) ≫ P.A.hom = (fst T P.A).left by rw [Category.id_comp, sq]))
      exact (sec_trans (φ := φ) (ε := ε) t (𝟙 _) z hz (Good.mem hJ φ _)).trans (((congrArg _ (a₁.trans (k₁.trans
        (congrArg _ a₂)))).trans (mul_left_comm _ _ _)).trans (congrArg _
        (sec_trans (φ := φ) (ε := ε) (b i₀) (𝟙 _) z hz (Good.mem hJ φ _)).symm))
    · obtain ⟨J, hJ, hj⟩ := exists_good _ P.isLB y (fun _ : Fin 1 => 𝟙 _ ≫ 𝟙 _) (fun _ => i) (fun _ _ _ => rfl) fun _ => hy
      have m := hJ.mem φ ρ.left
      have k₁ := gs_of_id ρ.left y m (h _ _ m)
      have a₁ : sval t ρ.left y J = _ := (ht _ _ y J hJ).trans (sp _ _ _ y J hJ)
      have a₂ := (hβ _ (𝟙 _) y J hJ).trans (sp _ _ _ y J hJ)
      rw [ρ₂, sval_of _ _ y J (fun _ => i) hj] at a₁
      rw [Category.id_comp, sval_of _ _ y J (fun _ => i) hj] at a₂
      rw [ρ₁] at k₁
      exact (gs_res (𝟙 _) y (h0_le fun _ => i) (chart_le_weighted_chart_single i hy) _).symm.trans (a₁.symm.trans (k₁.trans (congrArg _
        (a₂.symm.trans (gs_res (𝟙 _) y (chart_le_weighted_chart_single i) hy _).symm))))
  simp only [key]
  obtain ⟨r, hr, hu⟩ := hb t
  let eq' := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  refine ⟨eq' (r i₀), fun k => (hr k).trans ((su _).trans (congrArg (· * _) ?_)), fun a ha => ?_⟩
  · exact congrArg (fun q => ((fst T P.A).left.appLE ⊤ _ (fun _ _ => trivial)).hom q) (eq'.symm_apply_apply _).symm
  · rw [← hu (fun _ => eq'.symm a) fun k => (ha k).trans (Eq.symm ((su _).trans rfl)), RingEquiv.apply_symm_apply]

theorem gs_comp {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  have h' : (r ≫ F) z ∈ U := h
  unfold gs
  rw [dif_pos h', dif_pos h]
  have e := congrArg (fun φ => φ.hom ((F.app U).hom f)) (Scheme.Hom.germ_stalkMap r (F ⁻¹ᵁ U) z h)
  simp only [CommRingCat.comp_apply] at e
  rw [e]
  first
  | rfl
  | (rw [Scheme.Hom.comp_app, CommRingCat.comp_apply]; rfl)
  | (simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply]; rfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B]
  {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, _⟩ := sabPull proved_CubePullSt f t
  exact ⟨_, ⟨m⟩⟩

theorem globalSections_rank_one_obj (hT : SecTwistSt) (o : Obj D l b s) {R : Type} [CommRing R] [IsLocalRing R] {x : Sp R ⟶ X} {t : SAB H (Sp R)}
    (m : SABMap t o.t x) : ∃ β : LB.Sec t.PP.L, ∀ σ : LB.Sec t.PP.L, ∃! a : R, ∀ i, σ.f i = constFn t.G.hom _ a * β.f i := by
  have := t.semi.smooth
  obtain ⟨w, gw', -⟩ := m.lin
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x (IsLocalRing.closedPoint R)) trivial
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) :=
    { isPreconnected_univ := isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
          isPreconnected_singleton.closure⟩
      toNonempty := ⟨IsLocalRing.closedPoint R⟩ }
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (IsLocalRing.closedPoint R))
  obtain ⟨-, ws, gs', -⟩ := t.sym
  exact globalSections_rank_one_local hT
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB
      ample := relAmple_pull m.cart.1 o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') U hU (fun y =>
        (congrArg (fun W => y ∈ W) (Scheme.preimage_eq_top_of_closedPoint_mem x hp)).mpr trivial) o.ample
      ktriv := kTriv_pull m.cart o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') o.ktriv
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 o.proper, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

set_option maxHeartbeats 2000000 in
theorem gen_baseChangeR (hS : SecBaseChangeAnySt) (hT : SecTwistSt) (o : Obj D l b s) {S K : Type} [CommRing S] [CommRing K]
    {x : Sp S ⟶ X} {t : SAB H (Sp S)} (m₀ : SABMap t o.t x) (θ : LB.Sec t.PP.L)
    (hθ : ∀ σ : LB.Sec t.PP.L, ∃ a : S, ∀ i, σ.f i = constFn t.G.hom _ a * θ.f i) (ψ : S →+* K) {t' : SAB H (Sp K)}
    (m : SABMap t' t (spMap ψ)) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (σ' : LB.Sec t'.PP.L)
    (hσ : ∀ y j k, m.φ y ∈ t.PP.L.U j → y ∈ t'.PP.L.U k →
      gs m.φ y _ (θ.f j) = (gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) (s' : LB.Sec t'.PP.L) :
    ∃! a : K, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := by
  classical
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m
  have : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 o.proper
  have : CompactSpace t'.G.left := QuasiCompact.compactSpace_of_compactSpace t'.G.hom
  have loc : ∀ (p : Ideal K) [p.IsPrime], ∃ (t₁ : SAB H (Sp (Localization.AtPrime p)))
      (m₁ : SABMap t₁ t' (spMap (algebraMap K _))), ∀ τ : LB.Sec t'.PP.L, ∃! a : Localization.AtPrime p,
        ∀ y j, m₁.φ y ∈ t'.PP.L.U j → gs m₁.φ y _ (τ.f j) = cst t₁.G.hom y a * gs m₁.φ y _ (σ'.f j) := fun p _ => by
    obtain ⟨t₁, ⟨m₁⟩⟩ := exists_sab (spMap (algebraMap K (Localization.AtPrime p))) t'
    refine ⟨_, m₁, fun τ => ?_⟩
    obtain ⟨n₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m₁
    obtain ⟨β, hβ⟩ := globalSections_rank_one_obj hT o n₁
    obtain ⟨w₁, g₁, -⟩ := m₁.lin
    have dn := fun τ => sec_pull_down ((isGen_iff w₁).1 g₁) t'.PP.isLB t₁.PP.isLB τ
    choose d hd using dn
    have hd' : ∀ τ y j k, m₁.φ y ∈ t'.PP.L.U j → y ∈ t₁.PP.L.U k →
        gs m₁.φ y _ (τ.f j) = (gw w₁ (𝟙 _) y j k).val * gs (𝟙 _) y _ ((d τ).f k) := fun τ y j k h h' =>
      (congrArg (fun q => gs q y _ (τ.f j)) (Category.id_comp _)).symm.trans (hd τ _ (𝟙 _) y j k h h')
    obtain ⟨a₀, ha₀, -⟩ := hβ (d σ')
    have h₀ : IsUnit a₀ := by
      by_contra hne
      obtain ⟨t₂, ⟨m₂⟩⟩ := exists_sab (spMap (IsLocalRing.residue (Localization.AtPrime p))) t₁
      obtain ⟨n₂, e₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
      obtain ⟨n₃, e₃⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₂
      have key : ∀ y j, n₃.φ y ∈ t.PP.L.U j → gs n₃.φ y _ (θ.f j) = 0 := fun y j hj => by
        obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB (m₁.φ (m₂.φ y))
        obtain ⟨k', hk'⟩ := exists_chart t₁.PP.isLB (m₂.φ y)
        have e : n₃.φ = m₂.φ ≫ m₁.φ ≫ m.φ := e₃.trans ((congrArg (· ≫ m.φ) e₂).trans (Category.assoc _ _ _))
        have hj' : m.φ (m₁.φ (m₂.φ y)) ∈ t.PP.L.U j := (congrArg (fun q => q y ∈ t.PP.L.U j) e).mp hj
        rw [e, gs_comp m₂.φ _ y _ hj', gs_comp m₁.φ _ _ _ hj', hσ _ j k hj' hk, map_mul, ← gs_stalkMap m₁.φ _ _ hk,
          hd' σ' _ k k' hk hk', (sec_eq_iff _ _ _ _).1 ha₀ k' _ hk', map_mul, map_mul, map_mul, cst_stalkMap, m₂.cart.1.w,
          cst_comp, (IsLocalRing.residue_eq_zero_iff _).2 hne, cst, map_zero, gs_zero _ y ⊤ trivial, zero_mul, mul_zero, mul_zero]
      clear e₃
      revert n₃
      rw [← spMap_comp, ← spMap_comp]
      exact fun n₃ key => gen_ne_zero hS o m₀ θ hθ _ n₃ key
    obtain ⟨u, rfl⟩ := h₀
    have iff : ∀ a : Localization.AtPrime p, (∀ y j, m₁.φ y ∈ t'.PP.L.U j → gs m₁.φ y _ (τ.f j) = cst _ y a * gs m₁.φ y _ (σ'.f j)) ↔
        ∀ i, (d τ).f i = constFn _ _ (a * u) * β.f i := fun a => by
      rw [sec_eq_iff]
      refine ⟨fun h k y hk => ?_, fun h y j hj => ?_⟩
      · obtain ⟨j, hj⟩ := exists_chart t'.PP.isLB (m₁.φ y)
        have := h y j hj
        rw [hd' τ y j k hj hk, hd' σ' y j k hj hk, mul_left_comm, Units.mul_right_inj, (sec_eq_iff _ _ _ _).1 ha₀ k y hk] at this
        rw [this, cst_mul, _root_.mul_assoc]
      · obtain ⟨k, hk⟩ := exists_chart t₁.PP.isLB y
        rw [hd' τ y j k hj hk, hd' σ' y j k hj hk, h k y hk, (sec_eq_iff _ _ _ _).1 ha₀ k y hk, cst_mul]
        ring
    obtain ⟨a, ha, hu⟩ := hβ (d τ)
    exact ⟨a * ↑u⁻¹, (iff _).2 (by rwa [Units.inv_mul_cancel_right]), fun a' h =>
      (Units.eq_mul_inv_iff_mul_eq u).2 (hu _ ((iff _).1 h))⟩
  have cadd : ∀ {Z : Scheme.{0}} (q : Z ⟶ Sp K) z a c, cst q z (a + c) = cst q z a + cst q z c := fun q z a c => by
    rw [cst, map_add, gs_eq q z ⊤ trivial, map_add, map_add, ← gs_eq q z ⊤ trivial, ← gs_eq q z ⊤ trivial]; rfl
  let I : Ideal K :=
    { carrier := {r | ∃ a, ∀ j, ∀ y ∈ t'.PP.L.U j,
        cst t'.G.hom y r * gs (𝟙 _) y _ (s'.f j) = cst t'.G.hom y a * gs (𝟙 _) y _ (σ'.f j)}
      add_mem' := fun ⟨a, ha⟩ ⟨c, hc⟩ => ⟨a + c, fun j y hy => by rw [cadd, cadd, add_mul, add_mul, ha j y hy, hc j y hy]⟩
      zero_mem' := ⟨0, fun j y _ => by rw [cst, map_zero, gs_zero _ y ⊤ trivial, zero_mul, zero_mul]⟩
      smul_mem' := fun r c ⟨a, ha⟩ => ⟨r * a, fun j y hy => by
        rw [smul_eq_mul, cst_mul, cst_mul, _root_.mul_assoc, ha j y hy, _root_.mul_assoc]⟩ }
  have top : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨t₁, m₁, h₁⟩ := loc p
    obtain ⟨c, hc, -⟩ := h₁ s'
    obtain ⟨⟨a, q⟩, hq⟩ := IsLocalization.surj p.primeCompl c
    let g : ∀ j, Γ(t'.G.left, t'.PP.L.U j) := fun j => constFn t'.G.hom _ q.1 * s'.f j + constFn t'.G.hom _ (-a) * σ'.f j
    have gv : ∀ {Z : Scheme.{0}} (r : Z ⟶ t'.G.left) z j, r z ∈ t'.PP.L.U j → gs r z _ (g j) =
        cst (r ≫ t'.G.hom) z q.1 * gs r z _ (s'.f j) + cst (r ≫ t'.G.hom) z (-a) * gs r z _ (σ'.f j) := fun r z j h => by
      rw [← gs_constFn _ _ r z h, ← gs_constFn _ _ r z h, ← gs_mul r z _ h, ← gs_mul r z _ h, gs_eq r z _ h, gs_eq r z _ h,
        gs_eq r z _ h, map_add, map_add]
    choose j hj using fun y : t'.G.left => exists_chart t'.PP.isLB y
    choose V hV hyV hVU using fun y : t'.G.left => exists_isAffineOpen_mem_and_subset (hj y)
    have kill : ∀ y, ∃ r ∈ p.primeCompl, ∀ z ∈ V y, cst t'.G.hom z r * gs (𝟙 _) z _ (g (j y)) = 0 := fun y => by
      obtain ⟨r, hr, h⟩ := loc_ker p.primeCompl m₁.cart.1 (hV y) (resG _ (hVU y) (g (j y))) fun z hz => by
        rw [show gs m₁.φ z (V y) (resG _ (hVU y) (g (j y))) = _ from gs_res m₁.φ z (hVU y) hz _, gv _ z _ (hVU y hz),
          hc z _ (hVU y hz), m₁.cart.1.w, cst_comp, cst_comp, ← _root_.mul_assoc, ← cst_mul, ← add_mul, mul_comm _ c, hq, map_neg]
        have : cst t₁.G.hom z (algebraMap K (Localization.AtPrime p) a) + cst t₁.G.hom z (-algebraMap K _ a) = 0 := by
          rw [cst, cst, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_neg, map_neg, map_neg, add_neg_cancel]
        rw [this, zero_mul]
      exact ⟨r, hr, fun z hz => (congrArg _ (gs_res (𝟙 _) z (hVU y) hz _).symm).trans (h z hz)⟩
    choose r hr hk using kill
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set t'.G.left)) (fun y => (V y).2)
      fun y _ => Set.mem_iUnion.2 ⟨y, hyV y⟩
    refine p.primeCompl.mul_mem (p.primeCompl.prod_mem fun y (_ : y ∈ F) => hr y) q.2
      (hI ⟨(∏ y ∈ F, r y) * a, fun i z hz => ?_⟩)
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
    have k := hk y z hzy
    rw [gv _ z _ (hVU y hzy), Category.id_comp, gs_compat s' (𝟙 _) z (hVU y hzy) hz, gs_compat σ' (𝟙 _) z (hVU y hzy) hz] at k
    have n₀ : cst t'.G.hom z a + cst t'.G.hom z (-a) = 0 := by
      rw [← cadd, add_neg_cancel, cst, map_zero, gs_zero _ z ⊤ trivial]
    simp only [← Finset.mul_prod_erase F r hy, cst_mul]
    refine (Units.mul_right_inj (gm (𝟙 _) z (t'.PP.L.U (j y) ⊓ t'.PP.L.U i) (t'.PP.L.g (j y) i))).1 ?_
    rw [eq_neg_of_add_eq_zero_right n₀] at k
    linear_combination (cst t'.G.hom z (∏ x ∈ F.erase y, r x)) * k
  obtain ⟨a, ha⟩ : (1 : K) ∈ I := top ▸ Submodule.mem_top
  have ea := (sec_eq_iff _ _ _ _).2 fun j y hy => ((_root_.one_mul _).symm.trans (congrArg (· * _) (cst_one _ _).symm)).trans
    (ha j y hy)
  refine ⟨a, ea, fun a' h' => Chart.eq_of_loc fun p _ => ?_⟩
  obtain ⟨t₁, m₁, h₁⟩ := loc p
  have k : ∀ c, (∀ i, s'.f i = constFn t'.G.hom _ c * σ'.f i) → ∀ y j, m₁.φ y ∈ t'.PP.L.U j →
      gs m₁.φ y _ (s'.f j) = cst t₁.G.hom y (algebraMap K _ c) * gs m₁.φ y _ (σ'.f j) := fun c h y j hj => by
    rw [h, gs_mul _ y _ hj, gs_constFn _ _ _ y hj, m₁.cart.1.w, cst_comp]
  exact (h₁ s').unique (k _ h') (k _ ea)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
