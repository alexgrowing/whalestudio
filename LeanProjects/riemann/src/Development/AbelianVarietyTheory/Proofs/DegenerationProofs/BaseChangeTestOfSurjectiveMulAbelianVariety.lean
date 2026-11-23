import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.OmTest

open TopologicalSpace

theorem comp_mulN {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ ReciprocityTheory.ChartRestriction.G.Semi.mulN G n = x ^ n := by
  have e : ReciprocityTheory.ChartRestriction.G.Semi.mulN G n = (𝟙 G) ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  rw [e, MonObj.comp_pow, Category.comp_id]

theorem mulN_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.Semi.mulN G' n).left ≫ φ = φ ≫ (ReciprocityTheory.ChartRestriction.G.Semi.mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  rw [← comp_mulN, ← comp_mulN, Category.id_comp] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem surjective_mulN {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [GeometricallyIntegral G.hom]
    (n : ℕ) (ho : IsOpen (Set.range (ReciprocityTheory.ChartRestriction.G.Semi.mulN G n).left)) :
    Function.Surjective (ReciprocityTheory.ChartRestriction.G.Semi.mulN G n).left := by
  intro x
  let N := ReciprocityTheory.ChartRestriction.G.Semi.mulN G n
  let s := G.left.fromSpecResidueField x ≫ G.hom
  have : IsIntegral (pullback G.hom s) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom s)
  let X₀ : Over S := Over.mk s
  let T : Over S := Over.mk (pullback.snd G.hom s ≫ s)
  let x₀ : X₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField x) rfl
  let y : T ⟶ G := Over.homMk (pullback.fst G.hom s) pullback.condition
  let q : T ⟶ X₀ := Over.homMk (pullback.snd G.hom s) rfl
  have sec : ∀ g : X₀ ⟶ G, ∃ σ : X₀ ⟶ T, σ ≫ y = g ∧ σ ≫ q = 𝟙 _ := fun g =>
    ⟨Over.homMk (pullback.lift g.left (𝟙 _) ((Over.w g).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have ne : ∀ (z : T ⟶ G) (σ : X₀ ⟶ T), σ ≫ z = 1 → (z.left ⁻¹' Set.range N.left).Nonempty := fun z σ h => by
    have e : (1 : X₀ ⟶ G) ≫ N = σ ≫ z := by rw [h, comp_mulN, one_pow]
    exact ⟨σ.left (IsLocalRing.closedPoint _), (1 : X₀ ⟶ G).left (IsLocalRing.closedPoint _),
      congrArg (fun g => g.left (IsLocalRing.closedPoint _)) e⟩
  let z : T ⟶ G := (q ≫ x₀) * y
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec x₀⁻¹
  have : IrreducibleSpace T.left := inferInstanceAs (IrreducibleSpace (pullback G.hom s :))
  obtain ⟨t, ⟨a₀, ha⟩, b₀, hb⟩ := nonempty_preirreducible_inter (ho.preimage y.left.continuous)
    (ho.preimage z.left.continuous) (ne y σ₁ h₁)
    (ne z σ₂ (by rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]))
  obtain ⟨p₁, -, e₁⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback N.left y.left) a₀ t ha
  obtain ⟨p₂, -, e₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback N.left z.left) b₀ t hb
  have hW := IsPullback.of_hasPullback (pullback.snd N.left y.left) (pullback.snd N.left z.left)
  obtain ⟨w, -, -⟩ := Scheme.exists_preimage_of_isPullback hW p₁ p₂ (e₁.trans e₂.symm)
  let r₀ := pullback.fst (pullback.snd N.left y.left) (pullback.snd N.left z.left) ≫ pullback.snd N.left y.left
  let W : Over S := Over.mk (r₀ ≫ T.hom)
  let r : W ⟶ T := Over.homMk r₀ rfl
  have lift : ∀ (u : T ⟶ G) (a : W.left ⟶ G.left), a ≫ N.left = r₀ ≫ u.left → ∃ a' : W ⟶ G, a' ^ n = r ≫ u :=
    fun u a h => ⟨Over.homMk a (by
      change a ≫ G.hom = r₀ ≫ T.hom
      rw [← Over.w N, ← Category.assoc, h, Category.assoc, Over.w u]),
      (comp_mulN _ n).symm.trans (Over.OverMorphism.ext h)⟩
  obtain ⟨a, ea⟩ := lift y (pullback.fst _ _ ≫ pullback.fst _ _) (by
    simp only [r₀]
    rw [Category.assoc, Category.assoc, pullback.condition (f := N.left) (g := y.left)])
  obtain ⟨b, eb⟩ := lift z (pullback.snd _ _ ≫ pullback.fst _ _) (by
    simp only [r₀]
    rw [hW.w, Category.assoc, Category.assoc, pullback.condition (f := N.left) (g := z.left)])
  have e : (b * a⁻¹) ≫ N = r ≫ q ≫ x₀ := by
    rw [comp_mulN, mul_pow, inv_pow, ea, eb, MonObj.comp_mul, mul_inv_cancel_right]
  refine ⟨(b * a⁻¹).left w, (congrArg (fun g => g.left w) e).trans ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Z.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem mem_nonzeroLocus_iff {X Z : Scheme.{0}} {L : LB X} (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {k : L.ι}
    (hk : r z ∈ L.U k) : r z ∈ Out.nonzeroLocus θ ↔ IsUnit (gs r z _ (θ.f k)) := by
  rw [isUnit_gs_iff r z _ hk]
  refine ⟨fun h => ?_, fun h => Opens.mem_iSup.2 ⟨k, h⟩⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hj' : r z ∈ L.U j := X.basicOpen_le _ hj
  have hm : r z ∈ L.U k ⊓ L.U j := ⟨hk, hj'⟩
  have e := congrArg (gs r z _) (θ.compat k j)
  rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e
  rw [← isUnit_gs_iff r z _ hk, e]
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj' _).2 hj)

theorem exists_dvd_pow_mul {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (π a b : Γ(X, W))
    (h : ∀ z ∈ X.basicOpen π, gs (𝟙 X) z W b ∣ gs (𝟙 X) z W a) : ∃ n : ℕ, b ∣ π ^ n * a := by
  let I : Ideal Γ(X, W) := (Ideal.span {b}).colon {a}
  have : π ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hI, hP⟩
    by_contra hπ
    let y : PrimeSpectrum Γ(X, W) := ⟨P, hP⟩
    have hy : hW.fromSpec y ∈ X.basicOpen π := by
      have : y ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen π := by
        rw [hW.fromSpec_preimage_basicOpen]
        exact hπ
      exact this
    have hy' : hW.fromSpec y ∈ W := X.basicOpen_le _ hy
    have hd := h _ hy
    rw [gs_eq (𝟙 X) (hW.fromSpec y) W hy', gs_eq (𝟙 X) (hW.fromSpec y) W hy'] at hd
    have hl := hW.isLocalization_stalk' y hy'
    letI : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) := (X.presheaf.germ W _ hy').hom.toAlgebra
    have hl' : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec y)) P := hl
    have hm : algebraMap Γ(X, W) (X.presheaf.stalk (hW.fromSpec y)) a ∈
        (Ideal.span {b}).map (algebraMap Γ(X, W) (X.presheaf.stalk (hW.fromSpec y))) := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact hd
    obtain ⟨c, hc, hca⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl _ _ _).1 hm
    exact hc (hI (Submodule.mem_colon_singleton.2 hca))
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 (Submodule.mem_colon_singleton.1 hn)⟩

theorem dvd_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] [Algebra V K] [IsFractionRing V K] {H : Scheme.{0}} {f : H ⟶ Spec (.of V)} [Flat f]
    {HK : Scheme.{0}} [IsIntegral HK] {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
    {Hs : Scheme.{0}} [IsIntegral Hs] {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (IsLocalRing.ResidueField V))}
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))))
    {U : H.Opens} (a b : Γ(H, U)) {x : H} (hx : x ∈ U) (hfx : f x = IsLocalRing.closedPoint V)
    (hb : i (genericPoint Hs) ∈ H.basicOpen b) (h : ∀ y : HK, j y ∈ U → gs j y U b ∣ gs j y U a) :
    gs (𝟙 H) x U b ∣ gs (𝟙 H) x U a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  have hWU : W ≤ U := hWU
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hp := DvrModel.prime_res hϖ hs hW hxW hfx
  have hξ := (DvrModel.notMem_basicOpen_iff_specializes hϖ hs x).1 ((DvrModel.notMem_basicOpen_iff f hϖ x).2 hfx)
  obtain ⟨n, hn⟩ := exists_dvd_pow_mul hW ((H.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (.of V)).inv.hom ϖ))) ((H.presheaf.map (homOfLE hWU).op).hom a)
    ((H.presheaf.map (homOfLE hWU).op).hom b) fun z hz => by
    rw [Scheme.basicOpen_res] at hz
    obtain ⟨y, rfl⟩ := (DvrModel.opensRange_generic hϖ hK).ge hz.2
    rw [gs_res (𝟙 H) (j y) hWU hz.1, gs_res (𝟙 H) (j y) hWU hz.1]
    refine dvd_descend j y ?_
    rw [← gs_stalkMap j y U (hWU hz.1), ← gs_stalkMap j y U (hWU hz.1)]
    exact h y (hWU hz.1)
  obtain ⟨c, hc⟩ := hn
  have nd : ¬ (H.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (.of V)).inv.hom ϖ)) ∣ (H.presheaf.map (homOfLE hWU).op).hom b := by
    rintro ⟨d, hd⟩
    have m : i (genericPoint Hs) ∈ H.basicOpen ((H.presheaf.map (homOfLE hWU).op).hom b) := by
      rw [Scheme.basicOpen_res]
      exact ⟨hξ.mem_open W.isOpen hxW, hb⟩
    rw [hd, Scheme.basicOpen_mul, Scheme.basicOpen_res] at m
    exact (DvrModel.notMem_basicOpen_iff_specializes hϖ hs _).2 specializes_rfl m.1.2
  obtain ⟨d, rfl⟩ := hp.pow_dvd_of_dvd_mul_left n nd ⟨_, hc.symm⟩
  rw [mul_left_comm] at hc
  have e := mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) hc
  rw [← gs_res (𝟙 H) x hWU hxW b, ← gs_res (𝟙 H) x hWU hxW a, e, gs_mul (𝟙 H) x W hxW]
  exact dvd_mul_right _ _

variable {C : Core} (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) (E : T.Ext τ)

theorem isClosed_closedPoint : IsClosed ({τ.y₀ (IsLocalRing.closedPoint τ.V)} : Set C.Z) := by
  have := τ.j_loc
  have h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V := IsLocalRing.comap_closedPoint τ.j
  have e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V) := by
    rw [← h]
    exact (congrArg (fun g => g (cPt p)) τ.fac).symm
  rw [← e]
  exact GlobalTheory.ZH.isClosed_singleton_cPt y

theorem associated_generic (z : (pullback τ.H.hom (Out.jK τ.V) :)) (i : T.O₁.ι) (k : E.L.L.ι)
    (hi : τ.f (pullback.fst τ.H.hom (Out.jK τ.V) z) ∈ T.O₁.U i)
    (hk : (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left (pullback.fst τ.H.hom (Out.jK τ.V) z) ∈ E.L.L.U k) :
    Associated (gs (pullback.fst τ.H.hom (Out.jK τ.V) ≫ τ.f) z _ (T.s.f i))
      (gs (pullback.fst τ.H.hom (Out.jK τ.V) ≫ (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left) z _ (E.θ.f k)) := by
  let N : pullback τ.H.hom (Out.jK τ.V) ⟶ pullback τ.H.hom (Out.jK τ.V) :=
    (ReciprocityTheory.ChartRestriction.G.Semi.mulN ((Over.pullback (Out.jK τ.V)).obj τ.H) T.m).left
  have e₁ : N ≫ τ.φ = τ.φ ≫ (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.A T.m).left := mulN_comm τ.φ_cart T.m
  have e₂ : N ≫ pullback.fst τ.H.hom (Out.jK τ.V) =
      pullback.fst τ.H.hom (Out.jK τ.V) ≫ (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left :=
    mulN_comm (isGrpPullback_pullback τ.H (Out.jK τ.V)) T.m
  obtain ⟨l, hl⟩ := exists_chart T.L.isLB ((ReciprocityTheory.ChartRestriction.G.Semi.mulN C.A T.m).left (τ.φ z))
  have hi' : C.a (τ.φ z) ∈ T.O₁.U i := (congrArg (fun g => g z ∈ T.O₁.U i) τ.φ_f).mpr hi
  have hk' : pullback.fst τ.H.hom (Out.jK τ.V) (N z) ∈ E.L.L.U k := (congrArg (fun g => g z ∈ E.L.L.U k) e₂).mpr hk
  have hl' : τ.φ (N z) ∈ T.L.L.U l := (congrArg (fun g => g z ∈ T.L.L.U l) e₁).mpr hl
  have u₁ : IsUnit (gs (𝟙 _) (τ.φ z) _ (T.w.s (fun _ => i, fun _ => l)).val) := by
    refine (gs_unit (𝟙 _) (τ.φ z) _ ?_ _).symm ▸ Units.isUnit _
    exact And.intro (mem_pull.2 hi') (mem_pull.2 hl)
  have u₂ : IsUnit (gs (𝟙 _) (N z) _ (E.w.s (fun _ => k, fun _ => l)).val) := by
    refine (gs_unit (𝟙 _) (N z) _ ?_ _).symm ▸ Units.isUnit _
    exact And.intro (mem_pull.2 hk') (mem_pull.2 hl')
  rw [← τ.φ_f, ← e₂, gs_comp τ.φ C.a z _ hi', gs_comp N _ z _ hk', T.w_sec _ i l hi' hl, E.θ_eq _ k l hk' hl',
    map_mul, map_mul, ← gs_comp τ.φ _ z _ hl, ← gs_comp N _ z _ hl', e₁]
  exact (associated_unit_mul_left _ _ (u₁.map _)).trans (associated_unit_mul_left _ _ (u₂.map _)).symm

theorem mem_iff_special (h : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀)
    (hN : Function.Surjective (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left) (x : τ.H.left)
    (hx : τ.H.hom x = IsLocalRing.closedPoint τ.V) :
    τ.f x ∈ Out.nonzeroLocus T.s ↔ (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left x ∈ Out.nonzeroLocus E.θ := by
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible τ.V
  have hK := IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)
  have hs := IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have sp := fun x' (hx' : τ.H.hom x' = IsLocalRing.closedPoint τ.V) =>
    (DvrModel.notMem_basicOpen_iff_specializes hϖ hs x').1 ((DvrModel.notMem_basicOpen_iff τ.H.hom hϖ x').2 hx')
  set ξ := pullback.fst τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V))) (genericPoint _) with hξ
  set N := (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left with hN'
  obtain ⟨i, hi⟩ := exists_chart T.isLB (τ.f x)
  obtain ⟨k, hk⟩ := exists_chart E.L.isLB (N x)
  let U : τ.H.left.Opens := τ.f ⁻¹ᵁ T.O₁.U i ⊓ N ⁻¹ᵁ E.L.L.U k
  have hxU : x ∈ U := ⟨hi, hk⟩
  have hξU : ξ ∈ U := (sp x hx).mem_open U.isOpen hxU
  let a : Γ(τ.H.left, U) := (τ.f.appLE _ U inf_le_left).hom (T.s.f i)
  let b : Γ(τ.H.left, U) := (N.appLE _ U inf_le_right).hom (E.θ.f k)
  have ha : ξ ∈ τ.H.left.basicOpen a := by
    obtain ⟨x₀, hx₀, e₀⟩ := T.s_ne _ (isClosed_closedPoint τ)
    obtain ⟨x₁, e₁, e₁'⟩ := Scheme.exists_preimage_of_isPullback h x₀ _ e₀
    have m : ξ ∈ τ.f ⁻¹ᵁ Out.nonzeroLocus T.s :=
      (sp x₁ e₁').mem_open (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen (show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀)
    refine (isUnit_gs_iff (𝟙 _) ξ U hξU a).1 ?_
    rw [gs_appLE τ.f _ U inf_le_left (𝟙 _) ξ hξU, Category.id_comp]
    exact (mem_nonzeroLocus_iff T.s τ.f ξ hξU.1).1 m
  have hb : ξ ∈ τ.H.left.basicOpen b := by
    obtain ⟨x₀, hx₀, e₀⟩ := E.θ_ne
    obtain ⟨x₁, rfl⟩ := hN x₀
    have e₁ : τ.H.hom x₁ = IsLocalRing.closedPoint τ.V :=
      (congrArg (fun g => g x₁) (Over.w (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m))).symm.trans e₀
    have m : ξ ∈ N ⁻¹ᵁ Out.nonzeroLocus E.θ := (sp x₁ e₁).mem_open (N ⁻¹ᵁ Out.nonzeroLocus E.θ).isOpen hx₀
    refine (isUnit_gs_iff (𝟙 _) ξ U hξU b).1 ?_
    rw [gs_appLE N _ U inf_le_right (𝟙 _) ξ hξU, Category.id_comp]
    exact (mem_nonzeroLocus_iff E.θ N ξ hξU.2).1 m
  have as : ∀ z, pullback.fst τ.H.hom (Out.jK τ.V) z ∈ U →
      Associated (gs (pullback.fst τ.H.hom (Out.jK τ.V)) z U a) (gs (pullback.fst τ.H.hom (Out.jK τ.V)) z U b) :=
    fun z hz => by
      rw [gs_appLE τ.f _ U inf_le_left _ z hz, gs_appLE N _ U inf_le_right _ z hz]
      exact associated_generic T τ E z i k hz.1 hz.2
  have d₁ := dvd_of_generic hK hs a b hxU hx hb fun z hz => (as z hz).symm.dvd
  have d₂ := dvd_of_generic hK hs b a hxU hx ha fun z hz => (as z hz).dvd
  rw [gs_appLE τ.f _ U inf_le_left (𝟙 _) x hxU, gs_appLE N _ U inf_le_right (𝟙 _) x hxU, Category.id_comp,
    Category.id_comp] at d₁ d₂
  rw [mem_nonzeroLocus_iff T.s τ.f x hi, mem_nonzeroLocus_iff E.θ N x hk]
  exact ⟨isUnit_of_dvd_unit d₁, isUnit_of_dvd_unit d₂⟩

theorem surjective_mulN_test : Function.Surjective (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left := by
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  have hu : IsUnit (T.m : Γ(Sp τ.V, ⊤)) := by
    have := T.m_unit.map τ.y₀.appTop.hom
    rwa [map_natCast] at this
  have : Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left := GlobalTheory.GrpTangent.etale_mulN τ.H hu
  exact surjective_mulN τ.H T.m (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left.isOpenMap.isOpen_range

end GlobalTheory.ZJ.OmTest

namespace GlobalTheory.ZJ

open OmTest

theorem Core.Theta.bTest {C : Core} (L : C.Law) (T : C.Theta) : T.BTest L := by
  intro p _ y τ E x hx
  letI := L.grp
  have h := L.test p y τ
  have hN := surjective_mulN_test T τ
  have e := mulN_comm h T.m
  have w := Over.w (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m)
  have w' := Over.w (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m)
  have sq : IsPullback τ.f (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left τ.f :=
    IsPullback.of_bot (by rw [w, w']; exact h.1) e.symm h.1
  have sp : ∀ x', (ReciprocityTheory.ChartRestriction.G.Semi.mulN τ.H T.m).left x' = x → τ.H.hom x' = IsLocalRing.closedPoint τ.V :=
    fun x' h' => (congrArg (fun g => g x') w).symm.trans ((congrArg τ.H.hom h').trans hx)
  constructor
  · rintro ⟨g, hg, eg⟩
    obtain ⟨x', e₁, e₂⟩ := Scheme.exists_preimage_of_isPullback sq g x eg
    rw [← e₂]
    exact (mem_iff_special T τ E h.1 hN x' (sp x' e₂)).1 (e₁ ▸ hg)
  · intro hθ
    obtain ⟨x', e₂⟩ := hN x
    refine ⟨τ.f x', (mem_iff_special T τ E h.1 hN x' (sp x' e₂)).2 (e₂ ▸ hθ), ?_⟩
    exact (congrArg (fun g => g x') e).symm.trans (congrArg τ.f e₂)

theorem bTest_of_surjective_mulN : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (ReciprocityTheory.ChartRestriction.G.Semi.mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta), T.BTest L :=
  fun _ _ L T => Core.Theta.bTest L T

end GlobalTheory.ZJ
