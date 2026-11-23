import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

theorem genRel_target {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B'} {Φ : B' ⟶ B₀} {wD : LB.Iso M' (M₀.pull Φ)} {w' : LB.Iso M (M'.pull φ)}
    {w : LB.Iso M (M₀.pull (φ ≫ Φ))} (T : Tri wD w' w) (hM₀ : M₀.IsLB) (hM' : M'.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hp : ∀ k, pt k ≫ φ = pt' k) (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt₀ k)
    {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (H : PMaps wD pt' pt₀ ε t' t₀ (𝟙 _))
    (t : LB.Gen (LB.LinComb M pt ε)) (x : F) : GenRel w' t t' x ↔ GenRel w t t₀ x := by
  have z : Sp F := (default : PrimeSpectrum F)
  have pe : ∀ k, pt' k z = φ (pt k z) := fun k => congrArg (fun g => g z) (hp k).symm
  have key : ∀ (j₀ : K → M₀.ι) (i : K → M'.ι) (q : K → M.ι), (∀ k, Φ (φ (pt k z)) ∈ M₀.U (j₀ k)) →
      (∀ k, φ (pt k z) ∈ M'.U (i k)) → (∀ k, pt k z ∈ M.U (q k)) →
      (((∏ k, gw w' (pt k) z (i k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M' pt' i) (t'.s i)).val ↔
      ((∏ k, gw w (pt k) z (j₀ k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val) := by
    intro j₀ i q h₀ h₁ h₂
    have a := T.prod (ε := ε) (h' := 𝟙 _) (φ' := pt') (fun k => (hp k).trans (Category.id_comp _).symm) _ (𝟙 _) z j₀ i q
      h₀ h₁ h₂
    have b := H _ (𝟙 _) z j₀ i (fun k => by show Φ (pt' k z) ∈ _; rw [pe]; exact h₀ k)
      (fun k => by show pt' k z ∈ _; rw [pe]; exact h₁ k)
    simp only [Category.id_comp] at a b
    rw [a, b, _root_.mul_assoc, Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k),
      Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k), mul_left_comm, Units.mul_right_inj]
  rw [genRel_iff w' t t' x z, genRel_iff w t t₀ x z]
  refine ⟨fun h => ⟨fun k => by rw [← Category.assoc, hp, hc, Category.id_comp], fun q j₀ h₀ h₂ => ?_⟩,
    fun h => ⟨hp, fun q i h₁ h₂ => ?_⟩⟩
  · choose i hi using fun k => exists_chart hM' (φ (pt k z))
    exact (key j₀ i q h₀ hi h₂).1 (h.2 q i hi h₂)
  · choose j₀ hj using fun k => exists_chart hM₀ (Φ (φ (pt k z)))
    exact (key j₀ i q hj h₁ h₂).2 (h.2 q j₀ hj h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'} {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)}
  {hD : IsPullDeg f a.D₀ a'.D₀}

section Witness

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {g : O'' →+* R} {f₀ : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}

set_option maxHeartbeats 1600000 in

theorem exists_witness (h : IsBC f a a' hD) (hf₀ : f₀ = g.comp f) (W : ArcWit Y a I f₀ u χ) :
    ∃ W' : ArcWit Y a' I g u χ, W'.t = W.t ∧ HEq W'.m W.m ∧ HEq W'.P W.P ∧ HEq (W'.φ ≫ proj hD) W.φ ∧
      (∀ y, HEq (W'.e y) (W.e (hD.xe y))) ∧
      ∃ w : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD)), HEq w W.w ∧ Tri hD.w W'.w w := by
  letI := H.starRing
  subst hf₀
  obtain ⟨t, m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := W
  have gpD := pull_grp hD
  have sq : φ ≫ a.D₀.P.A.hom = (P.D.toPre.P.A.hom ≫ spMap g) ≫ spMap f := by
    rw [s1.1.w, spMap_comp, Category.assoc]
  obtain ⟨φ', rfl, hb⟩ : ∃ φ' : P.D.toPre.P.A.left ⟶ a'.D₀.P.A.left, φ' ≫ proj hD = φ ∧
      φ' ≫ a'.D₀.P.A.hom = P.D.toPre.P.A.hom ≫ spMap g :=
    ⟨gpD.1.lift _ _ sq, gpD.1.lift_fst _ _ _, gpD.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback P.D.toPre.P.A a'.D₀.P.A (spMap g) φ' := gpD.cancel (s1.congr (spMap_comp f g) rfl) hb
  have he' : eSec P.D.toPre.P.A ≫ φ' = spMap g ≫ eSec a'.D₀.P.A := (cubeMapOf gp).e_comm
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff w).1 s2
  obtain ⟨w', T⟩ := exists_cancel a.D₀.P.isLB hD.w w gD g0 a'.D₀.P.isLB P.D.toPre.P.isLB
  have hc : ∀ y, (P.D.toPre.c (e (hD.xe y))).left ≫ φ' = spMap g ≫ (a'.D₀.c y).left := fun y => by
    refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (spMap g), ← spMap_comp]
      exact s5 _
    · rw [Category.assoc, hb, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  refine ⟨⟨t, m, P, φ', he', w', h.xeL.trans e, gp, (isGen_iff w').2 (T.pgen_cancel a.D₀.P.isLB gD g0), ?_, fun x => ?_, hc,
    fun F _ _ _ _ uF ha hu => ?_⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl, w, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ proj hD) (spMap (g.comp f)) he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec a.D₀.P.A) _ a'.D₀.rig a.D₀.rig (specOf f) _
      (rigPull_le (proj hD) (specOf f) hD.he a.D₀.P.L) (fun _ => rfl)).1 hD.w_rig
    rw [spMap_comp] at r₀
    exact (maps_iff w' _ (fun _ => eSec a'.D₀.P.A) _ P.D.toPre.rig a'.D₀.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' a'.D₀.P.L) (fun _ => rfl)).2 (T.pmaps_cancel a.D₀.P.isLB (fun _ => he') r₁ r₀)
  · refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h.act x]
      exact (s4 x).trans (Category.assoc _ _ _)
    · rw [Category.assoc, Category.assoc, Over.w, hb, ← Category.assoc, Over.w]
  · obtain ⟨_, hK, -⟩ := h.etaA 0
    letI : Algebra (FractionRing O') F :=
      ((algebraMap (FractionRing O'') F).comp (algebraMap (FractionRing O') (FractionRing O''))).toAlgebra
    have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (hK x)
    obtain ⟨k₁, k₂⟩ := s6 F uF (fun x => (hF x).trans (ha (f x))) hu
    have hj : jFK (R := R) F ≫ jK R ≫ spMap g = jFK (R := O'') F ≫ jK O'' := Compat.sq (φ := g) ha
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀' q x e1 e2 e3 e4 => ?_⟩
    · rw [h.be_eq]
      refine (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB (fun _ => ?_) (fun _ => ?_) (pmaps_psi hD F hF.sq y) _ _).2
        (k₁ (hD.xe y))
      · show (jFK (R := R) F ≫ jK R ≫ (P.D.toPre.c (e (hD.xe y))).left) ≫ φ' = jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left
        rw [Category.assoc, Category.assoc, hc, ← Category.assoc (jK R), ← Category.assoc]
        exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
      · show (jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left) ≫ proj hD =
          𝟙 _ ≫ jFK (R := O') F ≫ jK O' ≫ (a.D₀.c (hD.xe y)).left
        rw [Category.id_comp, Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (jK O''), ← Category.assoc]
        exact (congrArg (· ≫ _) hF.sq).trans (Category.assoc _ _ _)
    · obtain ⟨p, hp, hσ'⟩ : ∃ p : QkPt a.D₀ (FractionRing O') k, IsPullQk hD p p₀ ∧
          ((k = l.A ∧ ∃ v, HEq p (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
              HEq p (a.eta v) ∧ σ = Y.oF.eta v)) := by
        rcases hσ with ⟨rfl, v, h₁, h₂⟩ | ⟨rfl, v, hv, h₁, h₂⟩
        · exact ⟨a.etaA v, eq_of_heq h₁ ▸ h.etaA v, Or.inl ⟨rfl, v, HEq.rfl, h₂⟩⟩
        · exact ⟨a.eta v, eq_of_heq h₁ ▸ h.eta v, Or.inr ⟨rfl, v, hv, HEq.rfl, h₂⟩⟩
      obtain ⟨q₀, hq₀, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
      obtain ⟨hy, hg⟩ := hp.ext hF hq₀ e1
      have hy' : hD.xe q₀'.y = q₀.y := by rw [hy, AddEquiv.apply_symm_apply]
      refine k₂ yF hyF k p σ hσ' q₀ q x hq₀ (e2.trans (congrArg e hy')) (fun z => ?_) e4
      obtain ⟨z, rfl⟩ := hD.xe.surjective z
      obtain ⟨hψ, hm⟩ := hg.2 z
      have pm := (maps_iff hD.w _ _ _ (q₀'.g.s z) (q₀.g.s (hD.xe z)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm
      have k' := e3 z
      rw [h.be_eq, hy'] at k'
      exact (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB k'.1 hψ pm _ _).1 k'

end Witness

theorem exists_witness_baseChange (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (h : IsBC f a a' hD) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') {i : O' →+* R} {i' : O'' →+* R'} {κ : R →+* R'}
    (hκ : Function.Injective κ) (hI : I.map κ ≤ I') (hi : κ.comp i = i'.comp f) {u : R} {u' : R'} (hu : κ u = u')
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I i u χ) :
    ∃ (W' : ArcWit Y a' I' i' u' (spMap κ ≫ χ)) (hD₁ : IsPullDeg κ W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf κ)).obj W.t.G), IsMonHom bc.hom ∧ IsPullUnif κ hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf κ)) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ := by
  subst hu
  obtain ⟨W₁, hD₁, bc, mb, pu, hm, he, w₁, hφ, hw, T₁⟩ :=
    W.baseChange CubePf.cubePull hP hU h5 (qkPullExists hG) polOActPull hR hR' κ hκ hI
  obtain ⟨W', ht, hm', hP', hφ', he', w₂, hw', T₂⟩ := exists_witness h hi W₁
  obtain ⟨t₁, m₁, P₁, φ₁, _, _, e₁, _⟩ := W₁
  obtain ⟨t', m', P', φ', he₀, w', e', sp⟩ := W'
  dsimp only at ht
  subst ht
  obtain rfl := eq_of_heq hm'
  obtain rfl := eq_of_heq hP'
  exact ⟨⟨_, _, _, φ', he₀, w', e', sp⟩, hD₁, bc, mb, pu, hm, fun y => (congrArg hD₁.xe (eq_of_heq (he' y))).trans (he _),
    (eq_of_heq hφ').trans hφ, w₁, w₂, (hw'.trans hw).symm, T₁, T₂⟩

theorem admissibleBase_powerSeries_span_X (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    AdmBase (PowerSeries A) (Ideal.span {PowerSeries.X}) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

def IsArc (Y : Model Xo c β) {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} (a : ArcIn D l β A b) (ϖ : A)
    (χ : Sp (PowerSeries A) ⟶ Y.X) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := A)) ≫ spMap b ∧
  (∀ x : Sp (PowerSeries A), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
  (∀ x : Sp (PowerSeries A), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧
  Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ

def IsArcBase (A : Type) [CommRing A] [IsDomain A] (ϖ : A) : Prop :=
  (IsField A ∧ ϖ = 1) ∨ (IsDiscreteValuationRing A ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) A)

theorem IsArcBase.isPrincipalIdealRing {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) :
    IsPrincipalIdealRing A := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    infer_instance
  · infer_instance

theorem IsArcBase.ne_zero {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) : ϖ ≠ 0 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, h, -⟩
  exacts [one_ne_zero, h.ne_zero]

theorem IsArcBase.dvd_pow {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∣ ϖ ^ n := by
  rcases h with ⟨h, rfl⟩ | ⟨_, h, -⟩
  · obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
    exact ⟨0, y, by rw [pow_zero, hy]⟩
  · obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx h
    exact ⟨n, hn.dvd⟩

section PowerSeries

theorem map_comp_C' (f : O' →+* O'') :
    (PowerSeries.map f).comp (PowerSeries.C (R := O')) = (PowerSeries.C (R := O'')).comp f :=
  RingHom.ext fun x => PowerSeries.map_C f x

theorem IsBC.injective (h : IsBC f a a' hD) : Function.Injective f := by
  obtain ⟨_, hK, -⟩ := h.etaA 0
  intro x y hxy
  apply IsFractionRing.injective O' (FractionRing O')
  apply (algebraMap (FractionRing O') (FractionRing O'')).injective
  rw [hK, hK, hxy]

theorem exists_witness_powerSeries (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    [IsPrincipalIdealRing O'] [IsPrincipalIdealRing O''] (h : IsBC f a a' hD) {χ : Sp (PowerSeries O') ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ) :
    ∃ (W' : ArcWit Y a' (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O'')) PowerSeries.X
        (spMap (PowerSeries.map f) ≫ χ)) (hD₁ : IsPullDeg (PowerSeries.map f) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf (PowerSeries.map f))).obj W.t.G), IsMonHom bc.hom ∧
      IsPullUnif (PowerSeries.map f) hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf (PowerSeries.map f))) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ :=
  exists_witness_baseChange hG hP hU h5 h (admissibleBase_powerSeries_span_X O') (admissibleBase_powerSeries_span_X O'')
    (PowerSeries.map_injective f h.injective)
    (by rw [Ideal.map_span, Set.image_singleton, PowerSeries.map_X]) (map_comp_C' f) (PowerSeries.map_X f) W

theorem IsArc.baseChange (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (h : IsBC f a a' hD) {ϖ : O'} {ϖ' : O''} (hϖ : IsArcBase O' ϖ) (hϖ' : IsArcBase O'' ϖ')
    {χ : Sp (PowerSeries O') ⟶ Y.X} (hχ : IsArc Y a ϖ χ) : IsArc Y a' ϖ' (spMap (PowerSeries.map f) ≫ χ) := by
  have := hϖ.isPrincipalIdealRing
  have := hϖ'.isPrincipalIdealRing
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hχ
  have mem : ∀ (x : Sp (PowerSeries O'')) (s : PowerSeries O'),
      s ∈ (spMap (PowerSeries.map f) x).asIdeal ↔ PowerSeries.map f s ∈ x.asIdeal := fun _ _ => Iff.rfl
  refine ⟨?_, fun x => ?_, fun x hx => ?_, ?_⟩
  · rw [Category.assoc, h₁, ← Category.assoc, ← spMap_comp, map_comp_C', spMap_comp, spMap_comp, Category.assoc]
  · refine (h₂ (spMap (PowerSeries.map f) x)).trans ?_
    rw [mem, PowerSeries.map_X]
  · refine h₃ (spMap (PowerSeries.map f) x) fun hm => hx ?_
    rw [mem, map_mul, PowerSeries.map_X, PowerSeries.map_C] at hm
    rcases x.isPrime.mem_or_mem hm with hm | hm
    · obtain ⟨n, y, hy⟩ := hϖ'.dvd_pow ((map_ne_zero_iff f h.injective).2 hϖ.ne_zero)
      refine Ideal.mul_mem_right _ _ (x.isPrime.mem_of_pow_mem n ?_)
      rw [← map_pow, hy, map_mul]
      exact Ideal.mul_mem_right _ _ hm
    · exact Ideal.mul_mem_left _ _ hm
  · obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 h₄
    obtain ⟨W', -⟩ := exists_witness_powerSeries hG hP hU h5 h W
    exact (Y.hasArcData_iff _ _ _ _ _).2 ⟨W'⟩

end PowerSeries

end GlobalTheory.ArcPull
