import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveAlgebraisationFormalEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlg

variable {X X' X'' : Scheme.{0}} {κ : Type}

def Carries (φ : X' ⟶ X) {H : LB X} {H' : LB X'} (w : LB.Iso H' (H.pull φ)) (s : κ → LB.Sec H)
    (s' : κ → LB.Sec H') : Prop :=
  ∀ j z (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
    gs φ z _ ((s j).f k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k')

theorem gs_stalk (r : X'' ⟶ X') (q : X' ⟶ X) (z : X'') (W : X.Opens) (h : q (r z) ∈ W)
    (a : Γ(X, W)) : (r.stalkMap z).hom (gs q (r z) W a) = gs (r ≫ q) z W a := by
  rw [gs_eq q (r z) W h, gs_eq (r ≫ q) z W h]
  exact Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ W) z h _

theorem Carries.at {φ : X' ⟶ X} {H : LB X} {H' : LB X'} {w : LB.Iso H' (H.pull φ)} {s : κ → LB.Sec H}
    {s' : κ → LB.Sec H'} (h : Carries φ w s s') (r : X'' ⟶ X') (j : κ) (z : X'') (k : H.ι) (k' : H'.ι)
    (hk : φ (r z) ∈ H.U k) (hk' : r z ∈ H'.U k') :
    gs (r ≫ φ) z _ ((s j).f k) = (Geo.Tor.gw w r z k k').val * gs r z _ ((s' j).f k') := by
  have hm : r z ∈ (H.pull φ).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (r.stalkMap z).hom (h j (r z) k k' hk hk')
  have g : ∀ a, (r.stalkMap z).hom (gm (𝟙 X') (r z) ((H.pull φ).U (fun _ => k) ⊓ H'.U k') a).val =
      (gm r z _ a).val := fun a => by
    rw [← gs_unit (𝟙 X') (r z) _ hm, gs_stalk r (𝟙 X') z _ hm, Category.comp_id, gs_unit r z _ hm]
  rw [gs_stalk r φ z _ hk, map_mul, gs_stalk r (𝟙 X') z _ hk', Category.comp_id] at e
  refine e.trans (congrArg (· * _) ?_)
  exact g _

def IsPull (φ : X' ⟶ X) {H : LB X} {H' : LB X'} (s : κ → LB.Sec H) (s' : κ → LB.Sec H') : Prop :=
  ∃ w : LB.Iso H' (H.pull φ), w.IsGen ∧ Carries φ w s s'

theorem exists_isPull (φ : X' ⟶ X) {H : LB X} (hH : H.IsLB) (s : κ → LB.Sec H) :
    ∃ s' : κ → LB.Sec (H.pull φ), IsPull φ s s' := by
  have hL := LB.isLB_pull hH φ
  have hw := CubePf.idIsoL_isGen hL
  choose s' hs' using fun j => GlobalTheory.SecPullIso.exists_pull φ H (H.pull φ) _ hH hL hw (s j)
  exact ⟨s', _, hw, hs'⟩

variable {F : X' ⟶ X} {F' : X'' ⟶ X'} {H : LB X} {H' : LB X'} {H'' : LB X''} {s : κ → LB.Sec H}
  {s' : κ → LB.Sec H'} {s'' : κ → LB.Sec H''}

theorem IsPull.comp (hH : H.IsLB) (hH' : H'.IsLB) (hH'' : H''.IsLB) (a : IsPull F s s') (b : IsPull F' s' s'') :
    IsPull (F' ≫ F) s s'' := by
  obtain ⟨w, hw, c⟩ := a
  obtain ⟨w', hw', c'⟩ := b
  rw [isGen_iff] at hw hw'
  obtain ⟨w'', T⟩ := exists_comp hH' w w' hw hw' hH hH''
  refine ⟨w'', (isGen_iff _).2 (T.pgen_comp hH' hw hw'), fun j z k k'' hk hk'' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hH' (F' z)
  rw [c.at F' j z k i hk hi, c' j z i k'' hi hk'', T _ (𝟙 _) z k i k'' hk hi hk'', Category.id_comp,
    Units.val_mul, _root_.mul_assoc]

theorem IsPull.cancel (hH : H.IsLB) (hH' : H'.IsLB) (hH'' : H''.IsLB) (a : IsPull F s s')
    (b : IsPull (F' ≫ F) s s'') : IsPull F' s' s'' := by
  obtain ⟨w, hw, c⟩ := a
  obtain ⟨w'', hw'', c''⟩ := b
  rw [isGen_iff] at hw hw''
  obtain ⟨w', T⟩ := exists_cancel hH w w'' hw hw'' hH' hH''
  refine ⟨w', (isGen_iff _).2 (T.pgen_cancel hH hw hw''), fun j z i k'' hi hk'' => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hH (F (F' z))
  have e := c'' j z k k'' hk hk''
  rw [c.at F' j z k i hk hi, T _ (𝟙 _) z k i k'' hk hi hk'', Category.id_comp,
    Units.val_mul, _root_.mul_assoc] at e
  exact (Units.mul_right_inj _).1 e

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A)
    {P : MvPolynomial σ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) P = c ^ e * MvPolynomial.eval₂ φ x P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hP (MvPolynomial.mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem gs_eval {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (U : X.Opens)
    (h : φ z ∈ U) (x : κ → Γ(X, U)) (P : MvPolynomial κ R) :
    gs φ z U (MvPolynomial.eval₂Hom (cst f U) x P) =
      MvPolynomial.eval₂ ((X'.presheaf.germ ⊤ z trivial).hom.comp (cst (φ ≫ f) ⊤)) (fun j => gs φ z U (x j)) P := by
  let G : Γ(X, U) →+* X'.presheaf.stalk z := (X'.presheaf.germ (φ ⁻¹ᵁ U) z h).hom.comp (φ.app U).hom
  have hG : ∀ a, gs φ z U a = G a := fun a => gs_eq φ z U h a
  simp only [hG]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  ext a
  rw [RingHom.comp_apply, ← hG, ← rs_cst f (le_top : U ≤ ⊤) a, gs_res _ z _ h, gs_eq φ z ⊤ trivial,
    RingHom.comp_apply]
  congr 1
  simp only [AbLaw.cst, RingHom.comp_apply, rs_self]
  rfl

theorem IsPull.eqn {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (hH : H.IsLB) (a : IsPull F s s')
    {t : ℕ} {P : MvPolynomial κ R} (hP : P.IsHomogeneous t)
    (h : ∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) P = 0) (k' : H'.ι) :
    MvPolynomial.eval₂Hom (cst (F ≫ f) (H'.U k')) (fun j => (s' j).f k') P = 0 := by
  obtain ⟨w, -, c⟩ := a
  refine fn_ext fun z hz => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (F z)
  have e := congrArg (gs F z _) (h k)
  rw [gs_eval f F z _ hk, gs_eq F z _ hk 0, map_zero, map_zero] at e
  simp only [fun j => c j z k k' hk hz] at e
  rw [eval₂_scale _ _ _ hP] at e
  rw [gs_eval (F ≫ f) (𝟙 _) z _ hz, gs_eq (𝟙 X') z _ hz 0, map_zero, map_zero, Category.id_comp]
  exact ((Units.isUnit _).pow t).mul_right_eq_zero.1 e

theorem exists_section (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y P : Over (Spec (CommRingCat.of V))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hj : ∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap V (IsLocalRing.maximalIdeal V) e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjV : ∀ e, j e ≫ P.hom = (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick V (IsLocalRing.maximalIdeal V) e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (j 0) (hjV 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (hjV 0) ≫
        pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have hpb : ∀ e, IsPullback (thickMap V (IsLocalRing.maximalIdeal V) e Y) (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom (thickObj V (IsLocalRing.maximalIdeal V) (e + 1) Y).hom
      (thickTrans V (IsLocalRing.maximalIdeal V) e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) (e + 1))) (h₂₂ := thick V (IsLocalRing.maximalIdeal V) (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.T.exists_projective_algebraisation_formal_embedding V (fun e => thickObj V (IsLocalRing.maximalIdeal V) e Y)
    (fun e => thickMap V (IsLocalRing.maximalIdeal V) e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick V (IsLocalRing.maximalIdeal V) e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy V P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjV]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjV]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimit.main V B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

theorem exists_hom_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y Z : Over (Spec (CommRingCat.of V))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ Y.hom) → (∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ g.left = f e := by
  intro V _ _ _ _ Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section V Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor V Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick V _ e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

end GlobalTheory.MorAlg
