import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans

section Generic

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem cst_mul_eq {R : Type} [CommRing R] (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    cst q z (a * b) = cst q z a * cst q z b := by
  rw [cst, map_mul]
  exact gs_mul q z ⊤ trivial _ _

theorem cst_comp_eq {R F : Type} [CommRing R] [CommRing F] (q : Z ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (z : Z)
    (a : R) : cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z a = cst q z (φ a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem sval_scale_const {R : Type} [CommRing R] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Spec (CommRingCat.of R))
    (c : R) (t : LB.Sec (LB.LinComb L φ ε)) (q : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale (scal p c) t) q z J = cst (q ≫ p) z c * sval t q z J :=
  (gs_mul q z _ (hJ.mem _ q) _ _).trans (congrArg (· * _)
    ((gs_res q z le_top (hJ.mem _ q) _).trans (ExpInt.gs_scal p q z c)))

theorem secLin_rescale (hL : L.IsLB) {R F : Type} [CommRing R] [Field F] (ρ : R →+* F)
    {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (p : Y ⟶ Spec (CommRingCat.of R))
    {π : Y' ⟶ Spec (CommRingCat.of F)} (hp : h ≫ p = π ≫ Spec.map (CommRingCat.ofHom ρ)) {c : Fin n → F}
    (a : Fin n → R) (ha : ∀ i, ρ (a i) ≠ 0) (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π (c i))) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε (fun i => SecOps.secScale (scal p (a i)) (s i)) h
      (fun i => scal π (c i / ρ (a i))) := by
  refine (FieldBaseChange.secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [(FieldBaseChange.secLin_iff_val hL _ _ _ _).1 H y J hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_scale_const _ _ _ _ _ hJ, ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, hp, ← Category.assoc, cst_comp_eq,
    ← _root_.mul_assoc, ← cst_mul_eq, div_mul_cancel₀ _ (ha i)]

end Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem expansion_eq (hR : AdmBase R I) (U : UnifPre I D A G) {k : ℕ} {σ : H0 U.LG.L k}
    {f g : ∀ α, D.toPre.SecB k α} (hf : ∀ e, U.ExpandsAt e k σ f) (hg : ∀ e, U.ExpandsAt e k σ g) : f = g := by
  have s : ∀ {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (a b : Γ(Y, W)),
      resTop W (scal p 1) * a + resTop W (scal p (-1)) * b = a - b := fun p W a b => by
    simp only [scal, map_neg, map_one, resTop]
    ring
  have h := (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![1, -1] (fun _ => σ) ![f, g]
    (fun i => by fin_cases i; exacts [hf, hg])).1 fun j => by
      rw [Fin.sum_univ_two]; exact (s _ _ _ _).trans (sub_self _)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((s D.toPre.P.A.hom _ _ _).symm.trans ?_)
  have := h α j
  rwa [Fin.sum_univ_two] at this

theorem LevelIso.exists_expansion (hG : GlobalFnsSt) (hR : AdmBase R I) {U : Unif I D A G} {U' : Unif I D' A' G'}
    {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j) {k : ℕ} (hk : 1 ≤ k) (τ : H0 U.LG.L k)
    (f : ∀ α, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k τ f) :
    ∃ (a : R) (τ' : H0 U'.LG.L k) (f' : ∀ α, D'.toPre.SecB k α), a ≠ 0 ∧ (∀ e, U'.ExpandsAt e k τ' f') ∧
      AgreeAll U.toUnifPre U'.toUnifPre hD j k (SecOps.secScale (scal G.hom a) τ) τ' ∧
      ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
        (SecOps.secScale (scal D.toPre.P.A.hom a) (f (hD.xe x))) := by
  obtain ⟨s, hs⟩ := exists_restrict U.toUnifPre k τ
  obtain ⟨F, ⟨r, hr, σ, f₀, h₁, h₂, h₃⟩, -⟩ := (U.expand k hk).1 s
  obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
  obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (U'.expand k hk).2 F'
  have e₁ : SecOps.secScale (scal G.hom r') σ = SecOps.secScale (scal G.hom (r' * r)) τ :=
    SecOps.sec_ext (scale_of_restrict _ hs h₁ r')
  have e₂ := expansion_eq hR U.toUnifPre (fun e => e₁ ▸ expandsAt_scale _ (h₃ e) r')
    (fun e => expandsAt_scale _ (hE e) (r' * r))
  have hp := fun x => congrFun e₂ (hD.xe x) ▸ integral_rel hD _ hF h₂ h₂' x
  exact ⟨r' * r, _, _, mul_ne_zero hr' hr, fun e => expandsAt_scale _ (h₃' e) r,
    hj.agreeAll (fun e => expandsAt_scale _ (hE e) _) (fun e => expandsAt_scale _ (h₃' e) _) hp, hp⟩

end GlobalTheory.GenericIso

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans GlobalTheory.GenericIso in

theorem expandsG_of_genericRel : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → ∀ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s' : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ (TFK (R := R) F ◁ Φ.hom).left ≫ UnifPre.gFK (G := G) F) z ∈ U.LG.L.U jL → (r ≫ UnifPre.gFK (G := G') F) z ∈ U'.LG.L.U jL' → gs (r ≫ (TFK (R := R) F ◁ Φ.hom).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) z jL (fun _ => jL') ^ k).val * gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => jL')) (σ'.f (fun _ => jL'))) → GlobalTheory.RigidSections.FamRel hD F s'.s s.s → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by
  intro hGl R _ _ I hR D D' A A' G G' _ _ _ _ _ _ U U' hD j hj Φ w hw F _ _ k hk σ σ' s s' hσ hs
    ⟨n, c, τ, f, hE, hG, hB⟩
  choose a τ' f' ha hE' hA hf using fun i => hj.exists_expansion hGl hR hk (τ i) (f i) (hE i)
  let ρ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hρ : ∀ i, ρ (a i) ≠ 0 := fun i =>
    (map_ne_zero_iff ρ ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (ha i)
  have hT : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom ρ) := (spMap_comp _ _).symm
  have pG : UnifPre.gFK (G := G) F ≫ G.hom =
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    have e₁ := Over.w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    have e₂ := Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    rw [← hT, Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) (e₁.trans e₂.symm)).trans (Category.assoc _ _ _))
  have pB : (DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom =
      (fst (TF (R := R) F) D.toPre.P.A).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [Over.w, ← hT]
    exact (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine ⟨n, fun i => c i / ρ (a i), τ', f', hE', ?_, fun x => ?_⟩
  · refine (FieldBaseChange.secLin_iff_val U'.LG.isLB _ _ _ _).2 fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at (Z := (UnifPre.GF (G := G') F).left) U.LG.isLB y
    have a₁ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ Φ.hom.left ≫
        pullback.fst G.hom (jK R) = (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F := by
      have e := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) Φ.hom)
      simp only [Over.comp_left] at e
      rw [Category.id_comp, Category.id_comp, ← Category.assoc, ← e, Category.assoc]
    have a₂ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ pullback.fst G'.hom (jK R) =
        𝟙 _ ≫ UnifPre.gFK (G := G') F := Category.assoc _ _ _
    have a₃ : (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
        𝟙 _ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left :=
      (Category.assoc _ _ _).trans
        (congrArg (𝟙 _ ≫ ·) (congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) Φ.hom)))
    have e₁ := hσ _ (𝟙 _) y _ _ (hJ ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F))
      (hJ' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
    have e₃ := secLin_val (secLin_rescale U.LG.isLB ρ G.hom pG a hρ hG) (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) y hJ
    refine (Units.mul_right_inj _).1 (e₁.symm.trans (e₃.trans ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e₂ := hw.2 k hk _ _ (hA i) _ (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) y
      (J ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F)) (J' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
      (by rw [a₁]; exact hJ _) (by rw [a₂]; exact hJ' _)
    rw [a₁, a₂] at e₂
    rw [ExpInt.gs_scal, ExpInt.gs_scal, a₃, mul_left_comm]
    refine congrArg (_ * ·) ?_
    refine (sval_of _ _ y J _ fun _ => ?_).trans (e₂.trans (congrArg (_ * ·) (sval_of _ _ y J' _ fun _ => ?_).symm))
    · rw [Category.comp_id]
    · rw [Category.comp_id]
  · refine secLin_transport D.toPre.P.isLB D'.toPre.P.isLB hD.w _ _ _ _ _ _ _ (prF hD F) _
      (famφ_eq D.toPre F (hD.xe x)) (famφ_eq D'.toPre F x) (famφB_pull hD x) (prF_snd hD F) _ _ (fun i y => ?_)
      _ _ _ _ (hs x) (fun i => hf i x) (secLin_rescale D.toPre.P.isLB ρ D.toPre.P.A.hom pB a hρ (hB (hD.xe x)))
    rw [ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, prF_fst]

end GlobalTheory
