import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]

omit [Algebra (FractionRing R) F] in

theorem secLin_of_secScal {X Y Y' W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₀ K K₁ : Type} [Fintype K₀] [Fintype K]
    [Fintype K₁] {φ₀ : K₀ → (W ⟶ X)} {ε₀ : K₀ → ℤ} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K₁ → (Y' ⟶ X)}
    {ε₁ : K₁ → ℤ} {h : Y ⟶ W} (p : Y' ⟶ Y) {h' : Y' ⟶ W} (hh : h' = p ≫ h) {ρ : Y ⟶ Spec (CommRingCat.of R)}
    {π : Y' ⟶ Spec (CommRingCat.of F)} (g : R →+* F) (hπ : p ≫ ρ = π ≫ Spec.map (CommRingCat.ofHom g)) {n : ℕ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {v : Fin n → LB.Sec (LB.LinComb L φ ε)}
    {σ : Fin n → LB.Sec (LB.LinComb L φ₀ ε₀)} {c d : Fin n → F} {r : Fin n → R} (hd : ∀ i, d i * g (r i) = c i)
    (hσ : ∀ i, GeneratorPullback.SecScal L φ ε (v i) φ₀ ε₀ (σ i) h (scal ρ (r i)))
    (hs : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = ∑ i, constVal (𝟙 Y' ≫ π) y (c i) * sval (v i) (𝟙 Y' ≫ p) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₀ ε₀ σ h' (fun i => scal π (d i)) := by
  subst hh
  refine (secLin_iff_val hL s₁ σ _ _).2 fun y J hJ => (hs y J hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have key : ∀ q : Y' ⟶ Y, sval (σ i) (q ≫ h) y J = gs q y ⊤ (scal ρ (r i)) * sval (v i) q y J := fun q => by
    rw [sval_of (σ i) (q ≫ h) y J (fun k => J (q ≫ h ≫ φ₀ k)) (fun k => by rw [Category.assoc])]
    have hm : q y ∈ LB.wchart L φ (fun k => J (q ≫ φ k)) ⊓
        LB.wchart L (fun k => h ≫ φ₀ k) (fun k => J (q ≫ h ≫ φ₀ k)) :=
      ⟨hJ.mem φ q, hJ.mem (fun k => h ≫ φ₀ k) q⟩
    have e := congrArg (gs q y _) (hσ i (fun k => J (q ≫ φ k)) (fun k => J (q ≫ h ≫ φ₀ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun t => J (q ≫ t)) e))
    exact ((gs_res q y _ hm _).trans (gs_pull q h y (LB.wchart L φ₀ (fun k => J (q ≫ h ≫ φ₀ k)))
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
      (e.trans ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res q y le_top hm _) (gs_res q y _ hm _))))
  rw [← Category.assoc, key, gs_scal, gs_scal, Category.assoc, hπ, ← Category.assoc, constVal_specMap,
    ← _root_.mul_assoc, ← hd i]
  congr 1
  exact (congrArg (gs _ y ⊤) (map_mul _ _ _)).trans (gs_mul _ y ⊤ trivial _ _)

omit [Algebra (FractionRing R) F'] in
theorem sval_fam_sum {k n : ℕ} (c : Fin n → F) (s : Fin n → Fam D F k) (α : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval ((∑ i, c i • s i).s α) r z J =
      ∑ i, constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c i) * sval ((s i).s α) r z J := by
  classical
  generalize (Finset.univ : Finset (Fin n)) = S
  induction S using Finset.induction_on with
  | empty => exact gs_zero' r z _ (hJ.mem _ r)
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add _ _ _ _ z hJ, ih,
      sval_smul _ _ _ _ z hJ]; rfl

variable (F) in
theorem exists_toFrac : ∃ θ : TF (R := R) F ⟶ TF (R := R) (FractionRing R),
    θ.left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ jFK (R := R) (FractionRing R) =
    jFK (R := R) F := (Spec.map_comp _ _).symm
  exact ⟨Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) h)), h⟩

theorem exists_expandsF (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (hk : 1 ≤ k) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  have e₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨σ', hσ'⟩ := exists_move A.isLB U.LG.isLB hw
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k : ℤ) (U.genF F).left e₁
    (g₂ := UnifPre.gFK (G := G) F) rfl t
  have H : IsPullback (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (pullback.snd G.hom (jK R))
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) :=
    (IsPullback.of_hasPullback _ _).flip
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := by
    have := A.isAb.proper
    have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
    have : IsLocallyNoetherian ((Over.pullback (jK R)).obj G).left :=
      LocallyOfFiniteType.isLocallyNoetherian (U.gen.hom.left ≫ A.A.hom)
    have : CompactSpace ((Over.pullback (jK R)).obj G).left :=
      QuasiCompact.compactSpace_of_compactSpace (U.gen.hom.left ≫ A.A.hom)
    have : IsNoetherian ((Over.pullback (jK R)).obj G).left := {}
    infer_instance
  obtain ⟨n, c, v, hv⟩ := (isExtension_pullOver H U.LG.isLB (I := Fin 1)
    (φ := fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))
    (φ' := fun _ => UnifPre.gFK (G := G) F) (fun _ => rfl)).exists_sum σ'
  choose S hS using fun i => ((U.expand k hk).1 (v i)).exists
  choose r hr σ f hσ hf he using hS
  obtain ⟨θ, hθ⟩ := exists_toFrac (R := R) F
  choose S' hS' using fun i => exists_famPull θ D.toPre hθ k (S i)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hg : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom g) := (Spec.map_comp _ _).symm
  have hd : ∀ i, c i * (g (r i))⁻¹ * g (r i) = c i := fun i => inv_mul_cancel_right₀
    ((map_ne_zero_iff g ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (hr i)) _
  refine ⟨∑ i, c i • S' i, σ', (isoRelM_iff w _ k _ e₁ _ (Category.id_comp _) t σ').2 fun y i₂ i₁ a₂ a₁ => ?_,
    n, fun i => c i * (g (r i))⁻¹, σ, f, he, ?_, fun α => ?_⟩
  · rw [Category.comp_id]
    exact hσ' _ (𝟙 _) y i₂ i₁ a₂ a₁
  · refine secLin_of_secScal U.LG.isLB (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left rfl g
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) H.w).trans
        ((Category.assoc _ _ _).trans (congrArg _ hg)))) hd hσ fun y J hJ => ?_
    refine (congrArg (fun x => sval x _ y J) hv).trans ((sval_sum' hJ _ _ _).trans
      (Finset.sum_congr rfl fun i _ => (sval_smul' hJ _ _ _).trans (congrArg _ ?_)))
    exact sval_pullOver H.w (fun _ => rfl) (v i) _ hJ
  · refine secLin_of_secScal D.toPre.P.isLB (toBK θ D.toPre).left
      (congrArg (fun q => q.left) (toBK_prB θ D.toPre)).symm g
      ((Over.w _).trans ((Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm.trans (congrArg _ hg))) hd
      (fun i => hf i α) fun y J hJ => ?_
    refine (sval_fam_sum D.toPre c S' α _ y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
    exact hS' i α _ _ y J hJ

theorem main : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s :=
  fun _ => exists_expandsF

end GlobalTheory.ExpansionTotal
