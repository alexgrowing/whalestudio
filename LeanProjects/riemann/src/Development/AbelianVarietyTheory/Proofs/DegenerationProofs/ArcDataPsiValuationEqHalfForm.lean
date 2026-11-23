import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ArcPsiVal

theorem gm_const {K F : Type} [Field K] [Field F] (g : K →+* F) (z : Sp F) (U : (Sp K).Opens) (hz : spMap g z ∈ U)
    (C : Γ(Sp K, U)ˣ) (c : K) (hC : C.val = resTop _ (scal (𝟙 (Sp K)) c)) :
    (gm (spMap g) z U C).val = toStk z (g c) := by
  rw [gm_val _ _ _ hz, hC]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
    ((spMap g).naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  have e2 := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  refine (congrArg ((Sp F).presheaf.germ _ z hz).hom e).trans ?_
  refine (TopCat.Presheaf.germ_res_apply (Sp F).presheaf _ z hz _).trans ?_
  exact congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e2.symm

theorem value_of_qVal {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : DegPre R) (ϖ : R)
    (χ : P.X) (n : ℤ) (h : QForm.QVal P ϖ χ n) (F : Type) [Field F] [Algebra (FractionRing R) F] (z : Sp F)
    (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ c : FractionRing R, HasVal ϖ c n ∧
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val = toStk z (algebraMap (FractionRing R) F c) := by
  obtain ⟨e, -, c, hc, hC⟩ := genHasVal_units _ _ _ _ _ _ h
  obtain ⟨C, hCv, hCt⟩ := hC (fun _ => j)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
    simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have ht : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => hj)
  have hz' : Out.jK R (Out.jFK (R := R) F z) ∈ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    ht (show Out.jK R (Out.jFK (R := R) F z) ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz : Out.jFK (R := R) F z ∈ LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j) :=
    Set.mem_iInter.2 fun k => by
      rw [QForm.ptK_eq]; exact Set.mem_iInter.1 hz' k
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (𝟙 _) _ ht (e.s (fun _ => j)) z
  rw [Category.comp_id, hg] at hv
  refine ⟨_, hasVal_mul_unit hc v, ?_⟩
  have h2 := congrArg (gm (spMap (algebraMap (FractionRing R) F)) z
    (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))) hCt
  rw [map_mul, gm_res _ _ _ hz] at h2
  replace hv := (congrArg Units.val (gm_pull _ _ _ _ hz' (e.s (fun _ => j)))).trans hv
  rw [map_mul, map_mul]
  exact (congrArg Units.val h2).trans
    (congrArg₂ (· * ·) (gm_const (algebraMap (FractionRing R) F) z _ hz C c hCv) hv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (P : DegPre R) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (y : a.D₀.X) (χ : P.X)
    (hc : (P.c χ).left ≫ φ = spMap f ≫ (a.D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (hG : GenRel w (LB.pullGen _ _ _ (P.psi χ) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F))
        (algebraMap (FractionRing R) F (algebraMap R _ u) ^ (a.be y y / 2)))
    (z : Sp F) (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  obtain ⟨hp, hv⟩ := (genRel_iff w _ _ _ z).1 hG
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c χ).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c χ) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c χ)) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hpt : spMap f (cpt R) ∈ (a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have h1 : (x ≫ φ) (cpt R) ∈ a.D₀.P.L.U j₀ := hj₀
    rw [hc] at h1
    exact h1
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVle⟩ := (Sp O').isBasis_affineOpens.exists_subset_of_mem_open hpt
    ((a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀).isOpen
  have hle : Out.jK O' ⁻¹ᵁ V ≤ LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hVle hq
  obtain ⟨r, ⟨r, rfl⟩, hr⟩ := a.gen y (fun _ => j₀) V hV (Set.subset_univ _) hVle hle
  have htV : ⊤ ≤ spMap f ⁻¹ᵁ V := (top_le_iff_cpt _ _).2 hpV
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (spMap f) V htV r z
  have hcomp : Out.jFK (R := O') F ≫ Out.jK O' = spMap g ≫ spMap f := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  have hzV : Out.jK O' (Out.jFK (R := O') F z) ∈ V := by
    have h1 : (spMap g ≫ spMap f) z ∈ V := htV (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [← hcomp] at h1
    exact h1
  have hr' : pullU (Out.jK O') V r = res hle ((a.D₀.psi y).s (fun _ => j₀)) := Units.ext hr
  rw [← hcomp, ← gm_pull _ _ _ _ hzV, hr'] at hu₀
  replace hu₀ := (congrArg Units.val (gm_res (Out.jFK (R := O') F) z hle hzV _)).symm.trans hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * u₀, H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem q_eq_of_hasArcData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ _ b a W _ _ _ f u χ hfi h
  obtain ⟨t, m, P, φ, he, w, e, -, -, -, -, hc, hG⟩ := h
  refine ⟨t, m, P, e.toAddEquiv, fun ϖ Q n hϖ hQ hu y => ?_⟩
  let F := AlgebraicClosure (FractionRing W)
  let g : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective _ _)
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing W) F (algebraMap W _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.D.toPre.P.isLB ((P.D.toPre.c (e y)).left (cpt W))
  obtain ⟨v, hv⟩ := psi_value a f u P.D.toPre φ w y (e y) (hc y) F hF ((hG F _ hF rfl).1 y) z j hj
  obtain ⟨d, hd, hd'⟩ := value_of_qVal P.D.toPre ϖ (e y) _ (hQ (e y)) F z j hj
  have e1 := (toStk z).injective (hd'.symm.trans hv)
  rw [← map_zpow₀, ← map_mul] at e1
  have e2 := (algebraMap (FractionRing W) F).injective e1
  obtain ⟨s, hs⟩ := hu
  refine hasVal_unique hϖ hd ⟨s ^ (a.be y y / 2) * v, ?_⟩
  rw [e2, hs, mul_zpow, ← zpow_mul, Units.val_mul, map_mul, _root_.mul_assoc]
  congr 2
  exact (map_zpow (((algebraMap W (FractionRing W)) : W →* FractionRing W).comp (Units.coeHom W)) s _).symm

end GlobalTheory.ArcPsiVal

end
