import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings

noncomputable section

namespace GlobalTheory.TorusType

section Torus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusExt GlobalTheory.FormalPoint GlobalTheory.TorusModel GlobalTheory.ArcQ

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_char {S : Type} [CommRing S] {s : Sp S ⟶ Sp R} (g : GtPt D (Over.mk s)) (hb : g.b = 1) (χ : D.X) :
    ∃ u : S, ∀ (S' : Type) [CommRing S'] (f : S →+* S') (z : Sp S') J, Good D.P.L z J →
      (val (g.s χ) (spMap f) z J).val = toStkA z (f u) := by
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by
      rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty]; simp) (g.s χ) (LB.oneGen D.P.L) (g.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  refine ⟨valR (𝟙 (Sp S)) ⊤ ρ.val, fun S' _ f z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, ← FormalValue.valR_spMap f _ _ le_rfl, Category.comp_id]
  exact (toStkA_valR (spMap f) ⊤ z le_rfl ρ).symm

theorem val_tangent [IsLocalRing R] {φ : D.X → R} {ν : GtPt D (epsR R)} (ht : GtTanR ν) (hb : ν.b = 1)
    (hφ : ∀ (x : D.X) j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D (epsR R) ν.b x) j →
      TrivSqZeroExt.snd (valR (A := DualNumber R) (𝟙 _) _ ((ν.s x).s j).val) =
        TrivSqZeroExt.fst (valR (A := DualNumber R) (𝟙 _) _ ((ν.s x).s j).val) * φ x)
    (χ : D.X) {S' : Type} [CommRing S'] (f : DualNumber R →+* S') (z : Sp S') {J} (hJ : Good D.P.L z J) :
    (val (ν.s χ) (spMap f) z J).val = toStkA z (f (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (φ χ))) := by
  have := ConstTan.isLocalRing_dual R
  obtain ⟨u, hu⟩ := exists_char ν hb χ
  obtain ⟨g₀, hz, hp⟩ := ht
  have h₁ : u.fst = 1 := by
    obtain ⟨I, hI⟩ := ConstFam.exists_good' D.P.isLB (cpt R)
    have e := (val_one _).symm.trans ((val_corr hI (hz.2 χ) (𝟙 _)).symm.trans ((val_corr hI (hp.2 χ) (𝟙 _)).trans
      (val_pull hI _ _ _)))
    rw [Category.id_comp] at e
    exact toStkA_injective ((hu _ _ _ I hI).symm.trans ((congrArg Units.val e.symm).trans (map_one _).symm))
  have h₂ : u.snd = φ χ := by
    obtain ⟨I, hI⟩ := ConstFam.exists_good' D.P.isLB (cpt (DualNumber R))
    have hm := (top_le_iff_cpt (𝟙 (Sp (DualNumber R))) _).2 (hI.mem (DegPre.gtφT D (epsR R) ν.b χ) (𝟙 _))
    have e := hu _ (RingHom.id _) _ I hI
    rw [show spMap (RingHom.id (DualNumber R)) = 𝟙 _ from Spec.map_id _] at e
    have e' := toStkA_injective ((toStkA_valR (𝟙 _) _ _ hm _).trans e)
    exact (congrArg TrivSqZeroExt.snd e').symm.trans ((hφ χ _ hm).trans
      ((congrArg (fun q => TrivSqZeroExt.fst q * φ χ) e').trans (by rw [RingHom.id_apply, h₁, _root_.one_mul])))
  rw [hu _ f z J hJ, ← h₁, ← h₂, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

theorem isPull_of_isSmulPt [IsLocalRing R] (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O] [Module O D.X]
    (oa : D.OAct O) (a : O) (s : R) {φ : D.X → R} (hs : ∀ y, φ (star a • y) = s * φ y) {ν ν' : GtPt D (epsR R)}
    (ht : GtTanR ν) (hb : ν.b = 1)
    (hφ : ∀ (x : D.X) j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D (epsR R) ν.b x) j →
      TrivSqZeroExt.snd (valR (A := DualNumber R) (𝟙 _) _ ((ν.s x).s j).val) =
        TrivSqZeroExt.fst (valR (A := DualNumber R) (𝟙 _) _ ((ν.s x).s j).val) * φ x)
    (h : IsSmulPt oa a ν ν') : GtPt.IsPull (spMap (epsScaleR s)) ν ν' := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isSmulPt_iff hG oa a ν ν').1 h
  refine (isPull_iff (Over.homMk (spMap (epsScaleR s)) (LieCombBaseChange.epsScale_over s)) ν ν').2
    ⟨by rw [b, hb, MonObj.one_comp, MonObj.comp_one], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := epsR R) y J) := isCub_cubV D.cub hJ
  have e := (rosGen_add hG oa a hJ (1 : epsR R ⟶ D.P.A) 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.s01, C.face, C.s01, C.face, _root_.mul_one, _root_.one_mul] at e
  have e₀ : val₂ (rosGen hG oa a) y J (cP D _ χ) ν.b = 1 := by rw [hb]; exact mul_eq_left.1 e.symm
  rw [v χ y J hJ, e₀, _root_.mul_one]
  have e₁ := val_tangent ht hb hφ (star a • χ) (RingHom.id _) y hJ
  rw [show spMap (RingHom.id (DualNumber R)) = 𝟙 _ from Spec.map_id _] at e₁
  refine Units.ext (e₁.trans (Eq.trans (congrArg _ ?_) (val_tangent ht hb hφ χ (epsScaleR s) y hJ).symm))
  rw [hs]
  ext <;> simp [epsScaleR, _root_.mul_comm]

end Torus

section ThetaShiftProofs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem tr_comp {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : Out.DegPre R}
    {D₀ : Out.DegPre R₀} {φ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {e : D₀.X → D.X}
    {T : Over (Sp R)} {T₀ T₁ : Over (Sp R₀)} {h : T.left ⟶ T₀.left} {g : Out.GtPt D T} {g₀ : Out.GtPt D₀ T₀}
    {g₁ : Out.GtPt D₀ T₁} (H : ConstLie.Tr w e h g g₀) (k : T₀ ⟶ T₁) (p : Out.GtPt.IsPull k.left g₁ g₀) :
    ConstLie.Tr w e (h ≫ k.left) g g₁ := fun x =>
  ⟨fun i => by
    rw [(H x).1, Category.assoc, ConstTanRed.comp_gtφT D₀ k g₁.b g₀.b (Over.OverMorphism.ext p.1.symm) x i],
   fun Z r z J J' hJ hJ' => by
    rw [← (H x).2 Z r z J J' hJ hJ', val_corr hJ (p.2 x), val_pull hJ, Category.assoc]⟩

theorem main : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (φ : a.D₀.X →+ A) (ρ : 𝓞 E →+* A) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), (∀ (x : 𝓞 E) y, φ (H.bar x • y) = ρ x * φ y) → GtTanR ν → ν.b = Out.DegPre.zeroT a.D₀ (epsR A) → (∀ (x : a.D₀.X) j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR A) ν.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * φ x) → LieImg W ν v → ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (ρ x))) ≫ v.left := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W φ ρ ν v hρ ht hb hφ hv x
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := ConstLie.exists_tr W hG hv
  obtain ⟨ν', hν'⟩ := TorusModel.exists_isSmulPt hG a.oa x ν
  obtain ⟨g', hg'⟩ := ConstLie.exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (ConstLie.cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := ConstLie.Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  have p := isPull_of_isSmulPt hG a.oa x (ρ x) (hρ x) ht hb hφ hν'
  let k : epsR (PowerSeries A) ⟶ epsR (PowerSeries A) :=
    Over.homMk (spMap (epsScaleR (PowerSeries.C (R := A) (ρ x)))) (LieCombBaseChange.epsScale_over _)
  have p' := ConstLie.Tr.cancel W.spec.1 W.e.surjective hg
    (tr_comp (T₁ := epsR A) hg' (Over.homMk (spMap (epsScaleR (ρ x))) (LieCombBaseChange.epsScale_over _)) p) k
    (LieCombBaseChange.dualMap_epsScale _ _).symm
  exact congrArg (fun q => q.left) ((ConstLie.main hG E H Dw l Xo c O β Y A b a χ W ν').1.unique
    (ConstLie.lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)) (ConstLie.lieImg_of_tr W hg' (hp.pull k p')))

end ThetaShiftProofs

end GlobalTheory.TorusType
