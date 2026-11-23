import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtOfSucc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cst_dvd_of_cst_mul_eq_zero {S : Type} [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X) {a b : S}
    (hab : ∀ c, a * c = 0 → b ∣ c) {t : X.presheaf.stalk x} (ht : cst p x a * t = 0) : cst p x b ∣ t := by
  classical
  let ψ : S →+* (Spec (CommRingCat.of S)).presheaf.stalk (p x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (Spec (CommRingCat.of S)).presheaf.germ ⊤ (p x) trivial).hom
  have hψ : ψ.Flat := by
    have e := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S) (p x)
    rw [show ψ = _ from congrArg CommRingCat.Hom.hom e.symm, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    refine RingHom.Flat.comp ?_ ?_
    · exact RingHom.flat_algebraMap_iff.mpr inferInstance
    · exact RingHom.Flat.of_bijective
        (Spec.stalkIso (CommRingCat.of S) (p x)).symm.commRingCatIsoToRingEquiv.bijective
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp ψ
  have hφ : ∀ c, cst p x c = φ c := by
    intro c
    simp only [φ, ψ, RingHom.comp_apply, CommRingCat.hom_comp]
    unfold cst
    rw [gs_eq p x ⊤ trivial]
    exact (Scheme.Hom.germ_stalkMap_apply (f := p) ⊤ x trivial _).symm
  have hfl : φ.Flat := RingHom.Flat.comp hψ (AlgebraicGeometry.Flat.stalkMap p x)
  let _ : Algebra S (X.presheaf.stalk x) := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := hfl
  rw [hφ] at ht
  rw [hφ]
  have h0 : ∑ _i : Unit, a • t = 0 := by
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using ht
  obtain ⟨k, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Unit => a) (x := fun _ => t) h0
  have hd : ∀ j, b ∣ c () j := fun j => hab _ (by simpa using hc j)
  choose d hd using hd
  refine ⟨∑ j, φ (d j) * y j, ?_⟩
  have hy' : t = ∑ j, c () j • y j := hy ()
  rw [hy', Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hd j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, _root_.mul_assoc]

private theorem stalkMap_cst_eq_cst_comp {V : Type} [CommRing V] {Y Z : Scheme.{0}} (τ : Z ⟶ Y) (q : Y ⟶ Sp V) (z : Z)
    (a : V) : (τ.stalkMap z).hom (cst q (τ z) a) = cst (τ ≫ q) z a := by
  unfold cst
  have e1 : gs q (τ z) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      gs (𝟙 Y) (τ z) (q ⁻¹ᵁ ⊤) ((q.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := by
    rw [gs_pull (𝟙 Y) q (τ z) ⊤ (by simp) _, Category.id_comp]
  rw [e1, ← gs_stalkMap τ z (q ⁻¹ᵁ ⊤) (by simp), gs_pull τ q z ⊤ (by simp)]

private theorem cst_comp_specMap_eq_cst_apply {V Q : Type} [CommRing V] [CommRing Q] (π : V →+* Q) {Z : Scheme.{0}}
    (q : Z ⟶ Sp Q) (z : Z) (a : V) :
    cst (q ≫ Spec.map (CommRingCat.ofHom π)) z a = cst q z (π a) := by
  have e := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  unfold cst
  rw [e]
  exact (gs_pull q _ z ⊤ (by simp) _).symm

private theorem cst_zero_rings_of_integers {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 0 = 0 := by
  unfold cst
  rw [map_zero]
  exact gs_zero q z ⊤ (by simp)

theorem thickMap_stalkMap_eq_zero {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (G : Over (Spec (CommRingCat.of V))) [Flat G.hom] (e : ℕ)
    (y : (thickObj V (maximalIdeal V) e G).left)
    {t : (thickObj V (maximalIdeal V) (e + 1) G).left.presheaf.stalk (thickMap V (maximalIdeal V) e G y)}
    (ht : cst (fGl (maximalIdeal V) G (e + 1) ≫ G.hom) _ ϖ * t = 0) :
    ((thickMap V (maximalIdeal V) e G).stalkMap y).hom t = 0 := by
  classical
  have hm : maximalIdeal V = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hc : fGl (maximalIdeal V) G (e + 1) ≫ G.hom =
      pullback.snd G.hom (thick V (maximalIdeal V) (e + 1)) ≫ thick V (maximalIdeal V) (e + 1) :=
    pullback.condition
  have hc0 : fGl (maximalIdeal V) G e ≫ G.hom =
      pullback.snd G.hom (thick V (maximalIdeal V) e) ≫ thick V (maximalIdeal V) e :=
    pullback.condition
  have e3 : cst (fGl (maximalIdeal V) G (e + 1) ≫ G.hom) (thickMap V (maximalIdeal V) e G y) ϖ =
      cst (pullback.snd G.hom (thick V (maximalIdeal V) (e + 1))) (thickMap V (maximalIdeal V) e G y)
        (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1 + 1)) ϖ) := by
    rw [hc]; exact cst_comp_specMap_eq_cst_apply _ _ _ _
  rw [e3] at ht
  have hab : ∀ c : V ⧸ maximalIdeal V ^ (e + 1 + 1),
      Ideal.Quotient.mk (maximalIdeal V ^ (e + 1 + 1)) ϖ * c = 0 →
        Ideal.Quotient.mk (maximalIdeal V ^ (e + 1 + 1)) (ϖ ^ (e + 1)) ∣ c := by
    intro c hc1
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hm, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hc1
    obtain ⟨d, hd⟩ := hc1
    have h2 : ϖ * c' = ϖ * (ϖ ^ (e + 1) * d) := by rw [hd, pow_succ', _root_.mul_assoc]
    refine ⟨Ideal.Quotient.mk _ d, ?_⟩
    rw [mul_left_cancel₀ hϖ.ne_zero h2, map_mul]
  obtain ⟨u, rfl⟩ := cst_dvd_of_cst_mul_eq_zero _ _ hab ht
  rw [map_mul]
  have e4 : ((thickMap V (maximalIdeal V) e G).stalkMap y).hom (cst (pullback.snd G.hom (thick V (maximalIdeal V) (e + 1))) (thickMap V (maximalIdeal V) e G y)
        (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1 + 1)) (ϖ ^ (e + 1)))) = 0 := by
    rw [stalkMap_cst_eq_cst_comp]
    have e5 : cst (thickMap V (maximalIdeal V) e G ≫ pullback.snd G.hom (thick V (maximalIdeal V) (e + 1))) y
        (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1 + 1)) (ϖ ^ (e + 1))) =
        cst ((thickMap V (maximalIdeal V) e G ≫ pullback.snd G.hom (thick V (maximalIdeal V) (e + 1))) ≫ thick V (maximalIdeal V) (e + 1)) y
          (ϖ ^ (e + 1)) := (cst_comp_specMap_eq_cst_apply _ _ _ _).symm
    have e6 : cst (pullback.snd G.hom (thick V (maximalIdeal V) e) ≫ thick V (maximalIdeal V) e) y (ϖ ^ (e + 1)) =
        cst (pullback.snd G.hom (thick V (maximalIdeal V) e)) y
          (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)) (ϖ ^ (e + 1))) := cst_comp_specMap_eq_cst_apply _ _ _ _
    have hmem : ϖ ^ (e + 1) ∈ maximalIdeal V ^ (e + 1) :=
      Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) _
    rw [e5, Category.assoc, ← hc, ← Category.assoc, thickMap_comp_fGl, hc0, e6,
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem, cst_zero_rings_of_integers]
  rw [e4, zero_mul]

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def ExpandsAtUpTo (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (c : R) :
    Prop :=
  ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
    (∀ α ∉ S, cst (fGl I G e ≫ G.hom) y c * sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
      cst (fGl I G e ≫ G.hom) y c * ((wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL -
        ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val) = 0

theorem stalkMap_gs {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (W : X.Opens) (h : q (r z) ∈ W)
    (a : Γ(X, W)) : (r.stalkMap z).hom (gs q (r z) W a) = gs (r ≫ q) z W a := by
  have e1 : gs q (r z) W a = gs (𝟙 Y) (r z) (q ⁻¹ᵁ W) ((q.app W).hom a) := by
    rw [gs_pull (𝟙 Y) q (r z) W (by simpa using h) a, Category.id_comp]
  rw [e1, ← gs_stalkMap r z (q ⁻¹ᵁ W) h, gs_pull r q z W h a]

theorem stalkMap_gm {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (h : r z ∈ W)
    (a : Γ(Y, W)ˣ) : (r.stalkMap z).hom (gm (𝟙 Y) (r z) W a).val = (gm r z W a).val := by
  rw [← gs_unit (𝟙 Y) (r z) W (by simpa using h) a, ← gs_stalkMap r z W h, gs_unit r z W h a]

private theorem stalkMap_gs_eq_gs_comp {X Y Z : Scheme.{0}} (τ : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (W : X.Opens)
    (a : Γ(X, W)) : (τ.stalkMap z).hom (gs q (τ z) W a) = gs (τ ≫ q) z W a := by
  by_cases hm : q (τ z) ∈ W
  · exact stalkMap_gs τ q z W hm a
  · have hm' : (τ ≫ q) z ∉ W := by simpa using hm
    unfold gs
    rw [dif_neg hm, dif_neg hm', map_zero]

private theorem cst_mul_rings_of_integers {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst
  rw [map_mul]
  exact gs_mul q z ⊤ (by simp) _ _

private theorem stalkMap_sval_eq_sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Y' ⟶ Y) (τ : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) :
    (τ.stalkMap z).hom (sval s r (τ z) (fun ψ => J (τ ≫ ψ))) = sval s (τ ≫ r) z J := by
  rw [sval_of s r (τ z) _ (fun k => J (τ ≫ r ≫ φ k)) (fun k => rfl),
    sval_of s (τ ≫ r) z J (fun k => J (τ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact stalkMap_gs_eq_gs_comp τ r z _ _

private theorem stalkMap_thickMap_wv_succ_eq_wv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι)
    (jL : U.LG.L.ι) (hM : pGl U e y ∈ D.toPre.P.L.U jM) (hL : fGl I G e y ∈ U.LG.L.U jL) :
    ((thickMap R I e G).stalkMap y).hom (wv U (e + 1) (𝟙 _) (thickMap R I e G y) jM jL).val =
      (wv U e (𝟙 _) y jM jL).val := by
  rw [← wv_thickMap U e y jM jL hM hL]
  unfold wv
  refine stalkMap_gm _ _ _ ?_ _
  have hq : thickMap R I e G ≫ pGl U (e + 1) = pGl U e := U.gt_q e
  have hf : thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := thickMap_comp_fGl I e G
  refine ⟨?_, ?_⟩
  · have h1 : (thickMap R I e G ≫ pGl U (e + 1)) y ∈ D.toPre.P.L.U jM := by rw [hq]; exact hM
    exact Set.mem_iInter.2 fun _ => h1
  · have h1 : (thickMap R I e G ≫ fGl I G (e + 1)) y ∈ U.LG.L.U jL := by rw [hf]; exact hL
    exact Set.mem_iInter.2 fun _ => h1

private theorem stalkMap_val_eq_val_comp_of_good {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Y' ⟶ Y) (τ : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    (τ.stalkMap z).hom (val t r (τ z) (fun ψ => J (τ ≫ ψ))).val = (val t (τ ≫ r) z J).val := by
  have hm := hJ.mem φ (τ ≫ r)
  simp only [Category.assoc] at hm
  have hm2 : r (τ z) ∈ LB.wchart L φ (fun k => J (τ ≫ r ≫ φ k)) := by simpa using hm
  rw [val_of t r (τ z) _ (fun k => J (τ ≫ r ≫ φ k)) (fun k => rfl),
    val_of t (τ ≫ r) z J (fun k => J (τ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact ((congrArg _ (gs_unit r (τ z) _ hm2 _).symm).trans (stalkMap_gs τ r z _ hm2 _)).trans
    (gs_unit (τ ≫ r) z _ hm _)

end

theorem expandsAtUpTo_succ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (c : V)
    (h : ExpandsAtUpTo U (e + 1) k σ f S (ϖ * c)) : ExpandsAtUpTo U e k σ f S c := by
  intro y J hJ
  have : Smooth G.hom := U.smooth
  have : Flat G.hom := inferInstance
  have hq : thickMap V (maximalIdeal V) e G ≫ pGl U (e + 1) = pGl U e := U.gt_q e
  have hf : thickMap V (maximalIdeal V) e G ≫ fGl (maximalIdeal V) G (e + 1) = fGl (maximalIdeal V) G e :=
    thickMap_comp_fGl _ e G
  have hJ' : Good D.toPre.P.L (thickMap V (maximalIdeal V) e G y) (fun ψ => J (thickMap V (maximalIdeal V) e G ≫ ψ)) := fun ψ => by
    simpa using hJ (thickMap V (maximalIdeal V) e G ≫ ψ)
  obtain ⟨h1, h2⟩ := h _ _ hJ'
  have key : ∀ t, cst (fGl (maximalIdeal V) G (e + 1) ≫ G.hom) (thickMap V (maximalIdeal V) e G y) (ϖ * c) * t = 0 →
      cst (fGl (maximalIdeal V) G e ≫ G.hom) y c * ((thickMap V (maximalIdeal V) e G).stalkMap y).hom t = 0 := by
    intro t ht
    have h0 := thickMap_stalkMap_eq_zero hϖ G e y
      (t := cst (fGl (maximalIdeal V) G (e + 1) ≫ G.hom) (thickMap V (maximalIdeal V) e G y) c * t)
      (by rw [← _root_.mul_assoc, ← cst_mul_rings_of_integers]; exact ht)
    rwa [map_mul, stalkMap_cst_eq_cst_comp, ← Category.assoc, hf] at h0
  have hT : ∀ α, val (tG U (e + 1) α) (thickMap V (maximalIdeal V) e G) y J = val (tG U e α) (𝟙 _) y J := fun α => by
    have := (val_pull hJ (tG U (e + 1) α) (thickMap V (maximalIdeal V) e G) (𝟙 _)).symm.trans (val_corr hJ (U.gt_t e α) (𝟙 _))
    rwa [Category.id_comp] at this
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · have := key _ (h1 α hα)
    rwa [stalkMap_sval_eq_sval_comp, hq] at this
  · have hL' : fGl (maximalIdeal V) G (e + 1) (thickMap V (maximalIdeal V) e G y) ∈ U.LG.L.U jL := by
      rw [← hf] at hL; simpa using hL
    have hM : pGl U e y ∈ D.toPre.P.L.U (J (pGl U e)) := hJ (pGl U e)
    have := key _ (h2 jL hL')
    convert this using 2
    symm
    rw [map_sub, map_mul, map_sum, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]
    refine congrArg₂ (· - ·) (congrArg₂ (· * ·) ?_ ?_) (Finset.sum_congr rfl fun α _ => ?_)
    · have hj : J (thickMap V (maximalIdeal V) e G ≫ pGl U (e + 1)) = J (pGl U e) := by rw [hq]
      simp only [hj]
      exact congrArg (· ^ k) (stalkMap_thickMap_wv_succ_eq_wv U e y _ jL hM hL)
    · simp only [sv]
      exact (stalkMap_gs_eq_gs_comp (thickMap V (maximalIdeal V) e G) (fGl (maximalIdeal V) G (e + 1)) y _ _).trans (by rw [hf])
    · rw [map_mul, stalkMap_sval_eq_sval_comp, stalkMap_val_eq_val_comp_of_good _ _ _ _ hJ, Category.comp_id, hT, hq]

private theorem sval_eq_cst_mul_sval_of_secIsMul {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {p : Y ⟶ Spec (CommRingCat.of R)} {a : R} {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : SecIsMul p a s' s) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s' r z J = cst (r ≫ p) z a * sval s r z J := by
  unfold sval
  exact secIsMul_gs h r z _ (hJ.mem φ r)

private theorem cst_one_rings_of_integers {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 1 = 1 := by
  unfold cst
  rw [map_one, gs_eq q z ⊤ (by simp), map_one, map_one]

theorem expandsAt_cancel_pow : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (e n k : ℕ) (σ σ' : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom (ϖ ^ n) σ' σ → (∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f' α) (f α)) → U.ExpandsAt (e + n) k σ' f' → U.ExpandsAt e k σ f := by
  intro V _ _ _ ϖ hϖ D A G _ _ U e n k σ σ' f f' hσ hf hE
  have hA : ∀ e', pGl U e' ≫ D.toPre.P.A.hom = fGl (maximalIdeal V) G e' ≫ G.hom := fun e' =>
    (U.gt e').pG.w.trans pullback.condition.symm
  obtain ⟨S, hS⟩ := expandsAt_val U (e + n) k σ' f' hE
  have hstep : ∀ m c, ExpandsAtUpTo U (e + m) k σ f S (ϖ ^ m * c) → ExpandsAtUpTo U e k σ f S c := by
    intro m
    induction m with
    | zero => intro c h; simpa using h
    | succ m ih =>
      intro c h
      refine ih c (expandsAtUpTo_succ hϖ U (e + m) k σ f S (ϖ ^ m * c) ?_)
      rw [pow_succ', _root_.mul_assoc] at h
      exact h
  have h0 : ExpandsAtUpTo U (e + n) k σ f S (ϖ ^ n * 1) := by
    intro y J hJ
    obtain ⟨h1, h2⟩ := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at h1 h2
    have hsval : ∀ α, sval (f' α) (pGl U (e + n)) y J =
        cst (fGl (maximalIdeal V) G (e + n) ≫ G.hom) y (ϖ ^ n) * sval (f α) (pGl U (e + n)) y J := fun α => by
      rw [sval_eq_cst_mul_sval_of_secIsMul (hf α) _ _ hJ, hA]
    refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
    · have := h1 α hα
      rw [hsval α] at this
      rwa [_root_.mul_one]
    · have := h2 jL (by simpa using hL)
      have hsv : sv U k σ' (fGl (maximalIdeal V) G (e + n)) y jL =
          cst (fGl (maximalIdeal V) G (e + n) ≫ G.hom) y (ϖ ^ n) * sv U k σ (fGl (maximalIdeal V) G (e + n)) y jL :=
        secIsMul_gs hσ _ y _ (Set.mem_iInter.2 fun _ => by simpa using hL)
      have e8 : ∑ α ∈ S, sval (f' α) (pGl U (e + n)) y J * (val (tG U (e + n) α) (𝟙 _) y J).val =
          ∑ α ∈ S, cst (fGl (maximalIdeal V) G (e + n) ≫ G.hom) y (ϖ ^ n) *
            (sval (f α) (pGl U (e + n)) y J * (val (tG U (e + n) α) (𝟙 _) y J).val) :=
        Finset.sum_congr rfl fun α _ => by rw [hsval α, _root_.mul_assoc]
      rw [hsv, e8] at this
      rw [_root_.mul_one, mul_sub, Finset.mul_sum, sub_eq_zero, ← this]
      ring
  have h1' := hstep n 1 h0
  refine expandsAt_of_val U e k σ f S (fun y J hJ => ?_)
  obtain ⟨a1, a2⟩ := h1' y J hJ
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · have := a1 α hα
    rwa [cst_one_rings_of_integers, _root_.one_mul] at this
  · have := a2 jL hL
    rwa [cst_one_rings_of_integers, _root_.one_mul, sub_eq_zero] at this

end GlobalTheory
