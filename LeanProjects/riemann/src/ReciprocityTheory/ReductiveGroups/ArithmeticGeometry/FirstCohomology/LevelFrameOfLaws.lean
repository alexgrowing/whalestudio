import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
  TensorProduct
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

private lemma gs_eq_stalkMap_germ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (f.stalkMap y).hom (X.presheaf.germ U (f y) hy a) := by
  rw [gs, dif_pos hy]
  first
    | exact (Scheme.Hom.germ_stalkMap_apply f U y hy a).symm
    | (erw [Scheme.Hom.germ_stalkMap_apply])
    | (erw [Scheme.Hom.germ_stalkMap_apply]; rfl)

theorem sval_scal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
    {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)}
    {h : Y' ⟶ Y} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = sval s₂ (r ≫ h) z J := by
  have hψ : ∀ k, (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) : K ⊕ K' → L.ι) k =
      J (r ≫ (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) k) := by
    intro k
    cases k <;> simp [Category.assoc]
  have hcoh : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k))) := by
    intro k₁ k₂ he
    rw [hψ, hψ, he]
  have key := H (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) hcoh
  simp only [resTop, map_one, one_mul] at key
  have hz1 : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) := by
    show r z ∈ (⋂ k, _ : Set _)
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro k
    exact hJ (r ≫ φ₁ k)
  have hz2 : r z ∈ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    show r z ∈ (⋂ k, _ : Set _)
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro k
    exact hJ ((r ≫ h) ≫ φ₂ k)
  have hz3 : (r ≫ h) z ∈ LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    show (r ≫ h) z ∈ (⋂ k, _ : Set _)
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro k
    exact hJ ((r ≫ h) ≫ φ₂ k)
  unfold sval
  have hz3' : h (r z) ∈ LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)) := hz3
  have hg : Y'.presheaf.germ _ (r z) hz1 (s₁.f (fun k => J (r ≫ φ₁ k))) =
      (h.stalkMap (r z)).hom (Y.presheaf.germ _ (h (r z)) hz3' (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k)))) := by
    erw [Scheme.Hom.germ_stalkMap_apply]
    have e1 := TopCat.Presheaf.germ_res_apply Y'.presheaf
      (homOfLE (inf_le_left : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
        LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) ≤ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))))
      (r z) ⟨hz1, hz2⟩ (s₁.f (fun k => J (r ≫ φ₁ k)))
    have e2 := TopCat.Presheaf.germ_res_apply Y'.presheaf
      (homOfLE (inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
          LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) ≤
            h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k))))
      (r z) ⟨hz1, hz2⟩ ((h.app (LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)))).hom
        (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k))))
    rw [← e1]
    erw [← e2]
    first
      | exact (congrArg (fun t => Y'.presheaf.germ _ (r z) ⟨hz1, hz2⟩ t) key).symm
      | (rw [key]; done)
      | (erw [key]; done)
      | (simp only [key]; done)
      | (rw [key]; erw [map_one, one_mul])
      | (rw [key]; simp)
      | (rw [key]; rw [RingHom.map_one, one_mul])
  erw [gs_eq_stalkMap_germ r z _ hz1, gs_eq_stalkMap_germ (r ≫ h) z _ hz3, hg]
  first
    | rw [Scheme.Hom.stalkMap_comp]
    | erw [Scheme.Hom.stalkMap_comp]
  first
    | rfl
    | erw [CommRingCat.comp_apply]
    | simp only [CommRingCat.hom_comp, RingHom.comp_apply]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a * b) =
      (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a * (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b :=
    map_mul _ a b
  simp only [cst, gs, e, map_mul]
  simp

theorem cst_one {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 1 = 1 := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom 1 = 1 := map_one _
  simp only [cst, gs, e, map_one]
  simp

theorem cst_stalkMap {V : Type} [CommRing V] {X Z : Scheme.{0}} (r : Z ⟶ X) (p : X ⟶ Sp V) (z : Z) (a : V) :
    (r.stalkMap z).hom (cst p (r z) a) = cst (r ≫ p) z a := by
  have hp : p (r z) ∈ (⊤ : (Sp V).Opens) := trivial
  have hrp : (r ≫ p) z ∈ (⊤ : (Sp V).Opens) := trivial
  simp only [cst, gs, dif_pos hp, dif_pos hrp]
  first
    | (rw [Scheme.Hom.germ_stalkMap_apply]; rfl)
    | (erw [Scheme.Hom.germ_stalkMap_apply]; rfl)
    | (rw [Scheme.stalkMap_germ_apply]; rfl)
    | (simp [Scheme.Hom.germ_stalkMap_apply, Scheme.comp_app])
    | (have e := congrArg (fun g => g.hom ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)))
          (Scheme.Hom.germ_stalkMap r (p ⁻¹ᵁ ⊤) z hp)
       simpa using e)

theorem gs_sum {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp [gs, h, map_sum]

theorem gs_spec {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) (z : Sp C) (a : A) :
    cst (spMap φ) z a = cst (𝟙 _) z (φ a) := by
  have e : ((spMap φ).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (φ a) := by
    have := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    first
      | exact this.symm
      | simp
      | (simp only [CommRingCat.comp_apply] at this; exact this.symm)
  have h1 : (spMap φ) z ∈ (⊤ : (Sp A).Opens) := trivial
  have h2 : (𝟙 (Sp C) : Sp C ⟶ Sp C) z ∈ (⊤ : (Sp C).Opens) := trivial
  simp only [cst, gs, dif_pos h1, dif_pos h2]
  rw [e]
  rfl

theorem cst_ext {C : Type} [CommRing C] {a b : C} (h : ∀ z : Sp C, cst (𝟙 _) z a = cst (𝟙 _) z b) : a = b := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom a = (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom b := by
    apply TopCat.Presheaf.section_ext (Sp C).sheaf ⊤
    intro x hx
    have hx' : (𝟙 (Sp C) : Sp C ⟶ Sp C) x ∈ (⊤ : (Sp C).Opens) := trivial
    have := h x
    simp only [cst, gs, dif_pos hx'] at this
    exact this
  have := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom t) key
  simpa using this

theorem gs_fromSpec {X Z : Scheme.{0}} {U W : X.Opens} (hU : IsAffineOpen U) (le : U ≤ W) (r : Z ⟶ Sp Γ(X, U)) (z : Z)
    (f : Γ(X, W)) : gs (r ≫ hU.fromSpec) z W f = cst r z ((X.presheaf.map (homOfLE le).op).hom f) := by
  have h0 : hU.fromSpec (r z) ∈ U := by
    have h1 : hU.fromSpec (r z) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at h1
  have hz : (r ≫ hU.fromSpec) z ∈ W := le h0
  have hz' : r z ∈ (⊤ : (Sp Γ(X, U)).Opens) := trivial
  simp only [cst, gs, dif_pos hz, dif_pos hz']
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  first
    | rw [Scheme.Hom.stalkMap_comp]
    | rw [Scheme.stalkMap_comp]
    | erw [Scheme.Hom.stalkMap_comp]
  first
    | erw [CommRingCat.comp_apply]
    | rw [CommRingCat.hom_comp, RingHom.comp_apply]
    | simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    | erw [ConcreteCategory.comp_apply]
  congr 1
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [hU.fromSpec_app_of_le W le]
  first
    | erw [CommRingCat.comp_apply]
    | rw [CommRingCat.hom_comp, RingHom.comp_apply]
    | simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    | erw [ConcreteCategory.comp_apply]
  try (first
      | erw [CommRingCat.comp_apply]
      | rw [CommRingCat.hom_comp, RingHom.comp_apply]
      | simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      | erw [ConcreteCategory.comp_apply])
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem dvd_of_comb {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (σ : LB.Sec (LB.LinComb D.P.L φ ε)) {n : ℕ} (τ : Fin n → LB.Sec (LB.LinComb D.P.L φ ε)) (b : Fin n → F)
    (hb : ∀ i, 0 < v (b i)) (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval σ (r ≫ (DegPre.prB D F).left) z J =
        ∑ i, cst (r ≫ (fst (TF (R := V) F) D.P.A).left) z (b i) * sval (τ i) (r ≫ (DegPre.prB D F).left) z J)
    (j : K → D.P.L.ι) (y : D.P.A.left) (hy : y ∈ LB.wchart D.P.L φ j) :
    cst D.P.A.hom y ϖ ∣ gs (𝟙 _) y (LB.wchart D.P.L φ j) (σ.f j) := by
  have := D.P.isAb.smooth
  obtain ⟨U, hU, hyU, le⟩ := exists_isAffineOpen_mem_and_subset hy
  let alg : V →+* Γ(D.P.A.left, U) :=
    (D.P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  let _ : Algebra V Γ(D.P.A.left, U) := alg.toAlgebra
  let _ : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  have : Module.Flat V Γ(D.P.A.left, U) :=
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)).comp
      (D.P.A.hom.flat_appLE (isAffineOpen_top _) hU _)
  have s₀ : hU.fromSpec ≫ D.P.A.hom = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec D.P.A.hom (isAffineOpen_top _) hU (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  let iL : Γ(D.P.A.left, U) →+* Γ(D.P.A.left, U) ⊗[V] F := Algebra.TensorProduct.includeLeftRingHom
  let iR : F →+* Γ(D.P.A.left, U) ⊗[V] F := (Algebra.TensorProduct.includeRight (R := V)).toRingHom
  have sq : spMap iR ≫ (TF (R := V) F).hom = (spMap iL ≫ hU.fromSpec) ≫ D.P.A.hom := by
    rw [Category.assoc, s₀, ← spMap_comp]
    refine ((congrArg (spMap iR ≫ ·) (spMap_comp _ _).symm).trans (spMap_comp _ _).symm).trans (congrArg spMap ?_)
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := V) (A := Γ(D.P.A.left, U)) (B := F)).symm
  let r : Sp (Γ(D.P.A.left, U) ⊗[V] F) ⟶ (DegPre.BF D F).left := pullback.lift _ _ sq
  have r₁ : r ≫ (fst (TF (R := V) F) D.P.A).left = spMap iR := pullback.lift_fst _ _ _
  have r₂ : r ≫ (DegPre.prB D F).left = spMap iL ≫ hU.fromSpec := pullback.lift_snd _ _ _
  have key : ((D.P.A.left.presheaf.map (homOfLE le).op).hom (σ.f j)) ⊗ₜ[V] (1 : F) =
      ∑ i, ((D.P.A.left.presheaf.map (homOfLE le).op).hom ((τ i).f j)) ⊗ₜ[V] b i := cst_ext fun z => by
    choose J hJ using fun ψ : Sp (Γ(D.P.A.left, U) ⊗[V] F) ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have e := h _ r z J hJ
    rw [r₁, r₂] at e
    have hm : (spMap iL ≫ hU.fromSpec) z ∈ LB.wchart D.P.L φ j := le (hU.range_fromSpec.le ⟨spMap iL z, rfl⟩)
    have t := fun s : LB.Sec (LB.LinComb D.P.L φ ε) => ((gs_fromSpec hU le (spMap iL) z (s.f j)).trans
      (gs_spec iL z _)).symm.trans (sec_trans s (spMap iL ≫ hU.fromSpec) z hm (Good.mem hJ φ _))
    refine (t σ).trans ((congrArg _ e).trans ?_)
    rw [Finset.mul_sum, cst, map_sum, gs_sum _ z ⊤ trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm]
    refine (congrArg₂ (· * ·) (gs_spec iR z (b i)) (t (τ i)).symm).trans ((cst_mul _ z _ _).symm.trans ?_)
    exact congrArg (cst (𝟙 _) z) ((Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans
      (by rw [_root_.one_mul, _root_.mul_one]; rfl))
  have h1 : 0 < v (algebraMap V F ϖ) := by
    have := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    exact lt_of_lt_of_eq (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) this.symm
  obtain ⟨g, hg⟩ := dvd_of_tensor hϖ v ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
    (ReciprocityTheory.ChartRestriction.G.DVR.GC.v_alg_nonneg hϖ hv) h1 b hb _ _ key
  refine ⟨gs (𝟙 _) y U g, (gs_res (𝟙 _) y le hyU _).symm.trans ((congrArg (gs (𝟙 _) y U) hg).trans
    ((gs_mul _ y U hyU _ _).trans (congrArg₂ (· * ·) ?_ rfl)))⟩
  exact (gs_constFn D.P.A.hom U (𝟙 _) y hyU ϖ).trans (by rw [Category.id_comp])

theorem levelFrame_of_laws (hL : Laws) : DvrLevelFrame := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv O _ _ _ oa w0 hw a N hN haa k hk s s' hP χ σ σF c hσ hs hprim r hν
  have haa' : star a * a = (N : O) := (mul_comm _ _).trans haa
  by_contra hlt
  rw [not_le] at hlt
  apply hprim
  have hc : c ≠ 0 := fun h => by rw [h, AddValuation.map_zero] at hlt; exact not_top_lt hlt
  obtain ⟨u, hu, hcu, hrel⟩ := hP.1 χ
  obtain ⟨m, ψ, δ, e, he, hF, ve⟩ := pullGen_one hL.globalFns D F oa w0 hw a N hN haa' k χ u hu hcu
  obtain ⟨σ₁, hσ₁⟩ := exists_sec D.toPre.P.isLB hF (pullMulSec σ (oa.onB.act a).left e he)
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hν (star a • χ)
  have hQa : (Q (star a • χ) : ℚ) / ((k * N : ℕ) : ℚ) = (Q χ : ℚ) / k := by
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    rw [ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ]
    push_cast
    field_simp
  rw [hQa] at hva
  have hb : ∀ i, 0 < v (c⁻¹ * a₀ i) := fun i => by
    by_contra hn
    have e₀ : v (a₀ i) = v c + v (c⁻¹ * a₀ i) := by rw [← AddValuation.map_mul, mul_inv_cancel_left₀ hc]
    exact absurd ((hlt.trans_le (hva i)).trans_le (e₀.le.trans (add_le_of_nonpos_right (not_lt.1 hn)))) (lt_irrefl _)
  have vc : ∀ {k : ℕ} {α} (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have a₁ : (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
    congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
  have a₂ : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
    congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
  have div₁ := dvd_of_comb hϖ D.toPre F v hv σ₁ τ (fun i => c⁻¹ * a₀ i) hb (fun Z q z J hJ => by
    have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel Z q z J hJ
    have e₂ : sval (s.s χ) (q ≫ (aF D F oa a).left) z J = _ :=
      (congrArg (gs _ z _) (hs _)).trans (vc σF c (q ≫ (aF D F oa a).left) z _ (hJ.mem _ _))
    have e₃ := sval_scal hσ (q ≫ (aF D F oa a).left) z hJ
    rw [Category.assoc, a₂, ← Category.assoc] at e₃
    rw [Category.assoc, a₁] at e₂
    have e₄ : sval (s'.s (star a • χ)) q z J = ∑ i, cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z (a₀ i) *
        sval (τ i) (q ≫ (DegPre.prB D.toPre F).left) z J :=
      (congrArg (gs _ z _) (hsum _)).trans ((gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (sval_scal (hτ i) q z hJ))))
    have e₅ : sval (s'.s (star a • χ)) q z J = cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z c *
        sval σ₁ (q ≫ (DegPre.prB D.toPre F).left) z J := by
      rw [hσ₁ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, ← ve Z q z J hJ, ← e₃, ← _root_.mul_assoc]
      exact e₁.trans (congrArg₂ (· * ·) e₂ rfl)
    simp only [cst_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← e₄, e₅, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ hc, cst_one, _root_.one_mul])
  have := D.toPre.P.isAb.smooth
  obtain ⟨-, hflat, hsurj, -⟩ := hL.mulN _ D.toPre.P N hN
  have hm : oa.onB.act (star a) ≫ oa.onB.act a = mulA D.toPre.P.A N := by
    rw [← oa.onB.map_mul, haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  refine exists_div_sec D.toPre.P.A.hom hϖ.ne_zero σ fun j y hy => ?_
  obtain ⟨x, rfl⟩ := (mulA D.toPre.P.A N).left.surjective y
  apply dvd_descend (mulA D.toPre.P.A N).left x
  choose J hJ using fun ψ : D.toPre.P.A.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ x)
  have m₁ := Good.mem hJ (D.toPre.famφB (star a • χ)) (oa.onB.act (star a)).left
  have d₁ := map_dvd ((oa.onB.act (star a)).left.stalkMap x).hom (div₁ _ _ m₁)
  rw [cst_stalkMap, Over.w] at d₁
  have d₂ : cst D.toPre.P.A.hom x ϖ ∣ sval σ₁ (oa.onB.act (star a)).left x J :=
    (congrArg (cst D.toPre.P.A.hom x ϖ ∣ ·) (gs_stalkMap _ x _ m₁ _)).mpr d₁
  rw [hσ₁ _ _ x J hJ, sval_pullMulSec _ _ _ _ _ x hJ, Units.dvd_mul_right, ← Over.comp_left, hm] at d₂
  rw [cst_stalkMap, Over.w]
  exact (congrArg (cst D.toPre.P.A.hom x ϖ ∣ ·) ((gs_stalkMap _ x _ hy _).symm.trans
    (sec_trans σ (mulA D.toPre.P.A N).left x hy (Good.mem hJ _ _)))).mpr (d₂.mul_left _)

end ReciprocityTheory.ChartRestriction.G.H1
