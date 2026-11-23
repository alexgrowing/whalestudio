import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Heat.ShiftGauge

theorem toUnit_left {R : Type} [CommRing R] (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem exists_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  intro R _ _ Q O _ _ _ oa Y mu x hx ψ₀ hψ₀
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hq : IsMonHom Y.q := Y.q_linear.isMonHom
  set Tx : Y.H ⟶ Y.H := 𝟙 Y.H * (toUnit Y.H ≫ x) with hTx

  have hTq : Tx ≫ Y.q = Y.q * (toUnit Y.H ≫ x ≫ Y.q) := by
    rw [hTx, MonObj.mul_comp, Category.id_comp, Category.assoc]
  have hcq : cP Q Y.H mu * (Tx ≫ Y.q) = Y.q := by
    rw [hTq, cP, _root_.mul_comm, _root_.mul_assoc, ← MonObj.comp_mul (toUnit Y.H) (x ≫ Y.q) (Q.c mu), hx,
      MonObj.comp_one, _root_.mul_one]
  have e₁ : (cP Q Y.H mu).left = Y.H.hom ≫ (Q.c mu).left := by rw [cP, Over.comp_left, toUnit_left]
  have e₂ : (1 : Y.H ⟶ Q.P.A).left = Y.H.hom ≫ eSec Q.P.A := by rw [Hom.one_def, Over.comp_left, toUnit_left]; rfl
  let s := (Y.Φ Y.H Tx).s mu
  let w := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ ψ₀ Y.H.hom)
    (LB.pullGen Q.P.L _ _ Q.rig Y.H.hom)) s
  have hw : w.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hψ₀ _)
    (pullGen_isGen _ _ _ _ Q.rig_gen _)) ((Y.Φ Y.H Tx).isGen mu)
  have hF : FormEq (Sum.elim (Sum.elim (fun _ : PUnit => Y.H.hom ≫ (Q.c mu).left)
      (fun _ : PUnit => Y.H.hom ≫ eSec Q.P.A)) (DegPre.gtφT Q Y.H (Y.Φ Y.H Tx).b mu))
      (fun k => - Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => (1 : ℤ))) DegPre.gtε k)
      (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] := by
    intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.prod_unique, Fin.prod_univ_two]
    rw [GlobalTheory.TorusModel.prod_pt, Ray.Φ_b, hcq, e₁, e₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  obtain ⟨e, he, hve⟩ := exists_gen hL hF (LB.invGen Q.P.L _ _ w) (invGen_isGen _ _ _ _ hw)
  have hval : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      val e y.left z J = (val ψ₀ T.hom z J * val Q.rig T.hom z J *
        val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J)⁻¹ := by
    intro T y z J hJ
    have hy : y ≫ Tx = y * (toUnit T ≫ x) := by
      rw [hTx, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit Y.H) (toUnit T)]
    have hp := ((GlobalTheory.TorusModel.isPull_iff y (Y.Φ Y.H Tx) (Y.Φ T (y ≫ Tx))).1 (Y.rep.1 T Y.H y Tx)).2 mu z J hJ
    rw [hve _ _ z J hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w y, ← hy]
    rw [show val ((Y.Φ T (y ≫ Tx)).s mu) (𝟙 _) z J = _ from hp]
  refine ⟨e, he, ?_, fun T y z J hJ => ?_⟩
  · intro j V hV S _ φ x₁ x₁' c a a' ha ha' hV₁ hV₂ hqq hc
    subst ha ha'
    have hV' : Y.q.left ⁻¹ᵁ V ≤
        (LB.LinComb Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1]).U j := hV
    have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) → ∀ z,
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (valR b (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))) =
          gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
            (e.s j).val := by
      intro b hb z
      rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hV']
      refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z _ (hb trivial) _).trans ?_)
      rw [Category.id_comp]
      exact gs_res b z hV (hb trivial) _
    have hq' : x₁'.left ≫ Y.q.left = x₁.left ≫ Y.q.left := congrArg CommaMorphism.left hqq
    have hu : ∀ u : Over.mk (spMap φ) ⟶ Y.H, u ≫ Tx ≫ Y.q = (u ≫ Y.q) * (toUnit _ ≫ x ≫ Y.q) := fun u => by
      rw [hTq, MonObj.comp_mul, ← Category.assoc u (toUnit Y.H), toUnit_unique (u ≫ toUnit Y.H) (toUnit _)]
    have hT₀ : x₁' ≫ Tx ≫ Y.q = x₁ ≫ Tx ≫ Y.q := by rw [hu, hu, hqq]
    have hT : x₁'.left ≫ Tx.left ≫ Y.q.left = x₁.left ≫ Tx.left ≫ Y.q.left := congrArg CommaMorphism.left hT₀
    have hk : ∀ k, x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k =
        x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k :=
      Fin.forall_fin_two.2 ⟨hq', hT⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left => exists_chart hL (χ z)
    have hJ : Good Q.P.L z I := hI
    have hgv : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
        gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
          (e.s j).val = (trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] b z j
            (fun k => I (b ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) *
            val e b z I).val := fun b hb =>
      (gs_unit b z _ (hV (hb trivial)) _).trans (congrArg Units.val (gen_trans he b z (hV (hb trivial)) (hJ.mem _ b)))
    have htr : trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁'.left z j
          (fun k => I (x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) =
        trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁.left z j
          (fun k => I (x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) := by
      unfold trF
      exact Finset.prod_congr rfl fun k _ => congrArg (fun ψ => gm ψ z (Q.P.L.U (j k) ⊓ Q.P.L.U (I ψ)) (Q.P.L.g (j k) (I ψ)) ^ (![1, -1] : Fin 2 → ℤ) k) (hk k)
    have ve : val e x₁'.left z I = gm (𝟙 (Over.mk (spMap φ)).left) z ⊤ (unitOn (c (-mu))) * val e x₁.left z I := by
      have hb : (Y.Φ _ x₁').b = (Y.Φ _ x₁).b := by rw [Ray.Φ_b, Ray.Φ_b, hqq]
      have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ (toUnit _ ≫ x))).2 mu z I hJ
      have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' (toUnit _ ≫ x))).2 mu z I hJ
      rw [hb] at h2
      have h3 := hc mu z I hJ
      have h4 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁) hJ mu (-mu)
      have h5 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁') hJ mu (-mu)
      rw [add_neg_cancel, GlobalTheory.TorusModel.cv_zero _ hJ] at h4 h5
      rw [hb] at h5
      have h6 := hc (-mu) z I hJ
      rw [hval _ x₁ z I hJ, hval _ x₁' z I hJ]
      apply Additive.ofMul.injective
      have g1 := congrArg Additive.ofMul h1
      have g2 := congrArg Additive.ofMul h2
      have g3 := congrArg Additive.ofMul h3
      have g4 := congrArg Additive.ofMul h4
      have g5 := congrArg Additive.ofMul h5
      have g6 := congrArg Additive.ofMul h6
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at g1 g2 g3 g4 g5 g6 ⊢
      linear_combination (norm := abel) g1 - g2 - g4 + g5 + g6
    show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
    rw [germ _ hV₂ z, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, hgv _ hV₂, hgv _ hV₁, htr, ve,
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c (-mu) : S) = (unitOn (c (-mu))).val from rfl,
      gs_unit (𝟙 _) z ⊤ trivial, ← Units.val_mul]
    exact congrArg Units.val (_root_.mul_left_comm _ _ _)
  · rw [hval T y z J hJ]
    simp only [_root_.mul_assoc, inv_mul_cancel]

end GlobalTheory.Heat.ShiftGauge
