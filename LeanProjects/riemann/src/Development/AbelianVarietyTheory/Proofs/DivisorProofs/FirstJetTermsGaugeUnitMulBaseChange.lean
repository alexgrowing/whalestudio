import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinCombStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

private theorem pre_lemma {Z Y X : Scheme.{0}} (x : Z ⟶ Y) (y : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ⊤ ≤ (x ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (show x.base p ∈ (⊤ : Y.Opens) from trivial)
  exact this

private theorem norm_natCast_le_one_kummer_theta_logarithms {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := pre_lemma _ _ _ h
  unfold valR
  rw [dif_pos h, dif_pos h']
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h (by intro _ _; trivial)]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e5 := fun w => congrArg (fun g => CommRingCat.Hom.hom g w) e2
  simp only [Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e5
  simp only [spMap, CommRingCat.hom_comp, RingHom.comp_apply, ← e5]
  congr 1

private theorem univ_le_preimage_inf_of_univ_le {Z X : Scheme.{0}} (y : Z ⟶ X) (U V : X.Opens) (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro p hp
  exact ⟨h1 hp, h2 hp⟩

private theorem alg_lemma_5 {S : Type} [CommRing S] {n : ℕ} (a b : Fin n → S) (Ps g1 g2 g T : S)
    (h : Ps * (g1 * g2) = T) : (∑ i, a i * (Ps * b i)) * (g1 * (g2 * g)) = T * ∑ i, a i * (b i * g) := by
  rw [← h, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private theorem mul_prod_four_rearrange {S : Type} [CommRing S] (a0 a1 a2 a3 b0 b1 b2 b3 : S) :
    a0 * a1 * a2 * a3 * (b0 * b1 * b2 * b3) = (a0 * b2) * (a1 * b0) * (a2 * b1) * (a3 * b3) := by
  ring

theorem jc_eq_unit_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  intro R _ _ D C _ _ N ν gm₀ gm htan hpull k J hJ
  have hb : gm.b.left = spMap (dualMap (toF R C)) ≫ gm₀.b.left := hpull.1
  have hν : ∀ (P : Sp (DualNumber C) ⟶ D.P.A.left), ⊤ ≤ P ⁻¹ᵁ D.P.L.U (ν.J (redE C ≫ P)) :=
    fun P => GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction C P _ (ν.good _)
  have hQ : redE C ≫ gm.b.left = (TF (R := R) C).hom ≫ eSec D.P.A := by
    rw [hb, ← Category.assoc, gl_redE, Category.assoc, gl_tan D gm₀ htan, ← gl_TF R C]
  have hJb : ∀ (p : Sp (DualNumber R) ⟶ D.P.A.left), ⊤ ≤ (spMap (dualMap (toF R C)) ≫ p) ⁻¹ᵁ D.P.L.U (J p) :=
    fun p => pre_lemma _ _ _ (hJ p)
  have hc0 : ⊤ ≤ gm.b.left ⁻¹ᵁ (D.P.L.U (ν.J (redE C ≫ gm.b.left)) ⊓ D.P.L.U (J gm₀.b.left)) :=
    univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb]; exact hJb _)
  have hcR : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left) :=
    top_le_wchart _ _ _ _ (fun _ => by rw [Category.id_comp, ← gl_tan D gm₀ htan]; exact pre_lemma _ _ _ (hJ _))
  refine ⟨(isUnit_trV D.P.L gm.b.left _ _ hc0 (k : ℤ)).unit, ?_, ?_, ?_⟩
  · unfold TanExp.rigValD valR
    rw [dif_pos hcR]
    exact (((D.rig.s _).isUnit.map _).map _).ne_zero
  · rw [IsUnit.unit_spec]
    have e1 : (trV D.P.L gm.b.left (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ)).fst =
        trV D.P.L (redE C ≫ gm.b.left) (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ) := by
      unfold trV
      exact (norm_natCast_le_one_kummer_theta_logarithms (TrivSqZeroExt.fstHom C C C).toRingHom _ _ _ hc0).symm
    have e2 : toF R C (TanExp.rigValD D (J gm₀.b.left)) = valR (TF (R := R) C).hom
        (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left)) (D.rig.s fun _ => J gm₀.b.left).val := by
      unfold TanExp.rigValD
      rw [gl_TF R C]
      have h5 := norm_natCast_le_one_kummer_theta_logarithms (toF R C) (𝟙 _) _ (D.rig.s fun _ => J gm₀.b.left).val hcR
      rw [Category.comp_id] at h5
      exact h5.symm
    have hQ1 : ⊤ ≤ ((TF (R := R) C).hom ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U (J gm₀.b.left) := by
      rw [← hQ, hb, ← Category.assoc]; exact pre_lemma _ _ _ (hJ _)
    have e3 := GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) C).hom
      (fun _ => ν.J ((TF (R := R) C).hom ≫ eSec D.P.A)) (fun _ => J gm₀.b.left)
      (top_le_wchart _ _ _ _ (fun _ => ν.good _)) (top_le_wchart _ _ _ _ (fun _ => hQ1))
    rw [e1, e2, hQ]
    simp only [NumOf.rg, vF]
    unfold valF
    unfold valR at e3 ⊢
    rw [e3]
    simp only [Finset.univ_unique, Finset.prod_singleton, mul_pow]
    rw [trV_pow D.P.L _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (ν.good _) hQ1), _root_.one_mul]
  · intro s n c f hlin α
    have hyP : ∀ {Z : Scheme.{0}} (g : D.P.A.left ⟶ Z),
        (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left ≫
          (D.prB C).left ≫ g = gm.b.left ≫ g :=
      fun g => by rw [← Category.assoc, gl_prB']
    have hsec := GlobalTheory.T.sectionValue_linear_relation_linComb D.P.L (D.famφ C (ν.eX α)) (DegPre.famε k) (s.s (ν.eX α)) (D.famφB (ν.eX α))
      (DegPre.famε k) (fun i => f i (ν.eX α)) (D.prB C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))
      (hlin _)
      (fun i => ν.J (redE C ≫ (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C)
        gm.b).left ≫ D.famφ C (ν.eX α) i))
      (fun i => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
      (by
        intro k₁ k₂ e
        rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢
        · rw [e]
        · rw [← hyP, ← e]
        · rw [← hyP, e]
        · rw [← hyP, ← hyP, e])
      (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left
      (top_le_wchart _ _ _ _ (fun i => hν _))
      (top_le_wchart _ _ _ _ (fun i => by rw [gl_prB']; exact hν _))
    have hS : ∀ i, valR gm.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
        ((f i (ν.eX α)).f fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j)) =
        (∏ j, trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) j) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
          (J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) (DegPre.famε k j)) *
        dualMap (toF R C) (valR gm₀.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
          ((f i (ν.eX α)).f fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))) := by
      intro i
      have hA : ⊤ ≤ gm₀.b.left ⁻¹ᵁ LB.wchart D.P.L (D.famφB (ν.eX α)) (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) :=
        top_le_wchart _ _ _ _ (fun j => hJ _)
      rw [GlobalTheory.T.sectionValue_linComb_change_of_charts D.P.L (D.famφB (ν.eX α)) (DegPre.famε k) (f i (ν.eX α)) gm.b.left _
        (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
        (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [hb, Category.assoc]; exact hJb _))]
      congr 1
      rw [hb]
      exact norm_natCast_le_one_kummer_theta_logarithms _ _ _ _ hA
    have hφ : ∀ j, D.gtφT (TE R C) gm.b (ν.eX α) j = spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j :=
      fun j => gl_gtφT_pull D (epsR R) (TE R C) (spMap (dualMap (toF R C))) (gl_hom R C) gm₀.b gm.b hb (ν.eX α) j
    have hpj : ∀ j, ⊤ ≤ D.gtφT (TE R C) gm.b (ν.eX α) j ⁻¹ᵁ D.P.L.U (pickJ (D.gtφT (TE R C) gm.b (ν.eX α))
        (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j) := by
      intro j
      obtain ⟨i', he, hj⟩ := pickJ_spec (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j
      rw [hj, ← he, hφ i']
      exact hJb _
    unfold jc sE vE
    rw [hsec]
    simp only [gl_scal, gl_prB', hS]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε (gm.s (ν.eX α)) (gm.3 _) (𝟙 _) _
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))]
    rw [gl_corr D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε
      (fun j => spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j) DegPre.gtε _ _ (hpull.2 _)
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (fun k₁ k₂ e => pickJ_congr _ _ e)
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ, hφ]; exact e))
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ k₂]; exact e))
      (𝟙 _)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [gl_pullGen D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (spMap (dualMap (toF R C)))
      _ (𝟙 _) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [Category.id_comp]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (gm₀.3 _)
      (spMap (dualMap (toF R C))) _ (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j))
      (top_le_wchart _ _ _ _ (fun j => by rw [← hφ]; exact hpj j)) (top_le_wchart _ _ _ _ (fun j => hJb _))]
    have hn := norm_natCast_le_one_kummer_theta_logarithms (dualMap (toF R C)) (𝟙 _) (LB.wchart D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) (((gm₀.s (ν.eX α)).s fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)).val)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hJ _))
    rw [Category.comp_id] at hn
    rw [hn, IsUnit.unit_spec]
    unfold TanExp.termV
    simp only [map_mul]
    refine alg_lemma_5 _ _ _ _ _ _ _ ?_
    rw [← Finset.prod_mul_distrib]
    simp only [Category.id_comp, ← hφ]
    rw [Finset.prod_congr rfl (fun j _ => GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle D.P.L D.P.isLB _ _ _ _ _ (hν _) (hpj j) (by rw [hφ]; exact hJb _))]
    simp only [gl_gtφT_famφB]
    have tadd : ∀ (i : Fin 4) (a b : ℤ), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) a * trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i)
        (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i)) (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) b =
        trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) (a + b) :=
      fun i a b => trV_add _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _)) a b
    have tzero : ∀ (i : Fin 4), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) 0 = 1 :=
      fun i => trV_zero _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _))
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_prod_four_rearrange, tadd, tadd, tadd, tadd]
    have h0 : D.famφB (ν.eX α) 0 = 𝟙 _ := by
      unfold DegPre.famφB
      rfl
    simp only [sub_add_cancel, add_neg_cancel, neg_add_cancel, tzero, _root_.mul_one, h0, Category.comp_id]

end GlobalTheory.MBLow.TanGauge

end
