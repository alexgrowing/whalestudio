import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R}

section Rep

open FreeAbelianGroup

variable {T₀ : Over (Sp R)}

abbrev JVals (D₁ D₂ : DegPre R) (T₀ : Over (Sp R)) :=
  ∀ (T : Over (Sp R)) (_ : T ⟶ T₀) (z : T.left) (_ : (T.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → (JN D₁ D₂).ι),
    (T.left.presheaf.stalk z)ˣ

def fsEval {U : Type} [CommGroup U] (h : (T₀.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U)
    (s : FreeAbelianGroup (T₀ ⟶ D₁.P.A) × FreeAbelianGroup (T₀ ⟶ D₂.P.A)) : U :=
  (FreeAbelianGroup.lift (fun q : T₀ ⟶ D₁.P.A => Additive.ofMul (h (q.left ≫ coprod.inl))) s.1 +
    FreeAbelianGroup.lift (fun q : T₀ ⟶ D₂.P.A => Additive.ofMul (h (q.left ≫ coprod.inr))) s.2).toMul

theorem fsEval_add {U : Type} [CommGroup U] (h : (T₀.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U)
    (s s' : FreeAbelianGroup (T₀ ⟶ D₁.P.A) × FreeAbelianGroup (T₀ ⟶ D₂.P.A)) :
    fsEval h (s + s') = fsEval h s * fsEval h s' := by
  simp only [fsEval, Prod.fst_add, Prod.snd_add, map_add]
  rw [add_add_add_comm]
  rfl

def JRep (s : FreeAbelianGroup (T₀ ⟶ D₁.P.A) × FreeAbelianGroup (T₀ ⟶ D₂.P.A)) (v : JVals D₁ D₂ T₀) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T₀.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (JN D₁ D₂) φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (T₀.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U), ∏ k, h (φ k) ^ ε k = fsEval h s) ∧
    ∀ T (ρ : T ⟶ T₀) z J, Good (JN D₁ D₂) z J → val t ρ.left z J = v T ρ z J

theorem JRep.one : JRep (D₁ := D₁) (D₂ := D₂) (T₀ := T₀) 0 fun _ _ _ _ => 1 :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen (JN D₁ D₂),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => by simp [fsEval], fun _ _ _ _ _ => val_one _⟩

theorem JRep.mul {s s'} {v v' : JVals D₁ D₂ T₀} (h : JRep s v) (h' : JRep s' v') :
    JRep (s + s') fun T ρ z J => v T ρ z J * v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', e'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen (JN D₁ D₂) _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T ρ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (e T ρ z J hJ) (e' T ρ z J hJ))⟩
  rw [fsEval_add]
  exact prod_sum₂ (K := K) (K' := K') (U := U) _ (f U h) (f' U h)

theorem JRep.unique {s s'} {v v' : JVals D₁ D₂ T₀} (h : JRep s v) (h' : JRep s' v')
    (hs : Function.Surjective T₀.hom.appTop.hom) (e : 𝟙_ _ ⟶ T₀) (hF : s = s')
    (h₀ : ∀ y J, Good (JN D₁ D₂) y J → v _ e y J = v' _ e y J) {T} (ρ : T ⟶ T₀) {z J}
    (hJ : Good (JN D₁ D₂) z J) : v T ρ z J = v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', c'⟩ := h'
  subst hF
  exact (c T ρ z J hJ).symm.trans ((gen_unique' (jn_isLB D₁ D₂) (fun U _ h => (f' U h).trans (f U h).symm) T₀.hom e.left
    (Over.w e) hs ht ht' (fun y I hI => (c _ e y I hI).trans ((h₀ y I hI).trans (c' _ e y I hI).symm))
    _ ρ.left z J hJ).trans (c' T ρ z J hJ))

theorem JRep.cub₁ (x x' y : T₀ ⟶ D₁.P.A) :
    JRep (D₂ := D₂) (of (x * x' * y) - of (x * x') - of (x * y) - of (x' * y) + of x + of x' + of y - of 1, 0)
      fun _ ρ z J => th D₁ z (rl J) (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine ⟨thK, inferInstance, _, _, (isPart_inl D₁.P.L D₂.P.L).gen
    (LB.pullGen D₁.P.L (thφ D₁.P.A (x3 D₁.P.A)) thε D₁.cub.t (lift x (lift x' y)).left),
    (isPart_inl D₁.P.L D₂.P.L).gen_isGen (pullGen_isGen _ _ _ _ D₁.cub.isGen _), fun U _ h => ?_,
    fun T ρ z J hJ => ((isPart_inl D₁.P.L D₂.P.L).val_gen _ _ z hJ).trans
      (val_cub D₁.cub ρ ((isPart_inl D₁.P.L D₂.P.L).good hJ) _ _ _)⟩
  refine (prod_cub x x' y (fun q => h (q ≫ coprod.inl))).trans ?_
  simp only [fsEval, map_add, map_sub, map_zero, lift_apply_of, add_zero, toMul_add, toMul_sub, toMul_ofMul,
    div_eq_mul_inv]

theorem JRep.cub₂ (x x' y : T₀ ⟶ D₂.P.A) :
    JRep (D₁ := D₁) (0, of (x * x' * y) - of (x * x') - of (x * y) - of (x' * y) + of x + of x' + of y - of 1)
      fun _ ρ z J => th D₂ z (rr J) (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine ⟨thK, inferInstance, _, _, (isPart_inr D₁.P.L D₂.P.L).gen
    (LB.pullGen D₂.P.L (thφ D₂.P.A (x3 D₂.P.A)) thε D₂.cub.t (lift x (lift x' y)).left),
    (isPart_inr D₁.P.L D₂.P.L).gen_isGen (pullGen_isGen _ _ _ _ D₂.cub.isGen _), fun U _ h => ?_,
    fun T ρ z J hJ => ((isPart_inr D₁.P.L D₂.P.L).val_gen _ _ z hJ).trans
      (val_cub D₂.cub ρ ((isPart_inr D₁.P.L D₂.P.L).good hJ) _ _ _)⟩
  refine (prod_cub x x' y (fun q => h (q ≫ coprod.inr))).trans ?_
  simp only [fsEval, map_add, map_sub, map_zero, lift_apply_of, zero_add, toMul_add, toMul_sub, toMul_ofMul,
    div_eq_mul_inv]

theorem JRep.cmp {b : D₁.P.A ⟶ D₂.P.A} {p : D₁.X} {χ : D₂.X} {u : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : u.IsGen)
    (x : T₀ ⟶ D₁.P.A) :
    JRep (of (cP D₁ T₀ p * x) - of (cP D₁ T₀ p) - of x + of 1,
        - of (cP D₂ T₀ χ * (x ≫ b)) + of (cP D₂ T₀ χ) + of (x ≫ b) - of 1)
      fun _ ρ z J => val u (ρ ≫ x).left z J := by
  refine ⟨Fin 4 ⊕ Fin 4, inferInstance, _, _, LB.pullGen (JN D₁ D₂) _ _ u x.left, pullGen_isGen _ _ _ _ hu _,
    fun U _ h => ?_, fun T ρ z J hJ => val_pull hJ _ _ _⟩
  have a₁ : ∀ k, x.left ≫ D₁.Oφ (𝟙 _) p k ≫ (coprod.inl : D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) =
      D₁.Oφ x p k ≫ coprod.inl := fun k => by
    rw [← Category.assoc, WeightPf.Oφ_comp, Category.comp_id]
  have a₂ : ∀ k, x.left ≫ D₂.Oφ b χ k ≫ (coprod.inr : D₂.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) =
      D₂.Oφ (x ≫ b) χ k ≫ coprod.inr := fun k => by
    rw [← Category.assoc, WeightPf.Oφ_comp]
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k) (a₁ k)).trans
      (OLinEnd.prod_Oφ D₁ x p (fun q => h (q ≫ coprod.inl))))
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k) (a₂ k)).trans
      (OLinEnd.prod_Oφ_inv D₂ (x ≫ b) χ (fun q => h (q ≫ coprod.inr))))).trans ?_
  apply Additive.ofMul.injective
  simp only [fsEval, map_add, map_sub, map_neg, lift_apply_of, ofMul_mul, ofMul_inv, ofMul_toMul]
  abel

end Rep

end GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R}

section Cmp

open FreeAbelianGroup

variable {b : D₁.P.A ⟶ D₂.P.A} {p p' p'' : D₁.X} {χ χ' χ'' : D₂.X} {T : Over (Sp R)} {z : T.left}
  {J : (T.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → (JN D₁ D₂).ι}

theorem jcmp_one {u : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : Nrm u) (hJ : Good (JN D₁ D₂) z J) :
    val u (1 : T ⟶ D₁.P.A).left z J = 1 :=
  hu.2 T.left T.hom z J hJ

theorem jcmp_zero (hG : GlobalFnsSt) {u : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : Nrm u) (hp : p = 0) (hχ : χ = 0)
    (hJ : Good (JN D₁ D₂) z J) (x : T ⟶ D₁.P.A) : val u x.left z J = 1 := by
  have h := (JRep.cmp hu.1 (𝟙 _)).unique JRep.one (hG _ _ D₁.P.isAb).2 1 (by
    subst hp hχ
    rw [cPoint_zero, cPoint_zero, _root_.one_mul, _root_.one_mul, Category.id_comp]
    ext1 <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> abel)
    (fun y I hI => by rw [Category.comp_id, jcmp_one hu hI]) x hJ
  rwa [Category.comp_id] at h

theorem jcmp_congr (hG : GlobalFnsSt) {u u' : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : Nrm u) (hu' : Nrm u')
    (hJ : Good (JN D₁ D₂) z J) (x : T ⟶ D₁.P.A) : val u x.left z J = val u' x.left z J := by
  have h := (JRep.cmp hu.1 (𝟙 _)).unique (JRep.cmp hu'.1 (𝟙 _)) (hG _ _ D₁.P.isAb).2 1 rfl
    (fun y I hI => by rw [Category.comp_id, jcmp_one hu hI, jcmp_one hu' hI]) x hJ
  rwa [Category.comp_id] at h

theorem jcmp_add_char (hG : GlobalFnsSt) [IsMonHom b] {u : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : Nrm u)
    {u' : LB.Gen (CmpLB D₁ D₂ b p' χ')} (hu' : Nrm u') {u'' : LB.Gen (CmpLB D₁ D₂ b p'' (χ + χ'))} (hu'' : Nrm u'')
    (hp : p'' = p + p') (hJ : Good (JN D₁ D₂) z J) (x : T ⟶ D₁.P.A) :
    val u'' x.left z J * th D₂ z (rr J) (cP D₂ T χ) (cP D₂ T χ') (x ≫ b) =
      th D₁ z (rl J) (cP D₁ T p) (cP D₁ T p') x * (val u x.left z J * val u' x.left z J) := by
  have h := ((JRep.cmp hu''.1 (𝟙 _)).mul (JRep.cub₂ (cP D₂ _ χ) (cP D₂ _ χ') b)).unique
    ((JRep.cub₁ (cP D₁ _ p) (cP D₁ _ p') (𝟙 _)).mul ((JRep.cmp hu.1 (𝟙 _)).mul (JRep.cmp hu'.1 (𝟙 _))))
    (hG _ _ D₁.P.isAb).2 1 (by
      subst hp
      simp only [cPoint_add, Category.id_comp]
      ext1 <;> simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add] <;> abel)
    (fun y I hI => by
      have C₁ : IsCub (th D₁ (T := 𝟙_ _) y (rl I)) := isCub_cubV D₁.cub ((isPart_inl D₁.P.L D₂.P.L).good hI)
      have C₂ : IsCub (th D₂ (T := 𝟙_ _) y (rr I)) := isCub_cubV D₂.cub ((isPart_inr D₁.P.L D₂.P.L).good hI)
      rw [Category.comp_id, jcmp_one hu hI, jcmp_one hu' hI, jcmp_one hu'' hI, MonObj.one_comp b, C₁.face₃, C₂.face₃]
      simp) x hJ
  simpa only [Category.comp_id, comp_cP] using h

theorem jcmp_add_pt (hG : GlobalFnsSt) [IsMonHom b] {u : LB.Gen (CmpLB D₁ D₂ b p χ)} (hu : Nrm u)
    (hJ : Good (JN D₁ D₂) z J) (x y : T ⟶ D₁.P.A) :
    val u (x * y).left z J * th D₂ z (rr J) (cP D₂ T χ) (x ≫ b) (y ≫ b) =
      th D₁ z (rl J) (cP D₁ T p) x y * (val u x.left z J * val u y.left z J) := by
  have sj : Function.Surjective (D₁.P.A ⊗ D₁.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D₁.P.A D₁.P.A)]
    exact surj_comp (surj_snd hG D₁.P.isAb _) (hG _ _ D₁.P.isAb).2
  have h := ((JRep.cmp hu.1 (fst _ _ * snd _ _)).mul (JRep.cub₂ (cP D₂ _ χ) (fst _ _ ≫ b) (snd _ _ ≫ b))).unique
    ((JRep.cub₁ (cP D₁ _ p) (fst _ _) (snd _ _)).mul ((JRep.cmp hu.1 (fst _ _)).mul (JRep.cmp hu.1 (snd _ _))))
    sj (lift 1 1) (by
      rw [MonObj.mul_comp, _root_.mul_assoc (cP D₁ _ p), _root_.mul_assoc (cP D₂ _ χ)]
      ext1 <;> simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add] <;> abel)
    (fun w I hI => by
      have C₁ : IsCub (th D₁ (T := 𝟙_ _) w (rl I)) := isCub_cubV D₁.cub ((isPart_inl D₁.P.L D₂.P.L).good hI)
      have C₂ : IsCub (th D₂ (T := 𝟙_ _) w (rr I)) := isCub_cubV D₂.cub ((isPart_inr D₁.P.L D₂.P.L).good hI)
      rw [MonObj.comp_mul, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, _root_.mul_one, jcmp_one hu hI,
        MonObj.one_comp, C₁.face₂, C₂.face₂]
      simp) (lift x y) hJ
  simpa only [MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, comp_cP] using h

end Cmp

end GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R}

section Act

open GlobalTheory.TorusExt

variable {b : D₁.P.A ⟶ D₂.P.A} {hh : D₂.X →+ D₁.X} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_good_rr {Z : Scheme.{0}} {z : Z} {J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι} (hJ₂ : Good D₂.P.L z J₂) :
    ∃ J, Good (JN D₁ D₂) z J ∧ rr J = J₂ := by
  choose J₁ hJ₁ using fun ψ : Z ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  obtain ⟨J, hJ, -, e⟩ := exists_good_join D₁.P.isLB D₂.P.isLB (J₁ := J₁) hJ₁ hJ₂
  exact ⟨J, hJ, e⟩

theorem jact_val {u : ∀ χ, LB.Gen (CmpLB D₁ D₂ b (hh χ) χ)} (hu : ∀ χ, Nrm (u χ)) {g : GtPtF D₁ F}
    {g' : GtPtF D₂ F} (hA : Act D₁ D₂ b hh g g') (χ : D₂.X) {y J} (hJ : Good (JN D₁ D₂) y J) :
    charVal g' χ y (rr J) = charVal g (hh χ) y (rl J) * val (u χ) g.b.left y J :=
  hA.2 χ (u χ) (hu χ) y J hJ

theorem jexists_act (hG : GlobalFnsSt) [IsMonHom b] (u : ∀ χ, LB.Gen (CmpLB D₁ D₂ b (hh χ) χ))
    (hu : ∀ χ, Nrm (u χ)) (g : GtPtF D₁ F) : ∃ g' : GtPtF D₂ F, Act D₁ D₂ b hh g g' := by
  let w := fun χ => LB.mulGen (JN D₁ D₂) _ _ _ _ ((isPart_inl D₁.P.L D₂.P.L).gen (g.s (hh χ)))
    (LB.pullGen (JN D₁ D₂) _ _ (u χ) g.b.left)
  have hw : ∀ χ, (w χ).IsGen := fun χ => mulGen_isGen _ _ _ _ _ _ _
    ((isPart_inl D₁.P.L D₂.P.L).gen_isGen (g.isGen _)) (pullGen_isGen _ _ _ _ (hu χ).1 _)
  have vw : ∀ χ y J, Good (JN D₁ D₂) y J → val (w χ) (𝟙 (TF (R := R) F).left) y J =
      charVal g (hh χ) y (rl J) * val (u χ) g.b.left y J := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((isPart_inl D₁.P.L D₂.P.L).val_gen _ _ y hJ)
      ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])))
  have a₁ : ∀ χ k, g.b.left ≫ D₁.Oφ (𝟙 _) (hh χ) k ≫ (coprod.inl : D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) =
      D₁.Oφ g.b (hh χ) k ≫ coprod.inl := fun χ k => by
    rw [← Category.assoc, WeightPf.Oφ_comp, Category.comp_id]
  have a₂ : ∀ χ k, g.b.left ≫ D₂.Oφ b χ k ≫ (coprod.inr : D₂.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) =
      D₂.Oφ (g.b ≫ b) χ k ≫ coprod.inr := fun χ k => by
    rw [← Category.assoc, WeightPf.Oφ_comp]
  have fe : ∀ χ, FormEq (Sum.elim (fun k => D₁.gtφ F g.b (hh χ) k ≫
      (coprod.inl : D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left)) (fun k => g.b.left ≫
        Sum.elim (fun k => D₁.Oφ (𝟙 D₁.P.A) (hh χ) k ≫ (coprod.inl : D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left))
          (fun k => D₂.Oφ b χ k ≫ (coprod.inr : D₂.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left)) k))
      (Sum.elim DegPre.gtε (Sum.elim Oε Oinvε)) (fun k => DegPre.gtφ D₂ F (g.b ≫ b) χ k ≫
      (coprod.inr : D₂.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left)) DegPre.gtε := fun χ U _ h => by
    refine (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _ (prod_gt g.b (hh χ) (fun q => h (q ≫ coprod.inl)))
      (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
        ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k) (a₁ χ k)).trans
          (OLinEnd.prod_Oφ D₁ g.b (hh χ) (fun q => h (q ≫ coprod.inl))))
        ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k) (a₂ χ k)).trans
          (OLinEnd.prod_Oφ_inv D₂ (g.b ≫ b) χ (fun q => h (q ≫ coprod.inr)))))).trans ?_
    refine Eq.trans ?_ (prod_gt (g.b ≫ b) χ (fun q => h (q ≫ coprod.inr))).symm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  choose t ht vt using fun χ => exists_gen (jn_isLB D₁ D₂) (fe χ) (w χ) (hw χ)
  choose t' ht' vt' using fun χ => (isPart_inr D₁.P.L D₂.P.L).exists_gen D₂.P.isLB
    (snd_surjective D₁.P.isLB) (t χ) (ht χ)
  have VV : ∀ χ y J, Good (JN D₁ D₂) y J → val (t' χ) (𝟙 (TF (R := R) F).left) y (rr J) =
      charVal g (hh χ) y (rl J) * val (u χ) g.b.left y J := fun χ y J hJ =>
    (vt' χ _ _ y J hJ).trans ((vt χ _ _ y J hJ).trans (vw χ y J hJ))
  obtain ⟨g', hb, hv⟩ := exists_gt (D := D₂) (g.b ≫ b) t' ht' (fun _ _ _ _ => rfl) (fun y J₂ hJ₂ => by
      obtain ⟨J, hJ, rfl⟩ := exists_good_rr (D₁ := D₁) hJ₂
      refine (VV 0 y J hJ).trans ?_
      rw [jcmp_zero hG (hu 0) (map_zero hh) rfl hJ g.b, _root_.mul_one]
      exact (congrArg (fun c => charVal g c y (rl J)) (map_zero hh)).trans
        (charVal_zero g ((isPart_inl D₁.P.L D₂.P.L).good hJ)))
    (fun χ χ' y J₂ hJ₂ => by
      obtain ⟨J, hJ, rfl⟩ := exists_good_rr (D₁ := D₁) hJ₂
      have e₁ := congrArg Additive.ofMul
        (jcmp_add_char hG (hu χ) (hu χ') (hu (χ + χ')) (map_add _ _ _) hJ g.b)
      have e₂ := charVal_add g ((isPart_inl D₁.P.L D₂.P.L).good hJ) (hh χ) (hh χ')
      rw [← map_add] at e₂
      have e₃ := congrArg Additive.ofMul e₂
      rw [VV _ y J hJ, VV _ y J hJ, VV _ y J hJ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₃)
  exact ⟨g', hb, fun χ u₁ hu₁ z J hJ => (hv χ z (rr J) ((isPart_inr D₁.P.L D₂.P.L).good hJ)).trans
    ((VV χ z J hJ).trans (congrArg (charVal g (hh χ) z (rl J) * ·) (jcmp_congr hG (hu χ) hu₁ hJ g.b)))⟩

theorem jact_unique {u : ∀ χ, LB.Gen (CmpLB D₁ D₂ b (hh χ) χ)} (hu : ∀ χ, Nrm (u χ)) {g : GtPtF D₁ F}
    {g' g'' : GtPtF D₂ F} (h₁ : Act D₁ D₂ b hh g g') (h₂ : Act D₁ D₂ b hh g g'') : g' = g'' :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ y J₂ hJ₂ => by
    obtain ⟨J, hJ, rfl⟩ := exists_good_rr (D₁ := D₁) hJ₂
    exact (jact_val hu h₁ χ hJ).trans (jact_val hu h₂ χ hJ).symm

theorem jact_isAdd (hG : GlobalFnsSt) [IsMonHom b] {u : ∀ χ, LB.Gen (CmpLB D₁ D₂ b (hh χ) χ)}
    (hu : ∀ χ, Nrm (u χ)) {g₁ g₂ g₃ : GtPtF D₁ F} {g₁' g₂' g₃' : GtPtF D₂ F} (hA : g₁.IsAdd g₂ g₃)
    (h₁ : Act D₁ D₂ b hh g₁ g₁') (h₂ : Act D₁ D₂ b hh g₂ g₂') (h₃ : Act D₁ D₂ b hh g₃ g₃') : g₁'.IsAdd g₂' g₃' := by
  obtain ⟨bb, v⟩ := (isAdd_iff_val _ _ _).1 hA
  refine (isAdd_iff_val _ _ _).2 ⟨by rw [h₁.1, h₂.1, h₃.1, bb, MonObj.mul_comp], fun χ y J₂ hJ₂ => ?_⟩
  obtain ⟨J, hJ, rfl⟩ := exists_good_rr (D₁ := D₁) hJ₂
  have e₁ := jcmp_add_pt hG (hu χ) hJ g₁.b g₂.b
  rw [← bb, ← h₁.1, ← h₂.1] at e₁
  have e₂ := congrArg Additive.ofMul e₁
  have e₃ := congrArg Additive.ofMul (v (hh χ) y (rl J) ((isPart_inl D₁.P.L D₂.P.L).good hJ))
  rw [jact_val hu h₁ χ hJ, jact_val hu h₂ χ hJ, jact_val hu h₃ χ hJ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e₂ e₃ ⊢
  linear_combination (norm := abel) e₂ + e₃

theorem jact_isTor [IsMonHom b] {u : ∀ χ, LB.Gen (CmpLB D₁ D₂ b (hh χ) χ)} (hu : ∀ χ, Nrm (u χ))
    {t : Multiplicative D₁.X →* Fˣ} {g : GtPtF D₁ F} {g' : GtPtF D₂ F} (ht : IsTor t g) (hA : Act D₁ D₂ b hh g g') :
    IsTor (t.comp (AddMonoidHom.toMultiplicative hh)) g' := by
  refine ⟨by rw [hA.1, ht.1, MonObj.one_comp], fun χ y J₂ hJ₂ => ?_⟩
  obtain ⟨J, hJ, rfl⟩ := exists_good_rr (D₁ := D₁) hJ₂
  have e : val (u χ) g.b.left y J = 1 :=
    (congrArg (fun c : TF (R := R) F ⟶ D₁.P.A => val (u χ) c.left y J) ht.1).trans (jcmp_one (hu χ) hJ)
  have e' := jact_val hu hA χ hJ
  rw [e, _root_.mul_one] at e'
  exact (congrArg Units.val e').trans (ht.2 (hh χ) y (rl J) ((isPart_inl D₁.P.L D₂.P.L).good hJ))

end Act

end GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem act_two_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X), IsMonHom b → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ g : GtPtF D₁ F, ∃! g' : GtPtF D₂ F, Act D₁ D₂ b h g g') ∧ (∀ (g₁ g₂ g₃ : GtPtF D₁ F) (g₁' g₂' g₃' : GtPtF D₂ F), g₁.IsAdd g₂ g₃ → Act D₁ D₂ b h g₁ g₁' → Act D₁ D₂ b h g₂ g₂' → Act D₁ D₂ b h g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ ∀ (t : Multiplicative D₁.X →* Fˣ) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), IsTor t g → Act D₁ D₂ b h g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative h)) g' := by
  intro R _ _ D₁ D₂ b h hb hu F _ _
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  choose u hu using hu
  refine ⟨fun g => ?_, fun _ _ _ _ _ _ => jact_isAdd hG hu, fun _ _ _ => jact_isTor hu⟩
  obtain ⟨g', hg⟩ := jexists_act hG u hu g
  exact ⟨g', hg, fun _ h' => jact_unique hu h' hg⟩

end GlobalTheory.Mum.Two
