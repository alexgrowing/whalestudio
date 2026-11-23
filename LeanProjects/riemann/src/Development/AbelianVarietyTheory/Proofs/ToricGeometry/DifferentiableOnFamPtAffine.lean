import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearOfMulPeriod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.ArtinKernel

open GlobalTheory.TangentOrigin

section Points

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem evalPt_congr {x y : Sp R ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalPt x U h f = evalPt y U h' f := by
  subst e
  rfl

theorem evalPt_appLE (x : Sp R ⟶ X) (φ : X ⟶ Y) (y : Sp R ⟶ Y) (hy : x ≫ φ = y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt x V hV ((φ.appLE U V e).hom f) = evalPt y U hU f := by
  subst hy
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

open Classical in

def evalPt' (x : Sp R ⟶ X) (U : X.Opens) (f : Γ(X, U)) : R :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then evalPt x U h f else 0

theorem evalPt'_eq (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    evalPt' x U f = evalPt x U h f := by
  unfold evalPt'
  rw [dif_pos h]

private theorem preimage_whole_comp_of_preimage_whole {Z W V : Scheme.{0}} (f : Z ⟶ W) (x : W ⟶ V) {U : V.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (f ≫ x) ⁻¹ᵁ U := by
  intro p _
  exact h (show f.base p ∈ (⊤ : W.Opens) from trivial)

theorem top_le_iff_residue [Subsingleton (PrimeSpectrum R)] (ρ : R →+* ℂ) (x : Sp R ⟶ X) (y : Sp ℂ ⟶ X)
    (hy : spMap ρ ≫ x = y) (W : X.Opens) : ⊤ ≤ x ⁻¹ᵁ W ↔ ⊤ ≤ y ⁻¹ᵁ W := by
  subst hy
  refine ⟨preimage_whole_comp_of_preimage_whole _ _, fun h p _ => ?_⟩
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hq : (spMap ρ).base q ∈ x ⁻¹ᵁ W := h (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have e : (spMap ρ).base q = p := Subsingleton.elim (α := PrimeSpectrum R) _ _
  rw [e] at hq
  exact hq

theorem residue_evalPt (ρ : R →+* ℂ) (x : Sp R ⟶ X) (y : Sp ℂ ⟶ X)
    (hy : spMap ρ ≫ x = y) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(X, W)) :
    ρ (evalPt x W h f) = valAt' y W f := by
  subst hy
  have h' : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ W := preimage_whole_comp_of_preimage_whole _ _ h
  rw [valAt'_eq_evalPt _ _ h', evalPt_spMap_comp ρ x W h h']

private theorem evalPt_res_eq_evalPt (x : Sp R ⟶ Y) {U V : Y.Opens} (e : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(Y, U)ˣ) : evalPt x V hV (res e s).val = evalPt x U hU s.val :=
  evalPt_res x e hU hV s.val

private theorem units_map_evalPt_res_pullU_eq_comp (x : Sp R ⟶ Y) (ψ : Y ⟶ X) {U₀ U₁ : X.Opens} {V : Y.Opens}
    (e : V ≤ ψ ⁻¹ᵁ U₀ ⊓ ψ ⁻¹ᵁ U₁) (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U₀ ⊓ U₁)ˣ) :
    Units.map (evalPt x V hV).toMonoidHom (res e (pullU ψ (U₀ ⊓ U₁) s)) =
      Units.map (evalPt (x ≫ ψ) (U₀ ⊓ U₁) (hV.trans (x.preimage_mono e))).toMonoidHom s := by
  ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact evalPt_appLE x ψ _ rfl (U₀ ⊓ U₁) V e hV _ s.val

private theorem mul_eq_mul_of_eq_mul_zpow_neg_one {M : Type} [CommGroup M] {c c' t₀ t₁ : M}
    (h : c = t₀ * t₁ ^ (-1 : ℤ) * c') : c * t₁ = t₀ * c' := by
  rw [h, _root_.zpow_neg_one, mul_right_comm, inv_mul_cancel_right]

theorem evalPt_gen_two (L : LB X) (φ₀ φ₁ : Y ⟶ X)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![1, -1])) (hc : c.IsGen)
    (x : Sp R ⟶ Y) (y₀ y₁ : Sp R ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j) (b : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j')
    (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0))) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1))) :
    evalPt x _ a (c.s j).val * evalPt y₁ _ a₁ (L.g (j 1) (j' 1)).val =
      evalPt y₀ _ a₀ (L.g (j 0) (j' 0)).val * evalPt x _ b (c.s j').val := by
  have hab : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L ![φ₀, φ₁] j ⊓ LB.wchart L ![φ₀, φ₁] j') :=
    GlobalTheory.ThetaGroupFrame.top_le_inf x a b
  have hh := congrArg
    (Units.map (evalPt x (LB.wchart L ![φ₀, φ₁] j ⊓ LB.wchart L ![φ₀, φ₁] j') hab).toMonoidHom) (hc j j')
  unfold LB.LinComb at hh
  simp only [map_mul, map_prod, map_zpow, units_map_evalPt_res_pullU_eq_comp] at hh
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zpow_one] at hh
  have hv := congrArg Units.val (mul_eq_mul_of_eq_mul_zpow_neg_one hh)
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hv
  rw [evalPt_res_eq_evalPt x _ a hab, evalPt_res_eq_evalPt x _ b hab, evalPt_congr h₀ _ _ a₀,
    evalPt_congr h₁ _ _ a₁] at hv
  exact hv

end Points

section Family

variable {R : Type} [CommRing R] [Algebra ℂ R]

variable (R) in

abbrev spO : Over (Sp ℂ) := Over.mk (spMap (algebraMap ℂ R))

def resPt (ρ : R →ₐ[ℂ] ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ spO R :=
  Over.homMk (spMap ρ.toRingHom) (by
    change spMap ρ.toRingHom ≫ spMap (algebraMap ℂ R) = 𝟙 (Sp ℂ)
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact ρ.commutes a)

theorem resPt_left (ρ : R →ₐ[ℂ] ℂ) : (resPt ρ).left = spMap ρ.toRingHom := rfl

variable {A : Over (Sp ℂ)}

theorem evalPt_const (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A.left.Opens)
    (h : ⊤ ≤ (toUnit (spO R) ≫ y).left ⁻¹ᵁ U) (h' : ⊤ ≤ y.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    evalPt (R := R) (toUnit (spO R) ≫ y).left U h f = algebraMap ℂ R (valAt' y.left U f) := by
  have e : (toUnit (spO R) ≫ y).left = spMap (algebraMap ℂ R) ≫ y.left := by
    rw [Over.comp_left]
    rfl
  have h'' : ⊤ ≤ (spMap (algebraMap ℂ R) ≫ y.left) ⁻¹ᵁ U := preimage_whole_comp_of_preimage_whole _ _ h'
  rw [evalPt_congr e U h h'', evalPt_spMap_comp _ _ U h' h'', valAt'_eq_evalPt _ _ h']

theorem top_le_const (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A.left.Opens) (h' : ⊤ ≤ y.left ⁻¹ᵁ U) :
    ⊤ ≤ (toUnit (spO R) ≫ y).left ⁻¹ᵁ U := by
  rw [Over.comp_left]
  exact preimage_whole_comp_of_preimage_whole _ _ h'

theorem surjective_residue_slice [Subsingleton (PrimeSpectrum R)] (ρ : R →ₐ[ℂ] ℂ) :
    Function.Surjective (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left := by
  have hc : spMap ρ.toRingHom ≫ spMap (algebraMap ℂ R) = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact ρ.commutes a
  have wP : (fst (spO R) A).left ≫ (spO R).hom = (snd (spO R) A).left ≫ A.hom :=
    (Over.w (fst (spO R) A)).trans (Over.w (snd (spO R) A)).symm
  have hL1 : (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left ≫ (fst (spO R) A).left = A.hom ≫ spMap ρ.toRingHom := by
    rw [← Over.comp_left, lift_fst, Over.comp_left, resPt_left]
    rfl
  have hL2 : (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left ≫ (snd (spO R) A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  intro p
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ.toRingHom)
    (g := (fst (spO R) A).left) q p (Subsingleton.elim (α := PrimeSpectrum R) _ _)
  have cond : pullback.fst (spMap ρ.toRingHom) (fst (spO R) A).left ≫ spMap ρ.toRingHom =
      pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (fst (spO R) A).left := pullback.condition
  have hq1 : pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left ≫ A.hom =
      pullback.fst (spMap ρ.toRingHom) (fst (spO R) A).left := by
    rw [← wP, ← Category.assoc, ← cond, Category.assoc, show (spO R).hom = spMap (algebraMap ℂ R) from rfl, hc,
      Category.comp_id]
  have key : (pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
      (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left = pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left := by
    apply Over.tensorObj_ext
    · show ((pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
          (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left) ≫ (fst (spO R) A).left =
          pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (fst (spO R) A).left
      rw [Category.assoc, hL1, ← cond, ← hq1]
      simp only [Category.assoc]
    · show ((pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) ≫
          (lift (toUnit A ≫ resPt ρ) (𝟙 A)).left) ≫ (snd (spO R) A).left =
          pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left
      rw [Category.assoc, hL2, Category.comp_id]
  refine ⟨(pullback.snd (spMap ρ.toRingHom) (fst (spO R) A).left ≫ (snd (spO R) A).left) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, hw2]

variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def famPt (R : Type) [CommRing R] [Algebra ℂ R] (z : Fin g → ℂ) : spO R ⟶ spO R ⊗ A :=
  lift (𝟙 _) (toUnit _ ≫ u.ex z)

theorem famPt_fst (z : Fin g → ℂ) : (famPt u R z).left ≫ (fst _ A).left = 𝟙 (Sp R) := by
  rw [← Over.comp_left]
  simp only [famPt, lift_fst, Over.id_left]
  rfl

theorem famPt_snd (z : Fin g → ℂ) : (famPt u R z).left ≫ (snd _ A).left = (toUnit (spO R) ≫ u.ex z).left := by
  rw [← Over.comp_left]
  simp only [famPt, lift_snd]

theorem famPt_mem (z : Fin g → ℂ) {U : A.left.Opens} (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) :
    ⊤ ≤ (famPt u R z).left ⁻¹ᵁ ((snd (spO R) A).left ⁻¹ᵁ U) := by
  intro p _
  have hp := top_le_const (R := R) (u.ex z) U h (show p ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [← famPt_snd u z] at hp
  exact hp

private lemma appLE_comp_presheaf_map {X Y : Scheme.{0}} (f : X ⟶ Y) (W : Y.Opens) (V V' : X.Opens)
    (e : V ≤ f ⁻¹ᵁ W) (i : Opposite.op V ⟶ Opposite.op V') (e' : V' ≤ f ⁻¹ᵁ W) :
    f.appLE W V e ≫ X.presheaf.map i = f.appLE W V' e' := by
  rw [Scheme.Hom.appLE_map]

private lemma app_comp_map_comp_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (W : Y.Opens) (V V' : X.Opens)
    (i : Opposite.op (f ⁻¹ᵁ W) ⟶ Opposite.op V) (i' : Opposite.op V ⟶ Opposite.op V') (e' : V' ≤ f ⁻¹ᵁ W) :
    (f.app W ≫ X.presheaf.map i) ≫ X.presheaf.map i' = f.appLE W V' e' := by
  rw [Category.assoc, ← Functor.map_comp]
  rfl

variable [Module.Finite ℂ R]

theorem differentiableOn_famPt_affine {U : A.left.Opens} (hU : IsAffineOpen U)
    (f : Γ((spO R ⊗ A).left, (snd (spO R) A).left ⁻¹ᵁ U)) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (evalPt' (R := R) (famPt u R z).left _ f))
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
  have hE : ∀ z ∈ {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U},
      ⊤ ≤ (famPt u R z).left ⁻¹ᵁ ((snd (spO R) A).left ⁻¹ᵁ U) := fun z hz => famPt_mem u z hz
  let T : Subring Γ((spO R ⊗ A).left, (snd (spO R) A).left ⁻¹ᵁ U) :=
    { carrier := {f | ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ
          (fun z => lam (evalPt' (R := R) (famPt u R z).left _ f)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}}
      mul_mem' := fun {a b} ha hb lam => by
        refine (GlobalTheory.ArtinKernel.differentiableOn_mul ha hb lam).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_mul]
      one_mem' := fun lam => by
        refine (differentiableOn_const (lam 1)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_one]
      add_mem' := fun {a b} ha hb lam => by
        refine ((ha lam).add (hb lam)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_add, Pi.add_apply]
      zero_mem' := fun lam => by
        refine (differentiableOn_const (0 : ℂ)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_zero]
      neg_mem' := fun {a} ha lam => by
        refine (ha lam).neg.congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_neg, Pi.neg_apply] }
  have gen1 : ∀ (W : A.left.Opens) (hUW : U ≤ W)
      (e : (snd (spO R) A).left ⁻¹ᵁ U ≤ (snd (spO R) A).left ⁻¹ᵁ W) (s : Γ(A.left, W)),
      ((snd (spO R) A).left.appLE W _ e).hom s ∈ T := by
    intro W hUW e s lam
    have hW : ∀ z ∈ {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ W :=
      fun z hz => hz.trans ((u.ex z).left.preimage_mono hUW)
    refine (((u.hol W s).2.mono hW).mul_const (lam 1)).congr fun z hz => ?_
    have h1 : ⊤ ≤ (toUnit (spO R) ≫ u.ex z).left ⁻¹ᵁ W := top_le_const (u.ex z) W (hW z hz)
    have h2 : ⊤ ≤ ((famPt u R z).left ≫ (snd (spO R) A).left) ⁻¹ᵁ W := by
      rw [famPt_snd]
      exact h1
    simp only [evalPt'_eq _ (hE z hz), evalPt_appLE _ _ _ rfl W _ e (hE z hz) h2,
      evalPt_congr (famPt_snd u z) W h2 h1, evalPt_const (u.ex z) W h1 (hW z hz),
      Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have gen2 : ∀ (e : (snd (spO R) A).left ⁻¹ᵁ U ≤ (fst (spO R) A).left ⁻¹ᵁ ⊤) (t : Γ(Sp R, ⊤)),
      ((fst (spO R) A).left.appLE ⊤ _ e).hom t ∈ T := by
    intro e t lam
    have h0 : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ⊤ := le_rfl
    refine (differentiableOn_const (lam (evalPt (𝟙 (Sp R)) ⊤ h0 t))).congr fun z hz => ?_
    have h2 : ⊤ ≤ ((famPt u R z).left ≫ (fst (spO R) A).left) ⁻¹ᵁ ⊤ := le_rfl
    simp only [evalPt'_eq _ (hE z hz), evalPt_appLE _ _ _ rfl ⊤ _ e (hE z hz) h2,
      evalPt_congr (famPt_fst u z) ⊤ h2 h0]
  have : IsAffine U := hU
  have : IsAffine (spO R).left := inferInstanceAs (IsAffine (Sp R))
  have hpb : IsPullback ((snd (spO R) A).left ∣_ U) (((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left)
      (U.ι ≫ A.hom) (spO R).hom :=
    (isPullback_morphismRestrict (snd (spO R) A).left U).paste_vert (IsPullback.of_hasPullback (spO R).hom A.hom).flip
  have hpo := isPushout_appTop_of_isPullback hpb
  have e1 : (snd (spO R) A).left ⁻¹ᵁ U ≤ (snd (spO R) A).left ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
  have k1 : ((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom =
      (snd (spO R) A).left.appLE (U.ι ''ᵁ ⊤) _ e1 := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE, Scheme.Opens.topIso_hom]
    exact appLE_comp_presheaf_map _ _ _ _ _ _ _
  have k2 : (((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left).appTop ≫
      ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom = (fst (spO R) A).left.appLE ⊤ _ le_top := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact app_comp_map_comp_map_eq_appLE _ _ _ _ _ _ _
  have m1 : ∀ s, (((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom s ∈ T := by
    intro s
    rw [k1]
    exact gen1 _ (Scheme.Opens.ι_image_top U).ge e1 s
  have m2 : ∀ t, ((((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left).appTop ≫
      ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom t ∈ T := by
    intro t
    rw [k2]
    exact gen2 le_top t
  let c1 := CommRingCat.ofHom (RingHom.codRestrict
    (((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom T m1)
  let c2 := CommRingCat.ofHom (RingHom.codRestrict ((((snd (spO R) A).left ⁻¹ᵁ U).ι ≫
    (fst (spO R) A).left).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom T m2)
  have hw : (U.ι ≫ A.hom).appTop ≫ c1 = (spO R).hom.appTop ≫ c2 := by
    ext s
    have := congrArg (fun m => (m ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom s) hpo.w
    simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  have hd : hpo.desc c1 c2 hw ≫ CommRingCat.ofHom T.subtype = ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom := by
    apply hpo.hom_ext
    · rw [← Category.assoc, hpo.inl_desc]
      rfl
    · rw [← Category.assoc, hpo.inr_desc]
      rfl
  have hf : f ∈ T := by
    have : ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom.hom (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv.hom f) = f := by
      show (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom f = f
      rw [Iso.inv_hom_id]
      rfl
    rw [← this, ← hd]
    exact ((hpo.desc c1 c2 hw).hom (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv.hom f)).2
  exact hf lam

theorem differentiableOn_famPt {U : A.left.Opens} {V : (spO R ⊗ A).left.Opens}
    (hV : (snd (spO R) A).left ⁻¹ᵁ U ≤ V) (f : Γ((spO R ⊗ A).left, V)) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (evalPt' (R := R) (famPt u R z).left V f))
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
  apply differentiableOn_of_locally_differentiableOn
  intro z hz
  obtain ⟨q0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hp : (u.ex z).left.base q0 ∈ U := hz (show q0 ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨U', hU'aff, hpU', hU'U⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hp
  refine ⟨{w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ U'}, (u.hol U' 1).1, ?_, ?_⟩
  · intro q _
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q q0]
    exact hpU'
  · have hle : (snd (spO R) A).left ⁻¹ᵁ U' ≤ V := ((snd (spO R) A).left.preimage_mono hU'U).trans hV
    refine ((differentiableOn_famPt_affine u hU'aff (resG _ hle f) lam).mono Set.inter_subset_right).congr ?_
    intro w hw
    have h1 : ⊤ ≤ (famPt u R w).left ⁻¹ᵁ ((snd (spO R) A).left ⁻¹ᵁ U') := famPt_mem u w hw.2
    have h2 : ⊤ ≤ (famPt u R w).left ⁻¹ᵁ V :=
      (famPt_mem u w hw.1).trans ((famPt u R w).left.preimage_mono hV)
    simp only [evalPt'_eq _ h1, evalPt'_eq _ h2, evalPt_res _ hle h2 h1]

end Family

end GlobalTheory.ArtinKernel
