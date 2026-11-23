import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PhiPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} {θ' : A → A → A → U}
  (β : A →* B) (Ω : A → U)
  (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c)
include h

theorem cubN_rel (k : ℕ) (a m x : A) : cubN θ k (β a) (β m) (β x) =
    Ω (a * m ^ k * x) * (Ω (a * x))⁻¹ * (Ω (a * m ^ k))⁻¹ * Ω a * ((Ω (m * x))⁻¹ * Ω m * Ω x * (Ω 1)⁻¹) ^ k *
      cubN θ' k a m x := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have c := h (a * m ^ k) m x
    rw [map_mul, map_pow] at c
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    rw [ih, c, pow_succ m, ← _root_.mul_assoc a, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem units_rel (k : ℕ) (a m x : A) (g n : U) :
    Ω (x * m) ^ ((k : ℤ) - 1) * Ω (a * (x * m)) * (Ω a)⁻¹ * Ω 1 *
      (cubN θ k (β a) (β m) (β x) * (θ (β a) (β x) (β m))⁻¹ *
        ((Ω (a * m))⁻¹ * Ω a * Ω m * (Ω 1)⁻¹ * g * (Ω 1 ^ (k : ℤ) * Ω m ^ (-(k : ℤ)) * n))) =
    Ω x ^ ((k : ℤ) - 1) * Ω (a * m ^ k * x) * (Ω (a * m ^ k))⁻¹ * Ω 1 *
      (cubN θ' k a m x * (θ' a x m)⁻¹ * (g * n)) := by
  rw [cubN_rel β Ω h, h, ← _root_.mul_assoc a x m, mul_comm m x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

end Alg

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem push_cP (hD : IsPullDeg φ D D') (T' : Over (Spec (CommRingCat.of R'))) (χ : D'.X) :
    pushHom (pull_grp hD) T' (cP D' T' χ) = cP D _ (hD.xe χ) := Over.OverMorphism.ext (by
  show (T'.hom ≫ (D'.c χ).left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
    (T'.hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
  rw [Category.assoc, hD.c_pr, Category.assoc])

theorem cub_rel (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {T' : Over (Spec (CommRingCat.of R'))} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' x.left))
    (a b c : T' ⟶ D'.P.A) :
    @Eq (T'.left.presheaf.stalk z)ˣ (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' a)
      (pushHom (pull_grp hD) T' b) (pushHom (pull_grp hD) T' c))
      (Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' z J' a b c) := by
  subst hΩ
  have e := cub_pull hG hD (T' := T') hJ hJ' a b c
  have q : (lift a (lift b c)).left ≫ (cubeMapOf (pull_grp hD)).F3 = (lift (pushHom (pull_grp hD) T' a)
      (lift (pushHom (pull_grp hD) T' b) (pushHom (pull_grp hD) T' c))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q z
    (J (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' q))) rfl)

variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]

theorem base_eq (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
    algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom :=
  (Category.assoc _ _ _).trans
    (((congrArg (jFK (R := R') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _)))

variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}

def liftB (ρ : T' ⟶ DegPre.BF D' F) : Over.mk (T'.hom ≫ spMap φ) ⟶ DegPre.BF D F :=
  Over.homMk (ρ.left ≫ Θ) (by
    show (ρ.left ≫ Θ) ≫ (DegPre.BF D F).hom = T'.hom ≫ spMap φ
    rw [← Over.w (fst (TF (R := R) F) D.P.A), Category.assoc, ← Category.assoc Θ, hΘ₁, ← hT, ← Over.w ρ,
      ← Over.w (fst (TF (R := R') F) D'.P.A)]
    simp only [Category.assoc])

theorem liftB_fst (ρ : T' ⟶ DegPre.BF D' F) :
    (liftB hT hΘ₁ ρ ≫ fst (TF (R := R) F) D.P.A).left = (ρ ≫ fst (TF (R := R') F) D'.P.A).left :=
  (Category.assoc _ _ _).trans (congrArg (ρ.left ≫ ·) hΘ₁)

include hΘ₂ in
theorem liftB_pr (ρ : T' ⟶ DegPre.BF D' F) :
    liftB hT hΘ₁ ρ ≫ DegPre.prB D F = pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F) :=
  Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (ρ.left ≫ ·) hΘ₂).trans (Category.assoc _ _ _).symm))

theorem liftB_pt (ρ : T' ⟶ DegPre.BF D' F) {b : TF (R := R) F ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = b.left) :
    liftB hT hΘ₁ ρ ≫ fst (TF (R := R) F) D.P.A ≫ b =
      pushHom (pull_grp hD) T' (ρ ≫ fst (TF (R := R') F) D'.P.A ≫ b') := by
  refine Over.OverMorphism.ext ?_
  show (liftB hT hΘ₁ ρ).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ b.left =
    (ρ.left ≫ (fst (TF (R := R') F) D'.P.A).left ≫ b'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
  rw [← Category.assoc, ← Over.comp_left, liftB_fst, ← hb]
  simp only [Over.comp_left, Category.assoc]

include hΘ₂ in
theorem liftB_tr (ρ : T' ⟶ DegPre.BF D' F) {b : TF (R := R) F ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = b.left) :
    liftB hT hΘ₁ ρ ≫ DegPre.trPt D F b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by
  apply CartesianMonoidalCategory.hom_ext
  · refine Over.OverMorphism.ext ?_
    rw [Category.assoc, tr_fst, liftB_fst, liftB_fst, Category.assoc, tr_fst]
  · refine Eq.trans ?_ (liftB_pr hD hT hΘ₁ hΘ₂ _).symm
    rw [Category.assoc, Category.assoc, tr_pr, tr_pr, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      liftB_pr hD hT hΘ₁ hΘ₂, liftB_pt hD hT hΘ₁ ρ hb]

include hΘ₂ in
theorem liftB_fam (ρ : T' ⟶ DegPre.BF D' F) (x : D'.X) (κ : Fin 4) :
    (liftB hT hΘ₁ ρ).left ≫ DegPre.famφ D F (hD.xe x) κ = (ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  fin_cases κ
  · exact congrArg (fun q => q.left) (liftB_pr hD hT hΘ₁ hΘ₂ ρ)
  · have e : liftB hT hΘ₁ ρ ≫ (DegPre.prB D F * cP D _ (hD.xe x)) =
        pushHom (pull_grp hD) T' (ρ ≫ (DegPre.prB D' F * cP D' _ x)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, comp_cP, comp_cP, push_cP, liftB_pr hD hT hΘ₁ hΘ₂]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ cP D _ (hD.xe x) = pushHom (pull_grp hD) T' (ρ ≫ cP D' _ x) := by
      rw [comp_cP, comp_cP, push_cP]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ (1 : DegPre.BF D F ⟶ D.P.A) =
        pushHom (pull_grp hD) T' (ρ ≫ (1 : DegPre.BF D' F ⟶ D'.P.A)) := by
      rw [MonObj.comp_one, MonObj.comp_one, map_one]
    exact congrArg (fun q => q.left) e

include hΘ₂ in

theorem sval_rel {k : ℕ} (x : D'.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (hD.xe x)) (DegPre.famε k)))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
      (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) (s.f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) (s'.f q))
    (ρ : T' ⟶ DegPre.BF D' F) {z : T'.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) :
    @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J') := by
  subst hΩ
  have e := H _ ρ.left z (fun κ => J ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => J' (ρ.left ≫ DegPre.famφ D' F x κ)) (fun κ => hJ ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => hJ' (ρ.left ≫ DegPre.famφ D' F x κ))
  have p := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _ (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).trans
    (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val p) rfl

set_option maxHeartbeats 1000000 in
include hT hΘ₁ hΘ₂ in
theorem phiVal_pull (hG : GlobalFnsSt) {k : ℕ} (p₀ : QkPt D F k) (p₀' : QkPt D' F k) (hy : p₀'.y = hD.xe.symm p₀.y)
    (hg : IsPullGtF φ hD F p₀.g p₀'.g)
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineε k)))
    (hl : ∀ i, DegPre.lineφ D' F p₀'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = 𝟙 _ ≫ DegPre.lineφ D F p₀.g.b i)
    (hν : PMaps hD.w (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k) ν' ν (𝟙 _))
    (s s₂ : Fam D F k) (s' s₂' : Fam D' F k)
    (H₁ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q)))
    (H₂ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s₂.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s₂'.s x).f q)))
    (H : PhiVal p₀ ν s.s s₂.s) : PhiVal p₀' ν' s'.s s₂'.s := by
  rintro α _ rfl T' ρ z J' hJ'
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ,
      Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left) := ⟨_, rfl⟩
  have hb := hg.1
  have e := H (hD.xe α) (hD.xe (α + p₀'.y)) (by rw [map_add, hy, AddEquiv.apply_symm_apply]) _ (liftB hT hΘ₁ ρ) z J hJ
  have v₂ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₂ (α + p₀'.y)) ρ hJ hJ' Ω hΩ
  have v₁ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₁ α) (ρ ≫ DegPre.trPt D' F p₀'.g.b) hJ hJ' Ω hΩ
  let σ : T' ⟶ TF (R := R') F := ρ ≫ fst _ _
  have m₁ : ρ ≫ fst (TF (R := R') F) D'.P.A ≫ p₀'.g.b = σ ≫ p₀'.g.b := (Category.assoc _ _ _).symm
  have cy : cP D' T' (α + p₀'.y) = cP D' T' α * (σ ≫ p₀'.g.b) ^ k := by
    rw [cPoint_add, ← comp_cP D' σ p₀'.y, cPoint_y]
    exact congrArg _ (map_pow (preHom σ) _ _)
  have tp : (ρ ≫ DegPre.trPt D' F p₀'.g.b) ≫ DegPre.prB D' F = (ρ ≫ DegPre.prB D' F) * (σ ≫ p₀'.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, m₁]
  rw [cy] at v₂
  rw [tp, ← liftB_tr hD hT hΘ₁ hΘ₂ ρ hb] at v₁
  have vu : @Eq (T'.left.presheaf.stalk z)ˣ (uVal D F k (hD.xe α) p₀.g.b (liftB hT hΘ₁ ρ) z J)
      (cubN (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J) k (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (σ ≫ p₀'.g.b)) (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) *
      (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) (pushHom (pull_grp hD) T' (σ ≫ p₀'.g.b)))⁻¹) := by
    rw [uVal, liftB_pt hD hT hΘ₁ ρ hb, liftB_pr hD hT hΘ₁ hΘ₂, push_cP, m₁]
  have vg : @Eq (T'.left.presheaf.stalk z)ˣ (val (p₀.g.s (hD.xe α)) σ.left z J)
      ((Ω (cP D' T' α * (σ ≫ p₀'.g.b)))⁻¹ * Ω (cP D' T' α) * Ω (σ ≫ p₀'.g.b) * (Ω 1)⁻¹ *
        val (p₀'.g.s α) σ.left z J') := by
    obtain ⟨hψ, hm⟩ := hg.2 α
    have pm := (maps_iff hD.w _ _ _ (p₀'.g.s α) (p₀.g.s (hD.xe α)) (𝟙 _) _
      (GeneratorPullback.pullAlong_le D.P.L _ (𝟙 _) _ _ hψ) (fun _ => rfl)).1 hm
    have c := DegPull.pmaps_val hψ pm σ.left z hJ hJ'
    erw [Category.comp_id] at c
    have p := prod_gt p₀'.g.b α (fun q => gw hD.w (σ.left ≫ q) z (J ((σ.left ≫ q) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' (σ.left ≫ q)))
    refine c.trans (congrArg₂ (· * ·) (p.trans ?_) rfl)
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
      MonObj.comp_one, hΩ]
  have vν : @Eq (T'.left.presheaf.stalk z)ˣ (val ν σ.left z J)
      (Ω 1 ^ (k : ℤ) * Ω (σ ≫ p₀'.g.b) ^ (-(k : ℤ)) * val ν' σ.left z J') := by
    have c := DegPull.pmaps_val hl hν σ.left z hJ hJ'
    erw [Category.comp_id] at c
    refine c.trans (congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl)
    have e₀ : σ.left ≫ DegPre.lineφ D' F p₀'.g.b 0 = (1 : T' ⟶ D'.P.A).left :=
      congrArg (fun q : T' ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) σ)
    have e₁ : σ.left ≫ DegPre.lineφ D' F p₀'.g.b 1 = (σ ≫ p₀'.g.b).left := rfl
    rw [e₀, e₁, hΩ]
    rfl
  have vm : @Eq (T'.left.presheaf.stalk z)ˣ
      (val (LB.mulGen D.P.L _ _ _ _ (p₀.g.s (hD.xe α)) ν) (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      (val (p₀.g.s (hD.xe α)) σ.left z J * val ν σ.left z J) := by
    rw [liftB_fst]; exact val_mul hJ _ _ _
  have key := units_rel (pushHom (pull_grp hD) T') Ω (cub_rel hG hD hJ hJ' Ω hΩ) k (cP D' T' α) (σ ≫ p₀'.g.b)
    (ρ ≫ DegPre.prB D' F) (val (p₀'.g.s α) σ.left z J') (val ν' σ.left z J')
  have fin := v₂.symm.trans (e.trans (congrArg₂ (· * ·) v₁ (congrArg Units.val
    (congrArg₂ (· * ·) vu (vm.trans (congrArg₂ (· * ·) vg vν))))))
  have alg : ∀ {S : Type} [CommRing S] (A₁ A₂ u u' : Sˣ) (a b : S), A₁ * u = A₂ * u' →
      A₂.val * b = A₁.val * a * u.val → b = a * u'.val := by
    intro S _ A₁ A₂ u u' a b h₁ h₂
    rw [mul_right_comm, ← Units.val_mul, h₁, Units.val_mul, _root_.mul_assoc] at h₂
    rw [(Units.mul_right_inj _).1 h₂, mul_comm]
  refine (alg _ _ _ _ _ _ key fin).trans ?_
  rw [val_mul hJ', uVal, m₁]

end Pull

end PhiPull

theorem phiRel_transport : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left), Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left → Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) → ∀ (k : ℕ) (p₀ : QkPt D F k) (p₀' : QkPt D' F k), p₀'.y = hD.xe.symm p₀.y → IsPullGtF φ hD F p₀.g p₀'.g → ∀ (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k))), ν.IsGen → ∃ ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineε k)), ν'.IsGen ∧ ∀ (s s₂ : Fam D F k) (s' s₂' : Fam D' F k), (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q))) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s₂.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s₂'.s x).f q))) → PhiRel D F k p₀ ν s s₂ → PhiRel D' F k p₀' ν' s' s₂' := by
  intro hG R R' _ _ _ _ φ D D' hD F _ _ _ hF Θ hΘ₁ hΘ₂ k p₀ p₀' hy hg ν hν
  have hT := PhiPull.base_eq hF
  have hl : ∀ i, DegPre.lineφ D' F p₀'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      𝟙 _ ≫ DegPre.lineφ D F p₀.g.b i := fun i => by
    obtain ⟨hψ, -⟩ := hg.2 0
    fin_cases i
    · exact hψ 3
    · exact hψ 2
  obtain ⟨ν', hν', pm⟩ := DegPull.exists_pmaps ((Geo.Tor.isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (𝟙 _) hl ν hν
  refine ⟨ν', hν', fun s s₂ s' s₂' H₁ H₂ H => ?_⟩
  rw [DVR.phiRel_iff hG p₀' ν' hν']
  exact PhiPull.phiVal_pull hD hT hΘ₁ hΘ₂ hG p₀ p₀' hy hg ν ν' hl pm s s₂ s' s₂' H₁ H₂
    ((DVR.phiRel_iff hG p₀ ν hν s s₂).1 H)

end GlobalTheory
