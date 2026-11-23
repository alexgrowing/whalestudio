import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X Y : Scheme.{0}}

def chartFn {L : LB X} {d : ℤ} (s : LB.Sec (pw L d)) (i : L.ι) : Γ(X, L.U i) := s.f i

theorem map_prod_eq_pow_mul {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* B)
    (φ' : A' →+* B) {k : ℕ} (x : Fin k → A) (y : Fin k → A') (g : B)
    (h : ∀ l, φ (x l) = g * φ' (y l)) : φ (∏ l, x l) = g ^ k * φ' (∏ l, y l) := by
  rw [map_prod, map_prod, Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def secMono {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d))
    (w : Fin k → τ) : LB.Sec (pw L D) where
  f i := ∏ l, chartFn (a (w l)) i
  compat i j := by
    subst h
    have := map_prod_eq_pow_mul (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom
      (fun l => chartFn (a (w l)) i) (fun l => chartFn (a (w l)) j)
      ((L.g i j ^ d : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) (fun l => (a (w l)).compat i j)
    refine this.trans ?_
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    rfl

def pullPow {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ) :
    LB.Iso (pw N t) ((pw N' t).pull β) :=
  ⟨fun p => v.s p ^ t⟩

theorem prod_mul_prod_eq {B τ : Type} [CommMonoid B] (φ : τ → B) {k : ℕ} (w₁ w₂ w₃ w₄ : Fin k → τ)
    (hw : Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) :
    (∏ l, φ (w₁ l)) * ∏ l, φ (w₂ l) = (∏ l, φ (w₃ l)) * ∏ l, φ (w₄ l) := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((Finset.univ.val.map w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  rw [key, key, key, key, ← Multiset.prod_add, ← Multiset.prod_add, ← Multiset.map_add, ← Multiset.map_add, hw]

theorem secMono_mul : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (w₁ w₂ w₃ w₄ : Fin k → τ), (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (secMono h a w₁).f c * (secMono h a w₂).f c = (secMono h a w₃).f c * (secMono h a w₄).f c := by
  intro X L τ d D k h a w₁ w₂ w₃ w₄ hw c
  exact prod_mul_prod_eq (fun i => chartFn (a i) (show L.ι from c)) w₁ w₂ w₃ w₄ hw

theorem zpow_mul_inv_eq {G : Type} [CommGroup G] (a a' b b' : G) (t : ℤ) (h : a' = a ^ t) (h' : b' = b ^ t) :
    (a * b⁻¹) ^ t = a' * b'⁻¹ := by
  rw [h, h', mul_zpow, inv_zpow]

theorem mapmap_zpow {G H K : Type} [CommGroup G] [CommGroup H] [CommGroup K] (f : G →* H) (g : H →* K)
    (x : G) (t : ℤ) : g (f (x ^ t)) = (g (f x)) ^ t := by
  rw [map_zpow, map_zpow]

theorem pull_pw_g {Z W : Scheme.{0}} (L : LB W) (φ : Z ⟶ W) (t : ℤ) (i j : PUnit → L.ι) :
    ((pw L t).pull φ).g i j = ((L.pull φ).g i j) ^ t := by
  refine (pull_g (pw L t) φ i j).trans ((mapmap_zpow (pullU φ _) (res _) (L.g _ _) t).trans ?_)
  exact congrArg (· ^ t) (pull_g L φ i j).symm

theorem pullPow_isGen : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ), v.IsGen → (pullPow v t).IsGen := by
  intro X Y N N' β v t hv p q
  have := congrArg (· ^ t) (hv p q)
  simp only [mul_zpow, ← map_zpow] at this
  refine this.trans ?_
  congr 1
  refine zpow_mul_inv_eq (G := Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2 ⊓ ((N'.pull β).U q.1 ⊓ N.U q.2))ˣ)
    (res _ ((N'.pull β).g p.1 q.1)) (res _ (((pw N' t).pull β).g p.1 q.1)) (res _ (N.g p.2 q.2))
    (res _ ((pw N t).g p.2 q.2)) t ?_ ?_
  · exact (congrArg _ (pull_pw_g N' β t p.1 q.1)).trans (map_zpow _ _ _)
  · exact map_zpow _ _ _

theorem secMaps_secMono : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw N d)) (a' : τ → LB.Sec (pw N' d)), (∀ i, SecMaps (pullPow v d) (a i) (secPull (a' i) β)) → ∀ w : Fin k → τ, SecMaps (pullPow v D) (secMono h a w) (secPull (secMono h a' w) β) := by
  intro X Y N N' β v τ d D k h a a' hmaps w p
  subst h
  let u : Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2)ˣ := v.s p
  refine (map_prod_eq_pow_mul
    ((resG X (inf_le_left)).comp ((resG X (GlobalTheory.Cartier.pull_U N' β p.1).le).comp (β.app _).hom))
    (resG X inf_le_right) (fun l => chartFn (a' (w l)) (p.1 ⟨⟩)) (fun l => chartFn (a (w l)) p.2)
    (u ^ d).val (fun l => hmaps (w l) p)).trans ?_
  congr 1
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  rfl

theorem nonzeroLocus_secMono_const : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (i : τ), 1 ≤ k → nonzeroLocus (secMono h a (fun _ => i)) = nonzeroLocus (a i) := by
  intro X L τ d D k h a i hk
  refine iSup_congr fun c => ?_
  change X.basicOpen (∏ l : Fin k, chartFn (a i) c) = X.basicOpen (chartFn (a i) c)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Scheme.basicOpen_pow _ _ (by omega)

end GlobalTheory.CompanionTheory.FormalAlg
