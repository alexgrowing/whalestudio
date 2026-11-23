import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

section Sections

variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]

def secVal {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε)) : Γ(Y, ⊤) :=
  (Y.presheaf.map (homOfLE (wchart_triv φ (fun _ => PUnit.unit)).ge).op).hom (s.f (fun _ => PUnit.unit))

theorem map_self {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)) : (Y.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem sec_f_eq {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε))
    (j : J → (Inh.trivLB Z).ι) :
    s.f j = (Y.presheaf.map (homOfLE le_top).op).hom (secVal s) := by
  obtain rfl : j = fun _ => PUnit.unit := rfl
  exact ((map_map _ _ _).trans (map_self _ _)).symm

theorem map_top_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)}
    (h : (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = (Y.presheaf.map (homOfLE le_top).op).hom b) :
    a = b := by
  subst hV
  rwa [map_self, map_self] at h

theorem secVal_of_secRel {φ₁ : J₁ → (Y ⟶ Z)} {ε₁ : J₁ → ℤ} {s₁ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₁ ε₁)}
    {φ₂ : J₂ → (Y ⟶ Z)} {ε₂ : J₂ → ℤ} {s₂ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₂ ε₂)} {h : Y ⟶ Y}
    (hh : h = 𝟙 Y) {φ₃ : J₃ → (Y ⟶ Z)} {ε₃ : J₃ → ℤ} {u : LB.Gen (LB.LinComb (Inh.trivLB Z) φ₃ ε₃)}
    {a : Γ(Y, ⊤)ˣ} (hu : IsConst u a)
    (H : GeneratorPullback.SecRel (Inh.trivLB Z) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u) : secVal s₁ = secVal s₂ * a := by
  have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
  subst hh
  refine map_top_inj (top_unique (le_inf (le_inf (wchart_triv φ₁ _).ge (wchart_triv _ _).ge)
    (wchart_triv φ₃ _).ge)) (Eq.trans ?_ (this.trans ?_))
  · exact (map_map _ _ _).symm.trans (congrArg _ (sec_f_eq s₁ _).symm)
  · rw [map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (congrArg _ (congrArg _ (sec_f_eq s₂ _))).trans (app_res _ _ _ _ _)
    · exact (congrArg _ (congrArg Units.val (hu _))).trans (map_map _ _ _)

end Sections

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]

theorem trPt_eq_id (b : TF (R := K) F ⟶ (toricPre K X q).P.A) :
    DegPre.trPt (toricPre K X q) F b = 𝟙 _ :=
  CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)

def constUnit : Fˣ →* Γ((DegPre.BF (toricPre K X q) F).left, ⊤)ˣ :=
  (pullTop (fst (TF (R := K) F) (toricPre K X q).P.A).left).comp
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom)

theorem pullTop_zF_constUnit (c : Fˣ) :
    pullTop (DegPre.zF (toricPre K X q) F).left (constUnit q F c) = unitOn c := by
  have h : (DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]
  ext
  change ((DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left).appTop.hom
    (unitOn c).val = _
  rw [h]
  rfl

theorem secVal_of_phiRel {n : ℕ} (p : QkPt (toricPre K X q) F n) (t : Multiplicative X →* Fˣ)
    (hp : p.g = pt q F t)
    (w : LB.Gen (LB.LinComb (toricPre K X q).P.L (DegPre.lineφ _ F p.g.b) (DegPre.lineε n))) (c : Fˣ)
    (hw : IsConst w (unitOn c)) {s s' : Fam (toricPre K X q) F n} (h : PhiRel _ F n p w s s') (α β : X)
    (hβ : β = α + (show X from p.y)) :
    secVal (s'.s β) = secVal (s.s α) * (constUnit q F (t (Multiplicative.ofAdd α) * c)).val := by
  subst hβ
  have hg : IsConst (p.g.s α) (unitOn (t (Multiplicative.ofAdd α))) := by
    rw [hp]
    exact pt_isConst q F t α
  refine secVal_of_secRel (congrArg CommaMorphism.left (trPt_eq_id q F p.g.b)) (cg_isConst _ _ _)
    (h α (cg _ _ (constUnit q F (t (Multiplicative.ofAdd α) * c))) (cg_isGen _ _ _) ?_)
  exact corr_of_isConst
    ((isConst_pullGen (cg_isConst _ _ _) _).of_eq ((pullTop_zF_constUnit q F _).trans (unitOn_mul _ _)))
    (isConst_mulGen hg hw)

theorem weilQkIs_pt {n : ℕ} (p p' : QkPt (toricPre K X q) F n) (t t') (hp : p.g = pt q F t) (hp' : p'.g = pt q F t') :
    WeilQkIs (toricPre K X q) F n p p'
      ((t (Multiplicative.ofAdd (show X from p'.y)) * (t' (Multiplicative.ofAdd (show X from p.y)))⁻¹ : Fˣ) : F) := by
  intro w w' _ _ s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ β j
  obtain ⟨a, ha⟩ := exists_isConst w
  obtain ⟨c, rfl⟩ := unitOn_bijective.2 a
  obtain ⟨a', ha'⟩ := exists_isConst w'
  obtain ⟨c', rfl⟩ := unitOn_bijective.2 a'
  change X at β
  let y : X := p.y
  let y' : X := p'.y
  have e₁ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₁ (β - y - y') (β - y - y' + y') rfl
  have e₂ := secVal_of_phiRel q F p t hp w c ha h₂ (β - y - y' + y') β (show β = β - y - y' + y' + y by abel)
  have e₃ := secVal_of_phiRel q F p t hp w c ha h₃ (β - y - y') (β - y - y' + y) rfl
  have e₄ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₄ (β - y - y' + y) β (show β = β - y - y' + y + y' by abel)
  have e : secVal (s₂.s β) = (constUnit q F (t (Multiplicative.ofAdd y') * (t' (Multiplicative.ofAdd y))⁻¹)).val *
      secVal (s₄.s β) := by
    rw [e₂, e₄, e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, mul_left_comm (Units.val _), ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 3
    simp only [ofAdd_add, map_mul]
    generalize t (Multiplicative.ofAdd (β - y - y')) = A
    generalize t' (Multiplicative.ofAdd (β - y - y')) = B
    generalize t (Multiplicative.ofAdd y') = C
    generalize t' (Multiplicative.ofAdd y) = D
    ext
    push_cast
    field_simp
  refine (sec_f_eq (s₂.s β) j).trans ?_
  rw [e, map_mul, sec_f_eq (s₄.s β) j]
  rfl

end GlobalTheory.ToricData
