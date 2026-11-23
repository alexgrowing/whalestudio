import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtReduction

section Abstract
universe w u v
variable {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] {C : Type u} [Category.{v} C]

theorem pull_sq {F : C ⥤ ModuleCat.{w} R} {F₁ : C ⥤ ModuleCat.{w} R₁} {F₂ : C ⥤ ModuleCat.{w} R₂} {F₃ : C ⥤ ModuleCat.{w} R₃}
    {σ₁ : R →+* R₁} {σ₂ : R₁ →+* R₃} {σ₃ : R →+* R₂} {σ₄ : R₂ →+* R₃}
    (a : Mor F F₁ σ₁) (b : Mor F₁ F₃ σ₂) (c : Mor F F₂ σ₃) (e : Mor F₂ F₃ σ₄) (n : ℕ)
    (h : ∀ z, b.pullC n (a.pullC n z) = e.pullC n (c.pullC n z)) (x : CH.H F n) :
    b.pull n (a.pull n x) = e.pull n (c.pull n x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

end Abstract

variable {l : ℕ} [Fact l.Prime]

def lcCast {U : Type*} [TopologicalSpace U] {Q q : ℕ} (h : q ∣ Q) :
    LocallyConstant U (ZMod Q) →+ LocallyConstant U (ZMod q) where
  toFun f := f.map (ZMod.castHom h (ZMod q))
  map_zero' := by ext v; simp
  map_add' f g := by
    ext v
    exact map_add (ZMod.castHom h (ZMod q)) (f v) (g v)

theorem pow_div_pow_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ', Nat.mul_div_cancel _ h]

theorem rho_pow (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem lcRes_id {U : Scheme.{0}} (q : ℕ) (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  simp [lcRes]

theorem zeta_red (r : Roots l) (A : PAlg l) (n : ℕ) :
    (r.zeta A n).1 = (primRes (𝟙 (SU A)) (r.zeta A (n + 1))).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_pow_succ]
  change ((toΓ A.Ug).comp (kb A)) (r.ρ n).1 = (𝟙 (SU A) : SU A ⟶ SU A).appTop.hom (((toΓ A.Ug).comp (kb A)) (r.ρ (n + 1)).1) ^ l
  rw [rho_pow r n, map_pow]
  simp

theorem lc_red (hN : LcNat) (H : RIn l) (A : Test l) (n : ℕ) (f : LocallyConstant (SU A.obj) (ZMod (l ^ (n + 1)))) :
    A.obj.red n.le_succ (lcA A.obj (n + 1) f) = lcA A.obj n (lcCast (pow_dvd_pow l n.le_succ) f) :=
  (hN l H _ A.property n).2 f

variable {C : Type 1} [Category.{0} C]

def redMor (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) :
    Mor (probe H r G (n + 1)).L (probe H r G n).L (RingHom.id ℤ) where
  G := 𝟭 C
  τ c :=
    { toFun := lcCast (pow_dvd_pow l n.le_succ)
      map_add' := map_add _
      map_smul' := fun z x => (map_zsmul (lcCast (U := (probe H r G n).U c) (pow_dvd_pow l n.le_succ)) z x).trans rfl }
  nat φ x := rfl

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

variable {l : ℕ} [Fact l.Prime]

theorem red_lc_sq (hN : LcNat) (H : RIn l) (r : Roots l) (P : PAlg l ⥤ Type) (n j : ℕ)
    (c : CH.H (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L j) :
    (MSys P j).r n ((lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).pull j c) =
      (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j
        ((redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j c) :=
  pull_sq (F := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L)
    (F₁ := CH.modF (AcrEl P (n + 1))) (F₂ := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).L)
    (F₃ := CH.modF (AcrEl P n))
    (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)) (Mor.ofNatTrans (redEl P n.le_succ))
    (redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) j
    (fun z => funext fun s => lc_red hN H (s.obj (Fin.last j)).1 n (z s)) c

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

theorem fred_of_etRed : EtRed → FRed := by
  intro hE E hN l _ H r K M n j x
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := hE E.gen E.red E.op (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) (El M.P) (El M.P)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) (n + 1)) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M (𝟭 _) (n + 1)) (pts H r M (𝟭 _) n) (redMor H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => 𝟙 _) (fun φ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun c f => (lcRes_id _ _).symm)
    (fun c => (Category.id_comp _).symm)
    (fun c => zeta_red r _ n) 0 j x
  exact (red_lc_sq hN H r M.P n j _).trans (congrArg _ key)

end GlobalTheory.CompanionTheory.EtReduction
