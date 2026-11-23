import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedTrans

section
variable {O A R₁ R₂ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂]
  {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
  {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n s : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tr_dp (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (n : ℕ) :
    IsDPMorphism (redδ T h (n + 1)) (redδ T h n) (lnMap (RingHom.id T.B) l n.le_succ) := by
  have key : ∀ y : T.B, lnMap (RingHom.id T.B) l n.le_succ (Ideal.Quotient.mk (lnT T l (n + 1)) y) =
      Ideal.Quotient.mk (lnT T l n) y := fun y => by
    simp only [lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [Ideal.mem_comap, key]
    exact Ideal.mem_map_of_mem _ hy
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [key]
    simp only [redδ]
    rw [DividedPowers.Quotient.dpow_apply _ _ hy, DividedPowers.Quotient.dpow_apply _ _ hy, key]

variable (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {σ' : R₁ →+* R₂}
  (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')

theorem tr_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (r : R₁) :
    lnMap (RingHom.id T.B) l n.le_succ (iBar T l (n + 1) (d₁.ρ r)) = iBar T l n (d₂.ρ (σ' r)) := by
  rw [hρ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [← ha]
  simp only [iBar, lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]

def eta (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) : redObj T d₁ h ⟶ m.obj (redObj T d₂ h) :=
  mkH (lnMap (RingHom.id T.B) l n.le_succ) (tr_comm d₁ d₂ hρ T) (tr_dp T h n)
    (Ideal.map_le_iff_le_comap.1 (tr_dp T h n).1) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        refine Eq.trans ?_ ((m.obj (redObj T d₂ h)).w r).symm
        exact congrArg (Ideal.Quotient.mk _) (tr_comm d₁ d₂ hρ T r)
      · refine Eq.trans ?_ (hpt _ _).symm
        change Spec.map _ ≫ Spec.map _ ≫ pt T = Spec.map _ ≫ pt T
        rw [← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end

theorem red_trans : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := by
  intro O A R₁ R₂ Λ _ _ _ _ _ _ I γ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X q s 𝒱 σ' m c₁ c₂ lam hc₁ hc₂ h₀ hpt hρ r j x
  rw [CrystallineSemistableComparison.pull_pull lam, trM, CrystallineSemistableComparison.pull_pull lam]
  symm
  refine CrystallineSemistableComparison.cr_pull_eq (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R₁ J₁ δ₁ l) (ht := rfl) (κ := κ₁) _ _ ?η ?nat ?cmp j x
  case η => exact fun T => eta d₁ d₂ m hpt hρ T.obj T.property.1
  case nat =>
    intro T T' f y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl
  case cmp =>
    intro T y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl

end GlobalTheory.CompanionTheory.RedTrans
