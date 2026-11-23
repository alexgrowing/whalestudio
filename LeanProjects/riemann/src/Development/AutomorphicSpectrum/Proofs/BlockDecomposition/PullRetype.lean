import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedNat

universe w w' v u v' u'

section Retype
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ σ₂ : R →+* R'}

def retype (m : CH.Mor F F' σ) (σ₂ : R →+* R') (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) : CH.Mor F F' σ₂ where
  G := m.G
  τ T :=
    { toFun := m.τ T
      map_add' := map_add _
      map_smul' := fun a x => (LinearMap.map_smulₛₗ (m.τ T) a x).trans (h T a _) }
  nat := m.nat

theorem pull_retype (m : CH.Mor F F' σ) (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) (n : ℕ) (x : CH.H F n) :
    (retype m σ₂ h).pull n x = m.pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
  have hb : CH.d F' n (m.pullC n a) = 0 := by rw [CH.Mor.d_pullC]; exact (congrArg _ ha).trans (map_zero _)
  exact (CrystallineSemistableComparison.P.mapH_cls (retype m σ₂ h).hom n a ha hb).trans (CrystallineSemistableComparison.P.mapH_cls m.hom n a ha hb).symm

end Retype

section Eta
variable {O A₁ A₂ R₁ R₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n s : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ')

theorem eta_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (r : R₁) :
    iBar ((nm.mor 0).obj T) l n (d₁.ρ r) = iBar T l n (d₂.ρ (σ' r)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [hρ, ← ha]
  rfl

def etaR (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (h₁ : TF l s ((nm.mor 0).obj T)) (h₂ : TF l s T) :
    redObj ((nm.mor 0).obj T) d₁ h₁ ⟶ m.obj (redObj T d₂ h₂) :=
  mkH (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun r => eta_comm d₁ d₂ nm hρ T r)
    ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have hw1 := (redObj ((nm.mor 0).obj T) d₁ h₁).w r
        have hw2 := (m.obj (redObj T d₂ h₂)).w r
        have h3 : Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((redObj ((nm.mor 0).obj T) d₁ h₁).i r) =
            Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((m.obj (redObj T d₂ h₂)).i r) :=
          congrArg (Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J) (eta_comm d₁ d₂ nm hρ T r)
        exact (congrArg (Ideal.quotientMap (m.obj (redObj T d₂ h₂)).J
          (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
      · have e := hpt _ (redObj T d₂ h₂).y
        refine Eq.trans ?_ e.symm
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (qBar ((nm.mor 0).obj T) l n)) ≫ (pt T ≫ nm.u) =
          (Spec.map (CommRingCat.ofHom (qBar T l n)) ≫ pt T) ≫ nm.u
        rw [Category.assoc, ← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end Eta

section Main
variable {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a))

include hc₁ hc₂ h₀ in

theorem lam_mem (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (a : Λ₁) :
    σ (lam₁ a) - lam₂ (σ₀ a) ∈ Ideal.span {(l : A₂) ^ n} := by
  refine Ideal.Quotient.eq.1 ?_
  have e := hρ (c₁ a)
  rw [h₀, hc₂, hc₁] at e
  exact e.symm

include hc₁ hc₂ h₀ in

theorem lam_smul (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (r : Option ℤ)
    (T : (TS γ₂ q₂ l s {⊤}).FullSubcategory) (a : Λ₁)
    (y : (sq (IdF.top (sP (TS γ₂ q₂ l s {⊤})).A) (stdI (TS γ₂ q₂ l s {⊤}) r ((l : A₂) ^ n))).obj T) :
    (σ.comp lam₁) a • y = (lam₂.comp σ₀) a • y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext (Ideal.Quotient.eq.2 ?_)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (lam_mem d₁ d₂ c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ a)
  refine ln_le q₂ s {⊤} r T ?_
  change T.obj.i (σ (lam₁ a)) * (show T.obj.B from b) - T.obj.i (lam₂ (σ₀ a)) * (show T.obj.B from b) ∈ lnT T.obj l n
  rw [← sub_mul, ← map_sub, ← hz, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Main

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := by
  intro O A₁ A₂ R₁ R₂ Λ₁ Λ₂ _ _ _ _ _ _ _ _ _ I₁ I₂ γ₁ γ₂ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X₁ X₂ q₁ q₂ s σ nm σ' m c₁ c₂ lam₁ lam₂
    hc₁ hc₂ σ₀ h₀ hpt hρ r j x
  let S2 := (nmS nm l s).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (nm_std nm l s r n)
  letI t1 : RingHomCompTriple σ₀ lam₂ (lam₂.comp σ₀) := ⟨rfl⟩
  letI t2 : RingHomCompTriple lam₁ σ (σ.comp lam₁) := ⟨rfl⟩
  let M1 : CH.Mor _ _ (lam₂.comp σ₀) := (B.omMor m σ₀ h₀).comp (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r)
  let M2 : CH.Mor _ _ (σ.comp lam₁) := (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).comp S2
  have hsc := lam_smul (q₂ := q₂) d₁ d₂ s c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ r
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := lam₂.comp σ₀) (B.omMor m σ₀ h₀) (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r) j x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := σ.comp lam₁) (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r) S2 j x).1
  have h3 := pull_retype M2 (σ₂ := lam₂.comp σ₀) hsc j x
  let η : (retype M2 (lam₂.comp σ₀) hsc).G ⟶ M1.G :=
    { app := fun T => etaR d₁ d₂ nm m hpt hρ T.obj T.property.1 T.property.1
      naturality := fun T T' f => hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) }
  have h4 := CrystallineSemistableComparison.P.prism (retype M2 (lam₂.comp σ₀) hsc) M1 η (fun T y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
    rfl) j x
  exact h1.symm.trans (h4.symm.trans (h3.trans h2))

end GlobalTheory.CompanionTheory.RedNat
