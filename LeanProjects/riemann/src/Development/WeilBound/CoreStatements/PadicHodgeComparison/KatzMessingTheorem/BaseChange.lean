import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers

namespace CompanionTheory.KM.G4

variable (k : Type) [Field k]

structure SmV where
  X : Scheme.{0}
  q : X ⟶ Spec (CommRingCat.of k)
  d : ℕ
  smooth : SmoothOfRelativeDimension d q
  proper : IsProper q

variable {k} (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I)

abbrev OY (Y : SmV k) : Thick ((schFn Y.q).cr b ht κ) ⥤ CommAlgCat.{0} b.R := OA _ (RingHom.id b.R)

abbrev Hc (Y : SmV k) (n : ℕ) : Type 1 := CH.H (CH.modF (OY b ht κ Y)) n

def schPt {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) : (schFn Y'.q).ptK κ ⟶ (schFn Y.q).ptK κ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1, z.1.2 ≫ u), by
    obtain ⟨⟨f, y⟩, h⟩ := z
    change y ≫ Y'.q = _ at h
    change (y ≫ u) ≫ Y.q = _
    exact (Category.assoc y u Y.q).trans ((congrArg (fun t => y ≫ t) hu).trans h)⟩
  naturality B B' φ := by
    ext z
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Category.assoc _ _ _

def crPull {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) :
    GlobalTheory.LogCris.Mor ((schFn Y.q).cr b ht κ) ((schFn Y'.q).cr b ht κ) (RingHom.id b.R) :=
  crMor (RingHom.id b.R) rfl ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩ (schPt b κ u hu) (fun _ _ _ => rfl)

def pull {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) (n : ℕ) : Hc b ht κ Y n →ₗ[b.R] Hc b ht κ Y' n :=
  (omMor (crPull b ht κ u hu) (RingHom.id b.R) (fun _ => rfl)).pull n

def cup {Y : SmV k} {p q : ℕ} (x : Hc b ht κ Y p) (y : Hc b ht κ Y q) : Hc b ht κ Y (p + q) :=
  (CH.mulP (OY b ht κ Y)).cup rfl x y

def one (Y : SmV k) : Hc b ht κ Y 0 := CH.oneH (OY b ht κ Y)

def basePt {b' : Base} {κ' : k →+* b'.R ⧸ b'.I} (σ : b.R →+* b'.R) (hI : b.I.map σ ≤ b'.I)
    (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hI) (κ a)) (Y : SmV k) :
    (schFn Y.q).ptK κ' ⟶ (schFn Y.q).ptK κ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1.comp (Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hI)), z.1.2), by
    obtain ⟨⟨f, y⟩, h⟩ := z
    change y ≫ Y.q = _ at h
    change y ≫ Y.q = _
    rw [h]
    congr 2
    ext a
    simp [hκ]⟩
  naturality B B' φ := by
    ext z
    rfl

def baseChange {b' : Base} {ht' : b'.t = 1} {κ' : k →+* b'.R ⧸ b'.I} (σ : b.R →+* b'.R) (hp : b.p = b'.p)
    (hD : IsDPMorphism b.γ b'.γ σ) (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hD.1) (κ a))
    (Y : SmV k) (n : ℕ) : Hc b ht κ Y n →ₛₗ[σ] Hc b' ht' κ' Y n :=
  (omMor (crMor (ht := ht) (ht' := ht') σ hp hD (basePt b κ σ hD.1 hκ Y) (fun _ _ _ => rfl)) σ (fun _ => rfl)).pull n

omit [Field k] in

def degZ [Field k] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of k)) : ℕ :=
  letI : Algebra k Γ(Z, ⊤) := ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  Module.finrank k Γ(Z, ⊤)

def GysinAx (cl : ∀ (Y : SmV k) (Z : Scheme.{0}) (_ : Z ⟶ Y.X) (c : ℕ), Hc b ht κ Y (2 * c))
    (tr : ∀ Y : SmV k, Hc b ht κ Y (2 * Y.d) →ₗ[b.R] b.R) : Prop :=

  (∀ Y : SmV k, cl Y Y.X (𝟙 _) 0 = one b ht κ Y) ∧

  (∀ (Y Y' : SmV k) (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) (Z Z' : Scheme.{0}) (i : Z ⟶ Y.X) (i' : Z' ⟶ Y'.X)
      (u' : Z' ⟶ Z) (c : ℕ), IsClosedImmersion i → c ≤ Y.d → SmoothOfRelativeDimension (Y.d - c) (i ≫ Y.q) →
      IsPullback u' i' i u → c ≤ Y'.d → SmoothOfRelativeDimension (Y'.d - c) (i' ≫ Y'.q) →
      pull b ht κ u hu (2 * c) (cl Y Z i c) = cl Y' Z' i' c) ∧

  (∀ (Y : SmV k) (Z Z' W : Scheme.{0}) (i : Z ⟶ Y.X) (i' : Z' ⟶ Y.X) (j : W ⟶ Y.X) (a : W ⟶ Z) (a' : W ⟶ Z') (c c' : ℕ),
      IsClosedImmersion i → IsClosedImmersion i' → c + c' ≤ Y.d →
      SmoothOfRelativeDimension (Y.d - c) (i ≫ Y.q) → SmoothOfRelativeDimension (Y.d - c') (i' ≫ Y.q) →
      IsPullback a a' i i' → j = a ≫ i → SmoothOfRelativeDimension (Y.d - (c + c')) (j ≫ Y.q) →
      cup b ht κ (cl Y Z i c) (cl Y Z' i' c') = ((show 2 * (c + c') = 2 * c + 2 * c' by ring) ▸ cl Y W j (c + c'))) ∧

  (∀ (Y : SmV k) (Z : Scheme.{0}) (i : Z ⟶ Y.X), IsClosedImmersion i → IsFinite (i ≫ Y.q) → Etale (i ≫ Y.q) →
      tr Y (cl Y Z i Y.d) = (degZ (i ≫ Y.q) : b.R))

def admitted (b : Base) (κ : k →+* b.R ⧸ b.I) : Prop :=
  Function.Bijective κ ∧ b.p.Prime ∧ IsNilpotent (b.p : b.R)

def G4 : Prop := ∀ (k : Type) [Field k] [Finite k],
  ∃ (cl : ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) (Y : SmV k) (Z : Scheme.{0}) (_ : Z ⟶ Y.X) (c : ℕ),
      Hc b ht κ Y (2 * c))
    (tr : ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) (Y : SmV k), Hc b ht κ Y (2 * Y.d) →ₗ[b.R] b.R),
    (∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I), admitted b κ → GysinAx (k := k) b ht κ (cl b ht κ) (tr b ht κ)) ∧
    (∀ (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I), admitted b κ → admitted b' κ' →
      ∀ (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hD : IsDPMorphism b.γ b'.γ σ)
        (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hD.1) (κ a)) (Y : SmV k)
        (x : Hc b ht κ Y (2 * Y.d)), tr b' ht' κ' Y (baseChange b ht κ σ hp hD hκ Y (2 * Y.d) x) = σ (tr b ht κ Y x)) ∧
    (∀ (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I), admitted b κ → admitted b' κ' →
      ∀ (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hD : IsDPMorphism b.γ b'.γ σ)
        (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hD.1) (κ a))
        (Y : SmV k) (Z : Scheme.{0}) (i : Z ⟶ Y.X) (c : ℕ), IsClosedImmersion i → c ≤ Y.d →
        SmoothOfRelativeDimension (Y.d - c) (i ≫ Y.q) →
        baseChange b ht κ σ hp hD hκ Y (2 * c) (cl b ht κ Y Z i c) = cl b' ht' κ' Y Z i c)

end CompanionTheory.KM.G4
