import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernClassOnThickenings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers CompanionTheory.KM.G4 GlobalTheory.CompanionTheory.KMGys ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMGys.Trace

variable {k : Type} [Field k]

def CutsOut {X D : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (s : L.Sec) (j : D ⟶ X) : Prop :=
  IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X) (i : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U i),
    (g.appLE (L.U i) ⊤ h).hom (s.f i) = 0 ↔ ∃ g' : T ⟶ D, g' ≫ j = g

def cupTop (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) {Y : SmV k} {e : ℕ} (hd : 2 + 2 * e = 2 * Y.d)
    (z : Hc b ht κ Y 2) (x : Hc b ht κ Y (2 * e)) : Hc b ht κ Y (2 * Y.d) :=
  (CH.mulP (OY b ht κ Y)).cup hd z x

abbrev TrAt (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) : Type 1 :=
  ∀ Y : SmV k, Hc b ht κ Y (2 * Y.d) →ₗ[b.R] b.R

abbrev TrFam (k : Type) [Field k] : Type 1 :=
  ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I), TrAt b ht κ

structure IsTraceAt (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) (tr : TrAt b ht κ) : Prop where
  proj : ∀ (Y : SmV k) (e : Y.X ≅ PSpace k Y.d), e.hom ≫ PSpace.str k Y.d = Y.q → ∀ h : Hc b ht κ Y 2,
    IsFirstChernClassOnThickenings b ht κ Y ((GlobalTheory.ProjSpace.O1 k Y.d).pull e.hom)
      (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (GlobalTheory.ProjSpace.O1_isLB k Y.d) e.hom) h →
    tr Y (powH b ht κ h Y.d) = 1
  point : ∀ Y : SmV k, IsProjOver Y.q → ∀ hd : 0 = 2 * Y.d, tr Y (hd ▸ one b ht κ Y) = (degZ Y.q : b.R)
  pointTr : ∀ Y : SmV k, IsProjOver Y.q → ∀ (hd : 0 = 2 * Y.d) (x : Hc b ht κ Y 0)
    (m : Hc b ht κ Y 0 →ₗ[b.R] Hc b ht κ Y 0), (∀ y, m y = cup b ht κ x y) →
    tr Y (hd ▸ x) = LinearMap.trace b.R (Hc b ht κ Y 0) m
  div : ∀ (D Y : SmV k) (j : D.X ⟶ Y.X) (hj : j ≫ Y.q = D.q),
    IsProjOver Y.q → ∀ (hd : 2 + 2 * D.d = 2 * Y.d) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB Y.X) (hL : L.IsLB) (s : L.Sec), CutsOut s j →
    ∀ z : Hc b ht κ Y 2, IsFirstChernClassOnThickenings b ht κ Y L hL z → ∀ x : Hc b ht κ Y (2 * D.d),
    tr Y (cupTop b ht κ hd z x) = tr D (pull b ht κ j hj (2 * D.d) x)

def BaseCompat (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I)
    (t : TrAt b ht κ) (t' : TrAt b' ht' κ') : Prop :=
  ∀ (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hD : IsDPMorphism b.γ b'.γ σ)
    (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hD.1) (κ a)) (Y : SmV k),
    IsProjOver Y.q → ∀ x : Hc b ht κ Y (2 * Y.d),
    t' Y (baseChange (ht' := ht') b ht κ σ hp hD hκ Y (2 * Y.d) x) = σ (t Y x)

structure IsTrace (tr : TrFam k) : Prop where
  atBase : ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I), admitted b κ → IsTraceAt b ht κ (tr b ht κ)
  base : ∀ (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I),
    admitted b κ → admitted b' κ' → BaseCompat b b' ht ht' κ κ' (tr b ht κ) (tr b' ht' κ')

end GlobalTheory.CompanionTheory.KMGys.Trace
