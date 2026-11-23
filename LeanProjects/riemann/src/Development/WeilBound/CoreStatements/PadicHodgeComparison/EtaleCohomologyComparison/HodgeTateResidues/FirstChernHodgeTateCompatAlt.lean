import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

structure RhoEx : Prop where
  ex : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m → ∀ x : Y.Fam M r j, CB.Comp x → ∃! w, L.Rho x w
  add : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (x y : Y.Fam M r j) w w', L.Rho x w → L.Rho y w' → L.Rho (x + y) (w + w')
  smul : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (c • x) (L.ι (L.lam c) • w)

def CoEx : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m →
  Spans L.γB M.q (L.QB M) L.tB_mem r j ∧ ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co

def HomRho : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n)),
  (∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u) →
  ∀ (r j : ℕ) (x : Y.Fam N r j) (w : HG (L.QB N) r j), L.Rho x w →
    L'.Rho (M := M) (fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n)) (h.fW u hu r j w)

def HomMu : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a r j : ℕ) (y : Hdg N.q a j),
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y)

structure MulRho : Prop where
  sh : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w)
  sh_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ), a ≤ r → ∀ y : Hdg M.q a j,
    shG (L.QB M) L.tB_mem k h j (L.μ M a r j y) = L.μ M a r' j y
  cup : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) w w',
    L.Rho x w → L.Rho y w' → L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w')
  cup_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c), a ≤ r → a' ≤ r' →
    ∀ (y : Hdg M.q a i) (y' : Hdg M.q a' j),
    cupG (L.QB M) h (L.μ M a r i y) (L.μ M a' r' j y') = L.μ M c s (i + j) (cupH M.q ha rfl y y')
  one : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q))

def FirstChernHodgeTateCompat : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), 1 < m → ∀ (D : E.LineData M.X), sSup (𝒱D D) = ⊤ →
  ∀ (x : Y.Fam M 1 2) (c : Hdg M.q 1 2), CB.IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → L.Rho x (L.μ M 1 1 2 c)

end CrystallineSemistableComparison.HT
