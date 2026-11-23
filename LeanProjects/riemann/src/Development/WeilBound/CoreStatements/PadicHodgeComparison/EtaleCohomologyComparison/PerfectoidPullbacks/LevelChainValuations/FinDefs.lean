import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K}

structure RhoSys (S : LevSys R) (G : Model l K → Prop) (D : Dat R) (c1K : ∀ {M : Model l K}, D.Ch M → HdR M.q 2 → Prop) where
  ρ : ∀ {M : Model l K} (a : D.Ch M) (j m : ℕ), (D.H a).N j → (Module.Dual K (HdR M.q j) →+ (S.L m).B) → Prop
  ex : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x, ∃ f, ρ a j m x f
  uniq : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f f', ρ a j m x f → ρ a j m x f' → f = f'
  add : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x y f g, ρ a j m x f → ρ a j m y g → ρ a j m (x + y) (f + g)
  smul : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m (c : R.A) x f, ρ a j m x f →
    ρ a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f)
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j m x f → ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ
  lev : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j (m + 1) x f → ρ a j m x ((S.dB m).toAddMonoidHom.comp f)
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m (g : K.fixingSubgroup) x f, ρ a j m x f →
    ρ a j m ((D.H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (μ : D.Mo u hu a b), G M → G N →
    ∀ j m x f f', ρ b j m x f → ρ a j m (D.pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j m x f → ∀ n r : ℕ, n ≤ m → D.fil a j n x →
    ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) → f φ ∈ pdP (S.L m).γB (n - r)
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} m x y z f g h, ρ a i m x f → ρ a j m y g → ρ a (i + j) m z h →
    (D.H a).cup x y z → ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s')))
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ m x f, ρ a 0 m x f → (D.H a).one x → ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ m x f c, ρ a 2 m x f → D.c1H a x → c1K a c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c)

structure KapA (G : Model l K → Prop) (D : Dat R) (c1K : ∀ {M : Model l K}, D.Ch M → HdR M.q 2 → Prop) where
  κ : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.B)
  lin : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (c : R.A) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j (c • x) φ = R.i c * κ a j x φ
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (k : K) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j x (k • φ) = R.o k * κ a j x φ
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j ((D.H a).act j σ x) φ = R.σ σ (κ a j x φ)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b), G M → G N → ∀ (j : ℕ) (x : (D.H b).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j (D.pullH m j x) φ = κ b j x (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j n r : ℕ) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), D.fil a j n x → (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
    ∃ y ∈ R.P, R.tB ^ r * κ a j x φ = R.tB ^ n * y
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H a).N i) (y : (D.H a).N j)
    (z : (D.H a).N (i + j)), (D.H a).cup x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      κ a (i + j) z φ = ∑ s, ∑ s', κ a i x (b.coord s) * κ a j y (b'.coord s') * R.o (φ (cupK M.q rfl (b s) (b' s')))
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x : (D.H a).N 0, (D.H a).one x →
    ∀ φ : Module.Dual K (HdR M.q 0), κ a 0 x φ = R.o (φ (oneK M.q))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (x : (D.H a).N 2) (c : HdR M.q 2), D.c1H a x → c1K a c →
    ∀ φ : Module.Dual K (HdR M.q 2), κ a 2 x φ = R.o (φ c)

end CrystallineSemistableComparison.Pb.Kap
