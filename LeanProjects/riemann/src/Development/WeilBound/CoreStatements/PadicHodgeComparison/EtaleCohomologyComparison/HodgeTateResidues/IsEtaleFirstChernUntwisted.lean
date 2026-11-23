import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.KatoCoprimality.CoprimePowers.CoprimePowerSubOne.CoprimePowSubOne

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (K) in

def kC : K →+* ℂ_[l] := (clToC l).comp K.val.toRingHom

variable (l) in

def qC : ℚ_[l] →+* ℂ_[l] := (clToC l).comp (algebraMap ℚ_[l] (PadicAlgCl l))

abbrev genD {M : Model l K} (D : E.LineData M.X) : E.LineData M.gen := D.pb (pullback.fst _ _)

open GlobalTheory.EtC in

def IsEtaleFirstChernUntwisted (r : E.Roots l) {M : Model l K} (D : E.LineData M.X) (v : M.T 2) : Prop :=
  ∃ (D' : E.LineData (E.gb M)) (π : D'.Y ⟶ D.Y) (L : cech D'.f ⟶ ofCat (glCat 1)) (x : ∀ n, Ht (l ^ n) M.spc ((2 : ℕ) : ℤ) 1),
    D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : E.gb M ⟶ M.X) D' π ∧ D'.IsMap L ∧
    (∀ n, pull _ (cechAug D'.f) _ 2 (x n) = c1 (l ^ n) L) ∧
    ∀ n, v.lev n = (cup (l ^ n) (x n) (rootClass (-1) (r.zetaX M n))).cast rfl rfl

variable (l K) in
set_option maxHeartbeats 1000000 in

structure HTPre where
  h : ∀ (M : Model l K) (a n : ℕ), M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l])
  lin : ∀ (M : Model l K) (a n : ℕ) (z : ℚ_[l]) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)), h M a n (z • v) φ = qC l z * h M a n v φ
  lin' : ∀ (M : Model l K) (a n : ℕ) (k : K) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)), h M a n v (k • φ) = kC K k * h M a n v φ

  fin : ∀ (M : Model l K), M.Sm → ∀ a n : ℕ, FiniteDimensional K (Hdg M.q a n) ∧ (n < a → Subsingleton (Hdg M.q a n))

  equi : ∀ (M : Model l K), M.Sm → ∀ (a n : ℕ) (σ : K.fixingSubgroup) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)),
    qC l (GaloisFrobeniusFixed.χ σ.1) ^ a * h M a n (M.act n σ v) φ = GaloisFrobeniusFixed.σC σ.1 (h M a n v φ)

  nat : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p), M.Sm → N.Sm → ∀ (a n : ℕ) (v : N.V n)
    (φ : Module.Dual K (Hdg M.q a n)),
    h M a n (Model.pullV u hu n v) φ = h N a n v (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a n)

  cup : ∀ (M : Model l K), M.Sm → ∀ {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)), M.CupT x y z →
    ∀ {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i)) (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j))
      (c : ℕ) (φ : Module.Dual K (Hdg M.q c (i + j))),
      h M c (i + j) (M.toV _ z) φ = ∑ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), ∑ s, ∑ s',
        h M p.1.1 i (M.toV _ x) ((b p.1.1).coord s) * h M p.1.2 j (M.toV _ y) ((b' p.1.2).coord s') *
          kC K (φ (cupH M.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (b p.1.1 s) (b' p.1.2 s')))

  one : ∀ (M : Model l K), M.Sm → ∀ v : M.T 0, (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) →
    ∀ φ : Module.Dual K (Hdg M.q 0 0), h M 0 0 (M.toV 0 v) φ = kC K (φ (oneH M.q))

  first_chern_class_exists : ∀ (M : Model l K), M.Sm → ∀ (D : E.LineData M.X), Etale D.f → sSup (Pb.𝒱D D) = ⊤ →
    (∀ r : E.Roots l, ∃ v, IsEtaleFirstChernUntwisted r D v) ∧ ∃! c, IsDlogFirstChernClass M.q (genD D) c

  c1 : ∀ (M : Model l K), M.Sm → ∀ (D : E.LineData M.X), Etale D.f → sSup (Pb.𝒱D D) = ⊤ → ∀ (r : E.Roots l) (v : M.T 2) (c : Hdg M.q 1 2),
    IsEtaleFirstChernUntwisted r D v → IsDlogFirstChernClass M.q (genD D) c →
    (∀ φ, h M 1 2 (M.toV 2 v) φ = kC K (φ c)) ∧ ∀ a, a ≠ 1 → ∀ φ, h M a 2 (M.toV 2 v) φ = 0

def HTPre.Inj (P : HTPre l K) (M : Model l K) (n : ℕ) : Prop :=
  ∀ {k : ℕ} (b : Module.Basis (Fin k) ℚ_[l] (M.V n)) (z : Fin k → ℂ_[l]), (∀ a φ, ∑ i, z i * P.h M a n (b i) φ = 0) → z = 0

def HTPre.Top (P : HTPre l K) (M : Model l K) (d : ℕ) : Prop :=
  ∀ {k : ℕ} (b : Module.Basis (Fin k) ℚ_[l] (M.V (2 * d))) (z : Fin k → ℂ_[l]), (∀ φ, ∑ i, z i * P.h M d (2 * d) (b i) φ = 0) → z = 0

def HodgeTateMapExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ P : HTPre l K, ∀ M : Model l K, M.Sm → (∀ n, P.Inj M n) ∧ ∀ d, M.Conn d → P.Top M d

end CrystallineSemistableComparison.HT
