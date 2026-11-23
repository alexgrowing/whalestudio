import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OwnPrimeIntegralOfBqd
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def KF {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Submodule ℂ (SmT M) :=
  Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}

variable (L) in

def levRow : Subgroup (GA D (Yc D 0)) :=
  Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}))

variable (L) in

abbrev Rows (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (Yc D 0) S) : Submodule ℂ (SmT M →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) :=
  MultT θ M (levRow L : Set _) 1

variable (G : GridData L sc)

def lev (X : Node) : Subgroup (GA D (G.V X)) := Lev.levA (G.V X) (G.levCong X)

abbrev CoreForms (θ : InfFam D) (i : ℕ) {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core i)) S) :
    Submodule ℂ (SmT M →ₗ[ℂ] (GA D (G.V (.core i)) → ℂ)) :=
  MultT θ M (lev G (.core i) : Set _) 1

def depLat (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) where
  carrier := {u | u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ∧
    ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.latS p) (G.latT p))}
  zero_mem' := ⟨zero_mem _, fun e _ => by rw [smul_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun e he => by rw [smul_add]; exact add_mem (ha.2 e he) (hb.2 e he)⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, fun e he => by rw [smul_neg]; exact neg_mem (ha.2 e he)⟩

variable {G} (W : G.Weil)

def Dep (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsThetaFunO W.ψ (G.pS p) (G.pT p) f ∧ IsLatVac (heisO W.ψ (G.pS p) (G.pT p)) (depLat G p) f

def part (M : Vol G) (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) (n : ℕ) (h : n ≤ D.R.m) : Fn G (.grid n 0) :=
  liftP W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) u

theorem part_m (M : Vol G) (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) :
    part W M ρ Φ u D.R.m le_rfl = thetaChi W M ρ Φ u := rfl

def RapidRow (M : Vol G) (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∀ ρ Φ n h, RapidDec (G.V (.grid n 0)) (part W M ρ Φ u n h)

variable (G) in

abbrev CoreVol : Type := ∀ i, GlobalTheory.Unf.Vol (G.V (.core i))

def dn (v : CoreVol G) (i : ℕ) (f : Sch G (.coreDown i)) (F : Fn G (.core (i + 1))) : Fn G (.core i) :=
  fun g => ∫ h in (v (i + 1)).𝓕, W.kerA (.coreDown i) f h g * F h ∂(v (i + 1)).μ

def IsColChain (v : CoreVol G) (Ψ : ∀ i, Fn G (.core i)) : Prop :=
  (∀ i, i ≤ D.R.m → RapidDec (G.V (.core i)) (Ψ i)) ∧
    ∀ i, i < D.R.m → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))

def Reach (v : CoreVol G) : Set (Fn G (.core 0)) :=
  {F | ∃ Ψ : ∀ i, Fn G (.core i), IsColChain W v Ψ ∧ Ψ 0 = F ∧
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, Ψ D.R.m = pairVec (coefPlus G W.θ) ξ c}

variable (G) in

def per0 (M : Vol G) (F : Fn G (.core 0)) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  ∫ h in M.fd (.grid 0 0), F (stabilizerEmbedding G.sp.dec0 h) * u h ∂M.ν (.grid 0 0)

abbrev GP := ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}, G.Weil → Vol G → Prop

def OffQ (D : D7) : Prop := Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)

def All (Q : GP) : Prop :=
  ∀ (D : D7), OffQ D → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts) (G : GridData L sc) (W : G.Weil) (M : Vol G),
    M.IsRow → Q W M

def Gap (Q : GP) : Prop :=
  ∀ (D : D7), OffQ D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts), sc.cGap = 1 →
    ∀ (G : GridData L sc) (W : G.Weil) (M : Vol G), M.IsRow → Q W M

def Ev (Q : GP) : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (G : GridData L ⟨1, CF, large₂.sc.b⟩) (W : G.Weil) (M : Vol G),
      M.IsRow → Q W M

def SizeGap : Prop :=
  ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D

def DepFixed : Prop := All fun {D} {T} _ _ {G} W _ => ∀ i, i < D.R.m → ∀ p : Pair T, p = .chi i 0 ∨ p = .core i →
  ∀ f, Dep W p f → ∀ k ∈ lev G p.small, ∀ k' ∈ lev G p.big, W.om p (G.toPair p k k') f = f

def DatumDep : Prop := All fun {_} _ _ _ _ W _ => ∀ ρ Φ i, Dep W (.chi i.1 0) (W.datum ρ Φ i)

def CoreModels : Prop := All fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MP : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i)), cart MP = W.cart (.core i)

def RowRapid : Prop := Gap fun {D} _ {L} _ _ W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w, RapidRow W M (t w) ∧ ∀ ρ Φ, ThetaConv W M ρ Φ (t w)

def Factor : Prop := Gap fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ w : SmT M₀, ∃ a : G.RealVec → Module.Dual ℂ (coefPlus G W.θ).W → ℂ, ∀ t ∈ Rows L W.θ M₀, ∀ Ψ ∈ Cols G W.θ, ∀ Φ,
    ∃ l : ℂ, ∀ ρ ξ, fPsiPhi W M ρ ξ Ψ Φ (t w) = a ρ ξ * l

def PeriodNe : Prop := Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 → ∀ w : SmT M₀, w ≠ 0 →
    ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v ∈ KF MP, per0 G M (y v) (t w) ≠ 0

def CoreOnto : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ (v : CoreVol G)
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), cart MP = W.cart (.core 0) →
    ∀ y ∈ CoreForms G W.θ 0 MP, ∀ x ∈ KF MP, y x ∈ Submodule.span ℂ (Reach W v)

def Ascent : Prop := All fun {D} _ _ _ {G} W M => ∀ (v : CoreVol G) (Ψ : ∀ i, Fn G (.core i)), IsColChain W v Ψ →
  ∀ u, RapidRow W M u → per0 G M (Ψ 0) u ≠ 0 → ∃ ρ Φ, Bplus W M (Ψ D.R.m) (thetaChi W M ρ Φ u) ≠ 0

def WeakSep : Prop := Ev fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, t ≠ 0 → ∀ w : SmT M₀, w ≠ 0 → ∃ ρ ξ, ∃ Ψ ∈ Cols G W.θ, ∃ Φ, fPsiPhi W M ρ ξ Ψ Φ (t w) ≠ 0

theorem offQ_of_sizeRows {large₂ : SizeData₂ D} (h : SizeRows large₂) : OffQ D := by
  obtain ⟨⟨Pm, -, -⟩, -⟩ := h
  exact ⟨UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host D.host.pde_prime (Pm.level_split _ D.host.pde_level.1),
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host D.host.pde'_prime (Pm.level_split _ D.host.pde_level.2)⟩

theorem dep_vac (i : ℕ) (h : i < D.R.m) : Dep W (.chi i 0) (W.vac i) :=
  ⟨(W.vac_is i h).2.theta, fun u hu => (W.vac_is i h).2.lat.1 u hu.1, fun e he u hu => (W.vac_is i h).2.lat.2 e he u hu.1⟩

theorem All.gap {Q : GP} (h : All Q) : Gap Q := fun D q _ T L μ0 hL sc _ G W M hM => h D q T L μ0 hL sc G W M hM

theorem Gap.ev {Q : GP} (hs : SizeGap) (h : Gap Q) : Ev Q := fun ε _ _ => by
  obtain ⟨x, hx⟩ := hs ε
  exact ⟨x, fun D large₂ e a b T L μ0 hL G W M hM => h D (offQ_of_sizeRows b) (hx D large₂ e a b) T L μ0 hL _ rfl G W M hM⟩

end GlobalTheory.SepRows

end
