import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)

abbrev ColT (i : ℕ) : Type := (I.chain l u a).cls i → (I.chain l u a).Y i → ℂ

set_option maxHeartbeats 1000000 in

structure TwDat (Ch : ℕ → Type) where
  bad : ℕ → Set (HeightOneSpectrum (𝓞 B.host.F))
  chOf : ∀ i, (I.stp u a i).Cl → Ch i
  K : ∀ i (hi : i ≤ B.R.m) (β : Ch i), LevelChart (I.rec7 l Z) (B.T u) (bad i) i hi
    (fun c : {c // chOf i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

  kb : ∀ i, Ch i → TC.GA B (B.R.N i)
  kA : ∀ i, Ch i → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)
  xr : ∀ i, Ch i → (AE (I.rec7 l Z))ˣ
  b0 : ∀ i, Ch i → Idx I.sel (I.tup a) (I.idx a) i
  p0 : ∀ i, Ch i → PtAt B.R I.sel (I.tup a) (I.cst a) u i

  U : ∀ i, Ch i → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  chi : ∀ i β, U i β →* ℂˣ
  h : ∀ i (β : Ch i), {c // chOf i c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)
  e : AE (I.rec7 l Z)

variable {I l Z u a} {Ch : ℕ → Type}

namespace TwDat
variable (A : TwDat I l Z u a Ch)

structure Is : Prop where
  reads : ∀ i (hi : i ≤ B.R.m), I.Reads u a i (A.chOf i) (fun β => (A.K i hi β).lev.Lb) (fun β => (A.K i hi β).lev.U)
    (fun β => (A.K i hi β).lev.chi) (fun c => ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩).1)
    (fun c s => ((A.K i hi (A.chOf i c)).stabI ⟨c, rfl⟩ s).1) (A.kb i)
  top : ∀ β, I.TopPt l Z u a (A.kb B.R.m β)
  kA : ∀ i (hi : i ≤ B.R.m) β, A.kA i β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.kA i β) = (A.kb i β).1 ∧
    IsDetRoot _ (A.kA i β) (A.xr i β)
  base : ∀ i, i ≤ B.R.m → ∀ β, TC.PtOf (A.kb i β) (extTo I.SQ (A.p0 i β).1.1) ∧
    (A.p0 i β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)
  rep : ∀ i, i ≤ B.R.m → ∀ c, c.1 = A.b0 i (A.chOf i c) ∧ cosetIn ((I.stp u a i).rep c) = cosetIn (A.p0 i (A.chOf i c))
  U : ∀ i (hi : i ≤ B.R.m) β g, g ∈ A.U i β ↔ g ∈ GfC _ ∧ ∃ κ : (A.K i hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g
  chi : ∀ i (hi : i ≤ B.R.m) β (g : A.U i β) (κ : (A.K i hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 →
    A.chi i β g = (A.K i hi β).lev.chi κ
  h : ∀ i (hi : i ≤ B.R.m) β c, A.h i β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.h i β c) = ((A.K i hi β).y c).1.1
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u)

  fin : ∀ i (hi : i ≤ B.R.m) β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (A.K i hi β).lev.chi κ ^ n = 1

  bad_le : ∀ i, i ≤ B.R.m → ∀ v ∈ A.bad i, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch i) (γ : Ch (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ)
    (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z))

def abelian₂ (_A : TwDat I l Z u a Ch) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    FP (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) →ₗ[ℂ] ℂ :=
  ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') •
    jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))

def rd (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (ψ : ColT I l u a i) (y : (I.chain l u a).Y i) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i) → ℂ :=
  rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => ψ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩

end TwDat

def RamT (i : ℕ) (φ : ColT I l u a i) : Prop :=
  φ ∈ (I.fm l u a).Fi i ∧ ∀ v c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT i v s c (φ ((I.fm l u a).dil i v s c)) = 0

def VacT (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m) (c₀ : ℂ)
    (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : Prop :=
  ∀ g ∈ GfC _, ∀ h ∈ GfC _, ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N →
    Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' → ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

structure PinX (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ) : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  xs : ∀ j, j ≤ B.R.m → (x j).s = (fun _ => 1) ∧ (x j).B = (fun _ => 1) ∧ ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _
  vc : ∀ j, j < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (vac j)
  mv : ∀ j (hj : j + 1 ≤ B.R.m), c₀ j ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨j, hj⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om →
    VacT I l Z θ j hj (c₀ j) μ om (vac j)

structure PinColT (A : TwDat I l Z u a Ch) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj α γ z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j, j < B.R.m → ∀ α γ, cK j = (volLev (x j).vol (A.U j α) : ℂ) * w j α γ * c₀ j *
    (A.chr (j + 1) (A.xr j α) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) γ) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ RamT j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj β φ y

structure PinColN (A : TwDat I l Z u a Ch) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop
    extends PinColT A ψ θ x vac c₀ kom dd w Ram rd cK where
  ne : ∀ j, j < B.R.m → cK j ≠ 0

namespace TwDat.Is
variable {A : TwDat I l Z u a Ch}

theorem chOf_onto (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) : Function.Surjective (A.chOf i) := (hA.reads i hi).onto

theorem chart_ext (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (α β : Ch i) (hb : A.b0 i α = A.b0 i β)
    (hc : cosetIn (A.p0 i α) = cosetIn (A.p0 i β)) : α = β := by
  obtain ⟨c, rfl⟩ := hA.chOf_onto i hi α
  obtain ⟨c', rfl⟩ := hA.chOf_onto i hi β
  obtain ⟨h1, h2⟩ := hA.rep i hi c
  obtain ⟨h3, h4⟩ := hA.rep i hi c'
  exact ((hA.reads i hi).key c c').2 ⟨by rw [h1, h3, hb], by rw [h2, h4, hc]⟩

theorem chi_pow (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) : ∃ n : ℕ, 0 < n ∧ ∀ g, A.chi i β g ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := hA.fin i hi β
  refine ⟨n, hn, fun g => ?_⟩
  obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
  rw [hA.chi i hi β g κ hκ]
  exact h κ

theorem norm_chi (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (g : A.U i β) : ‖((A.chi i β g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := hA.chi_pow i hi β
  have e : ((A.chi i β g : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h g, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e hn.ne'

theorem lev_chi_eq_one (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (κ : (A.K i hi β).lev.U)
    (h : ∀ v, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v →
      Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) : (A.K i hi β).lev.chi κ = 1 :=
  (A.K i hi β).lev.chi_triv κ fun v hv => h v (hA.bad_le i hi v hv)

end TwDat.Is

section Pin
variable {A : TwDat I l Z u a Ch} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram : ∀ j, Set (ColT I l u a j)}
    {rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

theorem PinColN.w_ne (h : PinColN A ψ θ x vac c₀ kom dd w Ram rd cK) (j : ℕ) (hj : j < B.R.m) (α : Ch j) (γ : Ch (j + 1)) :
    w j α γ ≠ 0 ∧ volLev (x j).vol (A.U j α) ≠ 0 ∧ c₀ j ≠ 0 := by
  have hc := h.ne j hj
  rw [h.cst j hj α γ] at hc
  refine ⟨fun h0 => hc ?_, fun h0 => hc ?_, fun h0 => hc ?_⟩ <;> simp [h0]

theorem PinColT.vacT (hX : PinX I l Z ψ θ x vac c₀) (h : PinColT A ψ θ x vac c₀ kom dd w Ram rd cK) (j : ℕ) (hj : j + 1 ≤ B.R.m) :
    VacT I l Z θ j hj (c₀ j) (A.chr (j + 1)) (kom j) (vac j) :=
  (hX.mv j hj).2 a _ _ (h.is.chr ⟨j, hj⟩) (h.om j hj)

end Pin

end GlobalTheory.AdForm
