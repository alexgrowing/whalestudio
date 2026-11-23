import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AscFin

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def MxOff (P : GlobalTheory.FinPl.Pl D → Prop) {m n : ℕ} (x : Mx D m n) : Prop := ∀ i j, x i j ∈ idOff D P

structure FinLat {m n : ℕ} (A : AddSubgroup (Mx D m n)) : Prop where
  fin : ∀ a ∈ A, MxAt (fun _ => True) a
  cpt : IsCompact (A : Set (Mx D m n))
  opn : ∃ U : Set (Mx D m n), IsOpen U ∧ (0 : Mx D m n) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ A

structure IsBump {m n : ℕ} (β : Mx D m n → ℂ) : Prop where
  cont : Continuous β
  supp : HasCompactSupport β
  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, β (x + u) = β x
  smooth : ∀ (k : ℕ) (l : (Fin k → ℝ) →+ Mx D m n), Continuous l → (∀ t, (l t).map (finPart D) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => β (w + l t)

section Step

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)

structure Pieces (V₀ W W₀ : HSp D) (ρ σ : ℕ) where
  A₁ : AddSubgroup (Mx D W.rank ρ)
  A₂ : AddSubgroup (Mx D W.rank ρ)
  B₁ : AddSubgroup (Mx D σ V₀.rank)
  B₂ : AddSubgroup (Mx D σ V₀.rank)
  Γ₀ : AddSubgroup (WO V₀ W₀)

variable (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)

structure Pieces.Is (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  a₁ : FinLat p.A₁
  a₂ : FinLat p.A₂
  b₁ : FinLat p.B₁
  b₂ : FinLat p.B₂
  dualA : ∀ a, MxAt (fun _ => True) a → (a ∈ p.A₁ ↔ ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1)
  dualA' : ∀ a', MxAt (fun _ => True) a' → (a' ∈ p.A₂ ↔ ∀ a ∈ p.A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1)
  dualB : ∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ p.B₁ ↔ ∀ η ∈ p.B₂, ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)
  dualB' : ∀ η, MxAt (fun _ => True) η → (η ∈ p.B₂ ↔ ∀ ξ ∈ p.B₁, ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)
  uni : ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) → x ⬝ u.1.1 - x ∈ p.A₁ → psiUni ψ u.1 = 1
  fin₀ : ∀ u ∈ p.Γ₀, MxAt (fun _ => True) (show Mx D W₀.rank V₀.rank from u)
  vac₀ : ∃ f, VacG ψ V₀ W₀ p.Γ₀ f ∧ f ≠ 0

def cls (ψ : AddChar (AF D.host.F) ℂ) : Set (WO V W → ℂ) :=
  {Φ | IsThetaFunO ψ V W Φ ∧ (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧
    (∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) ∧
    (∀ ξ ∈ p.B₁, heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • Φ) ∧
    (∀ η ∈ p.B₂, heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ) ∧
    IsLatVac (fun w f => heisO ψ V W w f) (p.Γ₀.map ((dV.ext0 W).comp (dW.inc0 V₀))) Φ}

structure Cond (ψ : AddChar (AF D.host.F) ℂ) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D W) : Prop where
  pt : ∃ u : UX D ρ, ∃ a ∈ p.A₁, MxOff P (mt W h⁻¹ ⬝ (x ⬝ u.1.1) - x - a)
  shift : ∀ N : Mx D ρ ρ, MxAt P N → (∀ i j, j ≤ i → N i j = 0) → mt W h⁻¹ ⬝ (x ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1
  iso : ∀ ξ ∈ p.B₁, ∀ ξ' : Mx D σ V₀.rank, MxAt P ξ → mt W h ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' →
    ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ))

def CondK (ψ : AddChar (AF D.host.F) ℂ) (LW : Lat W) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D W) : Prop :=
  ∀ κ, InK W LW P κ → Cond dW p x y ψ P (h * κ)

def piecesOf (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) : Pieces V₀ W W₀ ρ σ where
  A₁ := Γ.comap (dV.extX W)
  A₂ := AddSubgroup.closure {a' | MxAt (fun _ => True) a' ∧
    ∀ a, dV.extX W a ∈ Γ → ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1}
  B₁ := Γ'.comap ((dV.ext0 W).comp (dW.incX V₀))
  B₂ := Γ'.comap ((dV.ext0 W).comp (dW.incY V₀))
  Γ₀ := Γ.comap ((dV.ext0 W).comp (dW.inc0 V₀))

structure Splits (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W)) : Prop where
  comp : ∀ u ∈ Γ, ∃ a ∈ p.A₁, ∃ a' ∈ p.A₂, ∃ ξ ∈ p.B₁, ∃ η ∈ p.B₂, ∃ w ∈ p.Γ₀,
    u = dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w) ∧
    ψ (symplO V W (dV.extX W x) (dV.extY W a')) = 1 ∧ ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) = 1

structure StdAt (LV : Lat V) (LW : Lat W) (v : GlobalTheory.FinPl.Pl D) : Prop where
  a : ∀ a, MxAt (· = v) a → (a ∈ p.A₁ ↔ dV.extX W a ∈ latO V W (LV : Set _) (LW : Set _) (· = v))
  a' : ∀ a ∈ p.A₁, ∃ b, MxOff (· = v) (a - b) ∧ dV.extX W b ∈ latO V W (LV : Set _) (LW : Set _) (· = v)
  b : ∀ ξ, MxAt (· = v) ξ → (ξ ∈ p.B₁ ↔ dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v))

structure GoodAt (ψ : AddChar (AF D.host.F) ℂ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D) : Prop where
  sdV : IsSelfDualC V LV
  sdV₀ : IsSelfDualC V₀ LV₀
  sdW : IsSelfDualC W LW
  sdW₀ : IsSelfDualC W₀ LW₀
  monoV : MonoAt dV LV LV₀ v
  monoW : MonoAt dW LW LW₀ v
  prim : PrimAt ψ dV LV v
  cols : ColsAt dV x LV LW v

end Step

def CosetAt (W : HSp D) (R : Subgroup (GA D W)) (LW : Lat W) (v : GlobalTheory.FinPl.Pl D) (h : GA D W) : Prop :=
  ∃ r ∈ R, r ∈ grpAt W (· = v) ∧ ∃ κ, InK W LW (· = v) κ ∧ h = r * κ

section Stab

variable {S : HSp D} {LS : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {z : Fin n → AE D} (hz : ∀ j, z j ∈ idAt D P) (i : Fin m) : (M *ᵥ z) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hz j)

theorem inK_one : InK S LS P 1 := ⟨one_mem _, fun z _ => by rw [mt_one, one_mulVec]⟩

theorem inK_mul {κ κ' : GA D S} (h : InK S LS P κ) (h' : InK S LS P κ') : InK S LS P (κ * κ') :=
  ⟨mul_mem h.1 h'.1, fun z hz => by rw [mt_mul, ← mulVec_mulVec, h'.2 z hz, h.2 _ (mulVec_idAt _ hz)]⟩

theorem inK_inv {κ : GA D S} (h : InK S LS P κ) : InK S LS P κ⁻¹ :=
  ⟨inv_mem h.1, fun z hz => by rw [h.2 _ (mulVec_idAt _ hz), mulVec_mulVec, mt_mul_inv, one_mulVec]⟩

variable {V₀ W W₀ : HSp D} {ρ σ : ℕ} {dW : HypDec W W₀ σ} {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ}
  {LW : Lat W} {h κ : GA D W}

theorem CondK.cond (H : CondK dW p x y ψ LW P h) : Cond dW p x y ψ P h := by
  simpa only [mul_one] using H 1 inK_one

theorem condK_mul (hκ : InK W LW P κ) : CondK dW p x y ψ LW P (h * κ) ↔ CondK dW p x y ψ LW P h :=
  ⟨fun H k hk => by simpa only [mul_assoc, mul_inv_cancel_left] using H _ (inK_mul (inK_inv hκ) hk),
    fun H k hk => by simpa only [mul_assoc] using H _ (inK_mul hκ hk)⟩

theorem cosetAt_mul {R : Subgroup (GA D W)} {v : GlobalTheory.FinPl.Pl D} (hκ : InK W LW (· = v) κ) :
    CosetAt W R LW v (h * κ) ↔ CosetAt W R LW v h :=
  ⟨fun ⟨r, a, b, k, hk, e⟩ => ⟨r, a, b, _, inK_mul hk (inK_inv hκ), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩,
    fun ⟨r, a, b, k, hk, e⟩ => ⟨r, a, b, _, inK_mul hk hκ, by rw [e, mul_assoc]⟩⟩

theorem cosetAt_of_inK {R : Subgroup (GA D W)} {v : GlobalTheory.FinPl.Pl D} (hκ : InK W LW (· = v) κ) : CosetAt W R LW v κ :=
  ⟨1, one_mem _, one_mem _, κ, hκ, (one_mul κ).symm⟩

end Stab

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def idLat {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}

variable (G) in

def shiftId : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
    ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹

variable (G) in

def latBig (i : ℕ) : AddSubgroup (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) :=
  latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid i 0)) : Set _) fun _ => True

def colsOf {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    Matrix (Fin n) (Fin k) D.host.E := fun i p => s p * a i (f p)

def IsAuxiliaryVectorWittDec {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) : Prop :=
  ∃ h : 2 * ρ ≤ c, d.e = colsOf a.a (Fin.castLE (by omega)) (fun p => (-D.host.xi0) ^ (p.1 + 1)) ∧
    ∃ s, d.e' = colsOf a.a (fun p : Fin ρ => (Fin.castLE (by omega) p : Fin c).rev) s

structure Std (F : Frames G) : Prop where
  zA : F.oz.iA = frameMat _ _ G.sp.dec0.ι
  zB : F.oz.iB *ᵥ (show Fin F.Lz.rank → D.host.E from F.ζ 0) = fun i => G.sp.dec0.a i 0
  ζ : ∀ ρ, F.ζ ρ = (-D.host.xi0) ^ ρ • F.ζ 0
  hB : ∀ ρ h, IsAuxiliaryVectorWittDec (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h)
  aB : ∀ ρ h, (F.dB ρ h).i₀ * (F.oB ρ h).iA = frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι
  zB' : ∀ ρ h, ((F.dB ρ h).i₀ * (F.oB ρ h).iB) *ᵥ F.ζ 0 = fun i => (G.colDec (2 * ρ + 2) (by omega) h).a i ⟨ρ, by omega⟩
  hJ : ∀ ρ h, IsAuxiliaryVectorWittDec (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h)
  aJ : ∀ ρ h, (F.dJ ρ h).i₀ = frameMat _ _ (G.colDec (2 * ρ + 1) (by omega) (by omega)).ι

def lat0 (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : Lat (F.V₀ ρ) :=
  (G.Λ (.grid (2 * ρ + 2) 0)).comap ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E))

def lineLat (F : Frames G) : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))
  | 0 => (latCore G 0).comap ((F.oz.resT _).symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _))
  | σ + 1 => latO _ _ (G.Λ (.core (2 * (σ + 1) + 1)) : Set _)
      (idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _)
      fun _ => True

abbrev pcBF (W : G.Weil) (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :=
  piecesOf (F.dB ρ h) (F.dJ ρ h) W.ψ (latRow G (2 * ρ + 1)) (latBig G (2 * ρ + 1))

abbrev pcFB (W : G.Weil) (F : Frames G) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) :=
  piecesOf (F.dJ (σ + 1) h) (F.dB σ h') W.ψ (latRow G (2 * σ + 2)) (latBig G (2 * σ + 2))

abbrev xFB (F : Frames G) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) := xLast (F.dB σ h') (vecB (F.oB σ h') (F.ζ (σ + 1)))

abbrev yBF (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) := yZero (F.V₀ ρ) ρ (vecB (F.oB ρ h) (F.ζ (ρ + 1)))

def OnStd (Q : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}, G.Weil → Frames G → Prop) : Prop :=
  All fun {_} _ _ _ {G} W _ => ∀ F : Frames G, Std F → Q W F

example {m n : ℕ} : IsBump (0 : Mx D m n → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, fun _ _ _ _ _ => contDiff_const⟩

end GlobalTheory.AscFin

end
