import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ArchimedeanCocycleCharacter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueClassSumOfSeriesTotal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaDictCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Unif

variable {r : ℕ}

def toU {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  @Formalism.L2.Pj.Unf.mk _ _ _ _ _ _ _ Xo c σ r U.Comp U.fin U.X U.un

def ofU {σ : c.F →+* ℂ} (U : Formalism.L2.Pj.Unf Xo c σ r) : Formalism.L2.PjFree.Unf Xo c σ r :=
  @Formalism.L2.PjFree.Unf.mk _ _ _ _ _ _ _ Xo c σ r U.Comp U.fin U.X U.un

theorem isUnf_toU {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) :
    Formalism.L2.Pj.IsUnf (toU U) ↔ Formalism.L2.PjFree.IsUnf U := Iff.rfl

end Unif

def SameVal (f f' : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y

theorem SameVal.refl (f : Rul Xo c) : SameVal f f := fun _ _ _ _ _ => rfl

section Down

variable {n : ℕ}

def withC (d : DeltaDat Xo c n) (cδ' : Rul d.Xo₂ d.c₂) : DeltaDat Xo c n := { d with cδ := cδ' }

def FacTie (d : DeltaDat Xo c n) (cξ : Rul Xo c) (cδ' : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y →
      evR d.Xo₂ d.c₂ cδ' y₂ = evR Xo c cξ y * evR d.Xo₂ d.c₂ d.cδ y₂

variable {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {ι : Type} [Fintype ι]

end Down

section Act

variable {G0 : Type} [Group G0]

def CentreTie (e : G0 → LevGrp Dw l) : Prop :=
  (∀ z ∈ Subgroup.center G0, e z ∈ Subgroup.center (LevGrp Dw l)) ∧
    ∀ κ ∈ Subgroup.center (LevGrp Dw l), ∃ z ∈ Subgroup.center G0, e z = κ

def ActTie (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ z ∈ Subgroup.center G0, ∀ f ∈ sec Xo c a n, ∀ f' : Rul Xo c, IsLevelAct (e z) f f' ↔ SameVal f' (act z f)

end Act

section Row

variable {D : D7} (V : HSp D) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ)
  (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) (xi : ℝ)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {Tup : Type} (d : Tup → DeltaDat Xo c n) {ι : Tup → Type} [∀ t, Fintype (ι t)] (vol : Tup → ℚ)
  (J : Tup → Subgroup (UA E n)) (h : ∀ t, ι t → UA E n) (N : ∀ t, ι t → ℕ) (ep : Tup → UA E n → ℂ)
  (cξ : Tup → Rul Xo c) (φ : Tup → (Fin n → ConjQ Dw l) → c.F) (φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F)
  (dd : (E →+* ℂ) → ℤ) (lam : ∀ t, J t →* c.Fˣ) (thB : Tup → (UA E n → T) → GA D V → ℂ)
  (q₁ : ℕ) (S : Tup → Finset (Plc E))
  {G0 : Type} [Group G0] (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c)
  (cδ' : ∀ t, Rul (d t).Xo₂ (d t).c₂) (w : ∀ t, ι t → (Fin n → LevQ Dw (d t).l₂) → c.F) (κ : ∀ t, ι t → c.F)
  (thA : ∀ t, (ι t → T) → AutQ V → ℂ) (Pl : ∀ t, (ι t → T) → Prop)

def ChiTriv (n : ℕ) : Prop :=
  ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (Formalism.L2.PjFree.laU (U σ) a n k) γ = 1

structure Ties : Prop where
  centre : CentreTie e
  level : ActTie e act a n
  keeps : ∀ z ∈ Subgroup.center G0, ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, act z f ∈ Formalism.L2.PjFree.cusp Xo c U a n
  factor : ∀ t, FacTie (d t) (cξ t) (cδ' t)
  fourier : ∀ t i q, (d t).eF (w t i q) = fourierSum (d t).c₂ (coverDatum (d t) (φ t) (φδ t)) q
  scalar : ∀ t i, IsScalar (Dw := Dw) c (ep t) (h t i) (κ t i)
  placed : ∀ t x, Pl t x ↔ ∃ f, IsPlaced c dd (lam t) io f ∧ x = fun i => f (h t i)
  lift : ∀ t f, IsPlaced c dd (lam t) io f → ∀ g, thB t f g = thA t (fun i => f (h t i)) (Quotient.mk _ g)

abbrev RowA (LL : IntermediateField ℚ ℂ) (cc : (U σ).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow Xo c V (toU (U σ)) dict mu xi a act (fun t => withC (d t) (cδ' t)) ι w
    (fun t i => AdelicNormWeight.latOf (h t i)) N (fun t i => Nat.card (stab (J t) (h t i))) (fun t => (vol t : c.F)) κ io thA Pl LL
    (Formalism.L2.Pj.cusp Xo c (fun σ' => toU (U σ')) a n) cc ph

variable {V U σ dict mu xi a io d vol J h N ep cξ φ φδ dd lam thB q₁ S e act cδ' w κ thA Pl}

end Row

section LevelAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.LevelActionLaws

attribute [local instance] Over.cartesianMonoidalCategory

variable {G0 : Type} [Group G0] (lev : G0 → Dw.La →ₗ[𝓞 E] Dw.La)

variable (Xo c) in

def levelAct (g : G0) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S)
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G0) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (fun g => (lev g, LinearMap.id)) g' y y') g

variable (Xo c) in

def LevelLaws : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G0) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (fun g => (lev g, LinearMap.id)) g' y y')

end LevelAction

section Meet

variable {D : D7} {V : HSp D} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r} {σ : c.F →+* ℂ}
  {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {xi : ℝ}
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] {io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F}
  {Tup : Type} {d : Tup → DeltaDat Xo c n} {ι : Tup → Type} [∀ t, Fintype (ι t)] {vol : Tup → ℚ}
  {J : Tup → Subgroup (UA E n)} {h : ∀ t, ι t → UA E n} {N : ∀ t, ι t → ℕ} {ep : Tup → UA E n → ℂ}
  {cξ : Tup → Rul Xo c} {φ : Tup → (Fin n → ConjQ Dw l) → c.F} {φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F}
  {dd : (E →+* ℂ) → ℤ} {lam : ∀ t, J t →* c.Fˣ} {thB : Tup → (UA E n → T) → GA D V → ℂ}
  {q₁ : ℕ} {S : Tup → Finset (Plc E)}

theorem placed_ext {ι₀ : Type} {S₀ : Finset (Plc E)} {J₀ : Subgroup (UA E n)} {h₀ : ι₀ → UA E n} {lam₀ : J₀ →* c.Fˣ}
    (hr : IsRepSystem S₀ J₀ h₀) (hio : Function.Injective io) {f f' : UA E n → T}
    (hf : IsPlaced c dd lam₀ io f) (hf' : IsPlaced c dd lam₀ io f') (e : ∀ i, f (h₀ i) = f' (h₀ i)) : f = f' := by
  funext g
  obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := hr.2 g
  choose γ₀ hγ₀ using hγ.1
  have e₀ : γ.1 = (Matrix.of γ₀).map (diagE E) := by
    ext a b
    exact (hγ₀ a b).symm
  exact hio ((hf _ γ e₀ (h₀ i) ⟨k, hk⟩).trans (by rw [e i]; exact (hf' _ γ e₀ (h₀ i) ⟨k, hk⟩).symm))

omit [∀ t, Fintype (ι t)] in

theorem exists_lift (hr : ∀ t, IsRepSystem (S t) (J t) (h t)) (hio : Function.Injective io)
    (hinv : ∀ t f, IsPlaced c dd (lam t) io f → ∀ γ ∈ GQ V, ∀ g, thB t f (γ * g) = thB t f g) :
    ∃ thA : ∀ t, (ι t → T) → AutQ V → ℂ, ∀ t f, IsPlaced c dd (lam t) io f →
      ∀ g, thB t f g = thA t (fun i => f (h t i)) (Quotient.mk _ g) := by
  classical
  refine ⟨fun t x q => if hx : ∃ f, IsPlaced c dd (lam t) io f ∧ x = fun i => f (h t i) then thB t hx.choose q.out
    else 0, fun t f hf g => ?_⟩
  have hx : ∃ f', IsPlaced c dd (lam t) io f' ∧ (fun i => f (h t i)) = fun i => f' (h t i) := ⟨f, hf, rfl⟩
  simp only [dif_pos hx]
  rw [← placed_ext (hr t) hio hf hx.choose_spec.1 (congrFun hx.choose_spec.2)]
  have h1 := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
  rw [QuotientGroup.rightRel_apply] at h1
  have := hinv t f hf _ h1 (Quotient.mk (QuotientGroup.rightRel (GQ V)) g).out
  rwa [inv_mul_cancel_right] at this

variable {G0 : Type} [Group G0] {e : G0 → LevGrp Dw l} {act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c}
  {cδ' : ∀ t, Rul (d t).Xo₂ (d t).c₂} {w : ∀ t, ι t → (Fin n → LevQ Dw (d t).l₂) → c.F} {κ : ∀ t, ι t → c.F}
  {thA : ∀ t, (ι t → T) → AutQ V → ℂ} {Pl : ∀ t, (ι t → T) → Prop}

end Meet

end GlobalTheory.ThetaDictCompare
