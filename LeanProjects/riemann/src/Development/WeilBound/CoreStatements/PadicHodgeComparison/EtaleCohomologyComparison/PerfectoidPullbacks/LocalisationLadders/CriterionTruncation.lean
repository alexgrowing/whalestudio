import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.TruncationHomExt

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

namespace Cut

variable (E : Frame Φ (d + 1))

abbrev Φ1 : PDF R (Cut E) := Φ.res (U E)

def E1 : Frame (Φ1 E) d where
  D := ⟨E.D, 𝟙 E.D⟩
  ne Y := ⟨⟨Y.s, by rw [Category.id_comp]; exact E.τ_self 0 Y.s⟩⟩
  τ i {Y} σ σ' := E.τ i.succ σ.1 σ'.1
  mem i {Y} σ σ' := E.mem i.succ σ.1 σ'.1
  add i {Y} σ σ' σ'' := E.add i.succ σ.1 σ'.1 σ''.1
  nat i {Y Y'} σ σ' φ := E.nat i.succ σ.1 σ'.1 φ.1
  bij {Y} σ y hy := by
    have h0 : ∀ σ' : (⟨E.D, 𝟙 E.D⟩ : Cut E) ⟶ Y, E.τ 0 σ.1 σ'.1 = 0 := by
      intro σ'
      have a := σ.2
      have b := σ'.2
      simp only [Category.id_comp] at a b
      rw [E.add 0 _ Y.s, a, E.τ_swap, b, neg_zero, add_zero]
    obtain ⟨s', hs', hu⟩ := E.bij σ.1 (Fin.cons 0 y) (fun i => Fin.cases (Φ.J.S _).zero_mem hy i)
    refine ⟨⟨s', ?_⟩, fun i => by simpa using hs' i.succ, fun σ' h => Subtype.ext (hu σ'.1 fun i => ?_)⟩
    · change E.τ 0 (𝟙 E.D ≫ s') Y.s = 0
      have a := σ.2
      simp only [Category.id_comp] at a ⊢
      rw [E.add 0 _ σ.1, E.τ_swap, hs' 0, a]
      simp
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using h0 σ'
      · simpa using h i

@[simp] theorem frame_shift_domain : (E1 E).D = ⟨E.D, 𝟙 E.D⟩ := rfl

theorem frame_shift_tau (i : Fin d) {Y : Cut E} (σ σ' : (E1 E).D ⟶ Y) : (E1 E).τ i σ σ' = E.τ i.succ σ.1 σ'.1 := rfl

variable {E} (Q : Poly Φ)

def Q1 : Poly (Φ1 E) where
  P Y := ⟨Q.P Y.T, Y.s ≫ Q.j Y.T⟩
  j Y := ⟨Q.j Y.T, E.τ_self 0 _⟩
  X Y := Q.X Y.T
  X_mem Y := Q.X_mem Y.T
  univ {Y Y'} φ x hx := by
    refine ⟨⟨Q.lift φ.1 x hx, ?_⟩, ⟨hom_ext (Q.lift_j φ.1 x hx), Q.lift_X φ.1 x hx⟩, fun ψ h => hom_ext ?_⟩
    · change E.τ 0 ((Y.s ≫ Q.j Y.T) ≫ Q.lift φ.1 x hx) Y'.s = 0
      rw [Category.assoc, Q.lift_j]
      exact φ.2
    · exact (Q.univ φ.1 x hx).unique ⟨congrArg Subtype.val h.1, h.2⟩ ⟨Q.lift_j φ.1 x hx, Q.lift_X φ.1 x hx⟩
  span Y z := Q.span Y.T z

theorem criterion_truncation {a : ℤ → IdF Φ.A} {r : ℤ} (h : Q.Crit a r) : (Q1 Q).Crit (fun r => (a r).res (U E)) r :=
  fun Y b => h Y.T b

theorem ladder_truncation {a b : ℤ → IdF Φ.A} {r : ℤ} (h : Q.Ladder a b r) :
    (Q1 Q).Ladder (fun r => (a r).res (U E)) (fun r => (b r).res (U E)) r :=
  ⟨fun r' Y => h.le r' Y.T, fun r' hr => criterion_truncation Q (h.ca r' hr), fun r' hr => criterion_truncation Q (h.cb r' hr)⟩

theorem isFil_1 {Fil : ℤ → IdF Φ.A} (h : IsFil Φ Fil) : IsFil (Φ1 E) (fun r => (Fil r).res (U E)) :=
  ⟨fun r hr Y => h.top r hr Y.T, fun Y => h.one Y.T, fun hr Y => h.anti hr Y.T, fun r r' Y _ _ hx hy => h.mul r r' Y.T hx hy,
    fun k Y _ hx => h.dp_mem k Y.T hx⟩

theorem grConst_1 {Fil : ℤ → IdF Φ.A} (h : E.GrConst Fil) : (E1 E).GrConst (fun r => (Fil r).res (U E)) :=
  fun q Y σ σ' x hx => h q σ.1 σ'.1 hx

def can (Y : Cut E) : (E1 E).D ⟶ Y := ⟨Y.s, by change E.τ 0 (𝟙 E.D ≫ Y.s) Y.s = 0; rw [Category.id_comp]; exact E.τ_self 0 Y.s⟩

end Cut

namespace Pt

variable {E : Frame Φ d}

def Sσ (σ : ∀ T : C, E.D ⟶ T) : C ⥤ Pt E where
  obj T := ⟨T, σ T⟩
  map f := f

def adjσ (σ : ∀ T : C, E.D ⟶ T) : Sσ σ ⊣ U E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => Equiv.refl _
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

end Pt

namespace Cut

variable {E : Frame Φ (d + 1)} (Q : Poly Φ)

abbrev Pσ (σ : ∀ T : C, E.D ⟶ T) : C ⥤ Cut E := Pt.Sσ σ ⋙ P0 Q

def adjPσ (σ : ∀ T : C, E.D ⟶ T) : Pσ Q σ ⊣ U E := (Pt.adjσ σ).comp (adj Q)

def jσ (σ : ∀ T : C, E.D ⟶ T) : 𝟭 C ⟶ Pσ Q σ ⋙ U E := Functor.whiskerLeft (Pt.Sσ σ) (jNat Q)

end Cut

end CrystallineSemistableComparison.Pb
