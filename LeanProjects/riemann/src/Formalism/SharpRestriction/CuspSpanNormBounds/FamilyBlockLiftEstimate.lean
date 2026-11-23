import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.ParConsts

open MeasureTheory Matrix Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.S.GramWordSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsDiffOpOn {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (U : Set (Fin m → ℂ))
    (R : ((Fin m → ℂ) → E) → (Fin m → ℂ) → E) : Prop :=
  ∃ a : ∀ k : Fin (d + 1), (Fin m → ℂ) → (ContinuousMultilinearMap ℝ (fun _ : Fin k.val => (Fin m → ℂ)) E →L[ℝ] E),
    (∀ k, ContDiffOn ℝ ∞ (a k) U) ∧
    ∀ (φ : (Fin m → ℂ) → E), ∀ x ∈ U, ContDiffAt ℝ d φ x → R φ x = ∑ k : Fin (d + 1), a k x (iteratedFDeriv ℝ k.val φ x)

def IsRadQQd (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  L.IsRadQQ R ∧ ∀ (Y : ℂ) (a b : Fin 2), IsDiffOpOn (2 * L.r + L.k0 + 2) L.BD (R Y a b)

theorem IsRadQQd.rad {L : Lev} {R : ℂ → Matrix (Fin 2) (Fin 2) L.POp} (h : IsRadQQd L R) : L.IsRadQQ R := by
  exact h.1

abbrev GFn {k0 r : ℕ} (L : LocBessel (k0 + 1) r) :=
  Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)

abbrev Sec (k0 : ℕ) := ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

export Formalism.MainNotions.S.UnitaryLevelOperators (levOf headEl cutF)

def lev {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) : Lev :=
  (levOf L μsec).down j (r - j) (by show j + (r - j) = r; omega)

def headAt (k r j : ℕ) (hj : j ≤ r) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * (r - j) + k + 1)) (Fin (2 * (r - j) + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun p q => headEl k j (r - j) h g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def fullPt {r j : ℕ} (hj : j ≤ r) (p : Point ℂ j) : Point ℂ (r + 1) :=
  ⟨p.1 ++ List.replicate (r + 1 - j) ((1 : ℂ), 1), by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact p.2.1 b hb
      · rw [List.eq_of_mem_replicate hb]; exact ⟨one_ne_zero, le_rfl⟩
    · simp [p.2.2]; omega⟩

open Classical in

def orbJ {k r : ℕ} (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  if h : ∃ ν : Measure (PairSp k r), ∃ μR : Measure (Mt k r), IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν then
    OrbInt L F g h.choose else 0

def sliceJ {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) (F : GFn L) (p : Point ℂ j) :
    (lev L μsec j hj).GF :=
  fun g => orbJ L F (fullPt hj p) (headAt (k0 + 1) r j hj (ptMat p) g)

def IsCellOp (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ {g | Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    ∀ F : Lt.GF, SmoothOnH (Hpk (Lt.k0 + 1) Lt.r) F → ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r),
      Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0 → Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def minorsNe (Lt : Lev) (E : List ℕ) : Set (Mat Lt.k0 Lt.r) :=
  {g | ∀ l ∈ E, ∀ hl : l < Lt.r + 2, Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩ ≠ 0}

def CkAt (Lt : Lev) (o : ℕ) (F : Lt.GF) (g₀ : Mat Lt.k0 Lt.r) : Prop :=
  ∃ (U : Set (Mat Lt.k0 Lt.r)) (F' : Lt.GF), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ o F' U ∧
    ∀ g ∈ U, g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) → F g = F' g

theorem CkAt.of_smooth {Lt : Lev} {F : Lt.GF} (h : SmoothOnH (Hpk (Lt.k0 + 1) Lt.r) F) (o : ℕ) {g₀ : Mat Lt.k0 Lt.r}
    (hg : g₀ ∈ UH (Hpk (Lt.k0 + 1) Lt.r)) : CkAt Lt o F g₀ := by
  obtain ⟨U, F', hU, hg0, hF', hEq⟩ := h g₀ hg
  exact ⟨U, F', hU, hg0, contDiffOn_infty.mp hF' o, fun g hgU hgH => hEq g hgU hgH⟩

def IsInvC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ F : Lt.GF, (∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), CkAt Lt o F g) →
      ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), Θ (Lt.act h n h' n' F) g = Lt.act h n h' n' (Θ F) g

theorem IsInvC.isInv {Lt : Lev} {o : ℕ} {Θ : Lt.GF → Lt.GF} (h : IsInvC Lt o Θ) : Lt.IsInv Θ := by
  intro h₀ hh₀ n hn h' hh' n' hn' F hF g hg
  exact h h₀ hh₀ n hn h' hh' n' hn' F (fun g' hg' => CkAt.of_smooth hF o hg') g hg

def BigPosR (Lt : Lev) : Set (Mat Lt.k0 Lt.r) :=
  {g | g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ (∀ l : Fin (Lt.r + 2), Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g l ≠ 0) ∧
    0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g}

def RadZeroC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
    (∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
      ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ g ∈ BigPosR Lt, Lt.act h n h' n' J g = J g) →
    ∀ g ∈ BigPosR Lt, Θ J g = 0

def IsCellOpAt (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, (ws n).length ≤ o) ∧
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ minorsNe Lt E ∩ {g | 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    (∀ n, ∀ w : List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)), ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), ε ≤ Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g →
        (∀ l ∈ E, ∀ hl : l < Lt.r + 2, δ ≤ Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩)) →
        ‖Lt.EwordV w (a n) g‖ ≤ C * (1 + Lev.matNorm g) ^ (dP + 3 * ((Lt.r : ℝ) + 1) * w.length)) ∧
    IsInvC Lt (Finset.univ.sup fun n => (ws n).length) Θ ∧
    ∀ F : Lt.GF, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), g ∈ minorsNe Lt E →
      0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g → CkAt Lt (Finset.univ.sup fun n => (ws n).length) F g →
      Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def RadC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) (R : Lt.POp) : Prop :=
  ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
    (∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
      ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ g ∈ BigPosR Lt, Lt.act h n h' n' J g = J g) →
    ∀ x ∈ Lt.BD, Lt.B (Θ J) x = R (Lt.B J) x

def IsInvL (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
      ∀ g ∈ BigPosR Lt, Θ (Lt.act h n h' n' J) g = Lt.act h n h' n' (Θ J) g

def IsLetters (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (w : Word) (Θ : AuxiliarySlotStates w.length → Lt.GF → Lt.GF) : Prop :=
  ∀ β, IsCellOp Lt j hj (Θ β) ∧ Lt.Rad (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧
    IsCellOpAt Lt [j] (w.length * j) ((w.length * j + w.length * j ^ 2 : ℕ) : ℝ) (Θ β) ∧
    RadC Lt (w.length * j) (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧ IsInvL Lt (w.length * j) (Θ β)

def LettersExist : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : Sec k0), (levOf L μsec).Std →
    ∀ (j : ℕ) (hj : j ≤ r) (w : Word), ∃ Θ : AuxiliarySlotStates w.length → GFn L → GFn L, IsLetters (levOf L μsec) j hj w Θ

def snoc {j : ℕ} (h : Point ℂ j) (t : ℂ) (ht : t ≠ 0) (s : ℕ) (hs : 1 ≤ s) : Point ℂ (j + s) :=
  ⟨h.1 ++ [(t, s)], by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact h.2.1 b hb
      · rw [List.mem_singleton.1 hb]; exact ⟨ht, hs⟩
    · simp [h.2.2]⟩

def pt0 : Point ℂ 0 := ⟨[], by simp⟩

structure GramMap (k0 r : ℕ) extends ValMap (k0 + 1) r where
  top : ∀ (B : LocBessel (k0 + 1) r), Set ℝ → Word → GFn B → List (ℂ × ℕ) → List (ℂ × ℕ) → ℂ
  top_nil : ∀ (B : LocBessel (k0 + 1) r) (I : Set ℝ) (F : GFn B) (p p' : List (ℂ × ℕ)),
    top B I [] F p p' = hsInner (V B F p) (V B F p')

def Slices (Cs : ℝ) : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) (hd : Point ℂ j),
    L.c = cStd → (levOf L μsec).Std →
    (∀ g ∈ UH (Hpk (k0 + 1) (r - j)),
      Gf (k0 + 1) r L.z L.z' (headAt (k0 + 1) r j hj (ptMat hd) g) =
        Complex.normSq (ptMat hd).det * Gf (k0 + 1) (r - j) (lev L μsec j hj).z (lev L μsec j hj).z' g) ∧
    ∀ (h' : (lev L μsec j hj).Haar) (A : ℝ) (mm : ℕ) (F : GFn L), h'.Ok → (levOf L μsec).CC A mm F →
      0 ≤ A / (Cs * ((r : ℝ) + 1) ^ 2) - Cs * (((2 * r + k0 + 2 : ℕ) : ℝ) ^ 2 + ((r : ℝ) + 1) * mm) →
      ∃ Fh : (lev L μsec j hj).GF,
        (lev L μsec j hj).CC (A / (Cs * ((r : ℝ) + 1) ^ 2) -
          Cs * (((2 * r + k0 + 2 : ℕ) : ℝ) ^ 2 + ((r : ℝ) + 1) * mm)) mm Fh ∧
        ((∃ ε : ℝ, 0 < ε ∧ SuppGe (levOf L μsec) ε F) → ∃ ε' : ℝ, 0 < ε' ∧ SuppGe (lev L μsec j hj) ε' Fh) ∧
        ∀ x ∈ (lev L μsec j hj).BD,
          lJ (lev L μsec j hj) h' Fh ((lev L μsec j hj).pt x) = sliceJ L μsec j hj F hd ((lev L μsec j hj).pt x)

structure Dat (D : D7) (k0 : ℕ) where
  hk : k0 + 1 = D.R.k
  B : D.what₂.Tau → LocBessel (k0 + 1) D.R.rS
  μsec : D.what₂.Tau → Sec k0
  l : D.what₂.Tau → Fin (k0 + 1)
  a : D.what₂.Tau → ℝ
  b : D.what₂.Tau → ℝ
  a1 : D.what₂.Tau → ℝ
  b1 : D.what₂.Tau → ℝ
  f : ∀ v, GFn (B v)
  R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (lev (B v) (μsec v) j hj).POp
  Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : Word), AuxiliarySlotStates w.length → GFn (B v) → GFn (B v)

abbrev GWord (D : D7) := D.what₂.Tau → Word

abbrev Head (D : D7) (j : ℕ) := D.what₂.Tau → Point ℂ j

def Len {D : D7} (m : ℕ) (w : GWord D) : Prop := ∀ v, (w v).length ≤ m

def ExtAt {D : D7} (K : ℕ) (A : Set D.what₂.Tau) (w w' : GWord D) : Prop :=
  ∀ v, ∃ l : Word, l.length ≤ K ∧ (v ∉ A → l = []) ∧ w' v = l ++ w v

def ExtPlusAt {D : D7} (K : ℕ) (A : Set D.what₂.Tau) (w w' : GWord D) : Prop :=
  ∀ v, ∃ l : Word, l.length ≤ K ∧ (∀ x ∈ l, x.1 = true) ∧ (v ∉ A → l = []) ∧ w' v = l ++ w v

def dualL (l : Word) : Word := l.map fun x => (false, x.2 + 1)

def ExtDualAt {D : D7} (K : ℕ) (A : Set D.what₂.Tau) (w : GWord D) (q : GWord D × GWord D) : Prop :=
  ∀ v, ∃ l : Word, l.length ≤ K ∧ (∀ x ∈ l, x.1 = true) ∧ (v ∉ A → l = []) ∧
    q.1 v = l ++ w v ∧ q.2 v = dualL l ++ w v

def IsProb {α : Type*} (θ : α →₀ ℝ) : Prop := (∀ x, 0 ≤ θ x) ∧ θ.sum (fun _ c => c) = 1

def NN (D : D7) (Ks : ℕ) : ℕ := 4 * Ks * (D.R.rS + 1)

namespace Dat

variable {D : D7} {k0 : ℕ} (X : Dat D k0)

abbrev lv (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) : Lev := lev (X.B v) (X.μsec v) j hj

def T (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z
def T' (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z'

def I (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a v) (X.b v)
def I1 (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a1 v) (X.b1 v)

def sg (v : D.what₂.Tau) : ℝ := sCut (X.B v).u (X.B v).u' (X.I v)

def loc (v : D.what₂.Tau) : LocalDataRealPlace D where
  lam := fun s => (X.B v).lam (Fin.cast (by have := X.hk; omega) s)
  u := fun i => (X.B v).u (Fin.cast X.hk.symm i)
  u' := fun i => (X.B v).u' (Fin.cast X.hk.symm i)
  l := Fin.cast X.hk (X.l v)
  a := X.a v
  b := X.b v
  a1 := X.a1 v
  b1 := X.b1 v

def xi (C₁ C₂ : ℝ) (Ks i : ℕ) (v : D.what₂.Tau) : ℝ := xSz D C₁ C₂ (NN D Ks) 1 (X.T v) (X.T' v) (X.loc v) i
def abelian₂ (C₁ C₂ : ℝ) (Ks s i : ℕ) (v : D.what₂.Tau) : ℝ := LamSz D C₁ C₂ (NN D Ks) 1 (X.T v) (X.T' v) (X.loc v) i s
def LamP (C₁ C₂ : ℝ) (Ks i : ℕ) (v : D.what₂.Tau) : ℝ := LamPSz D C₁ C₂ (NN D Ks) 1 (X.T v) (X.T' v) (X.loc v) i

def LamG (C₁ C₂ : ℝ) (Ks s i : ℕ) (v : D.what₂.Tau) : ℝ := if s = 1 then X.xi C₁ C₂ Ks i v else X.abelian₂ C₁ C₂ Ks s i v

def admitted (w : GWord D) : Prop := ∀ v, Admissible (X.I v) (w v)

def brk (w : GWord D) : ℝ := ∏ v, brkW (X.B v).lam ((w v).map Prod.snd)

def Fv (χ : ℝ → ℝ) (ε : ℝ) (v : D.what₂.Tau) : GFn (X.B v) := cutF (X.B v).z (X.B v).z' χ ε (X.f v)

def gramLow (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) (w : Word) (F : GFn (X.B v)) (p p' : Point ℂ j) : ℂ :=
  (X.lv v j hj).form ((X.lv v j hj).wmod (X.R v j hj) (X.sg v) (X.B v).u (X.B v).u' w).RR
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p))
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p'))

def energy (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) : ℂ :=
  ∏ v, X.gramLow v 0 (Nat.zero_le _) (w v) (X.Fv χ ε v) pt0 pt0

def jn2 : ℂ := ∏ v, (X.B v).beta (X.μsec v) (X.f v) (X.f v)

def okT (v : D.what₂.Tau) (j0 s : ℕ) (t : ℂ) : Prop :=
  t ≠ 0 ∧ (s = 1 → j0 = D.R.rS → X.T v * X.T' v < Complex.normSq t)

def wt (v : D.what₂.Tau) (j0 s : ℕ) (t : ℂ) : ℝ :=
  Real.sqrt (ptWeightFrom (k0 + 1) D.R.rS (X.T v) (X.T' v) j0 [(t, s)])

def Std (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  4 ≤ Ks ∧ ∀ v,
    (∀ i, (X.B v).ε i = epsSH D.R (Fin.cast (by have := X.hk; omega) i)) ∧ (X.B v).c = cStd ∧
    IsSection (k0 + 1) D.R.rS (X.B v).z (X.B v).z' (X.μsec v) ∧
    IsCutS (X.B v).u (X.B v).u' (X.I v) ∧
    ((X.B v).u (X.l v) ≠ (X.B v).u' (X.l v) ∧
      min (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) + 2 ≤ X.a v ∧ X.a v ≤ X.b v ∧
      X.b v ≤ max (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) - 2) ∧
    (∃ ρ : Fin k0 → ℝ, Interlace (X.B v).u ρ ∧ Interlace (X.B v).u' ρ) ∧
    X.I1 v ⊆ X.I v ∧ X.a1 v ≤ X.b1 v ∧ ((NN D Ks : ℕ) : ℝ) ^ 3 / 2 ≤ X.b1 v - X.a1 v ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u (X.B v).lam ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u' (X.B v).lam ∧
    C₀ * ((D.R.k : ℝ) * (NN D Ks : ℕ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((NN D Ks : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 +
      ((NN D Ks : ℕ) : ℝ) ^ 3) ≤ X.b v - X.a v ∧
    GapAtLeast (X.B v).ε (X.B v).lam
      (Cg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (((NN D Ks : ℕ) : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) ∧
    UnitaryLevelOperators.IsKFinCoefT (X.B v).σ (X.f v) ∧
    (∀ (j : ℕ) (hj : j ≤ D.R.rS), IsRadQQd (X.lv v j hj) (X.R v j hj)) ∧
    ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), IsLetters (levOf (X.B v) (X.μsec v)) j hj w (X.Th v j hj w)

end Dat

section Weights

variable {D : D7} {k0 : ℕ} (Gm : GramMap k0 D.R.rS) (X : Dat D k0)

def gram (v : D.what₂.Tau) (j : ℕ) (w : Word) (F : GFn (X.B v)) (p p' : Point ℂ j) : ℂ :=
  if hj : j ≤ D.R.rS then X.gramLow v j hj w F p p' else Gm.top (X.B v) (X.I v) w F p.1 p'.1

open Classical in

def gramS (v : D.what₂.Tau) (j0 s : ℕ) (w : Word) (F : GFn (X.B v)) (h h' : Point ℂ j0) (t t' : ℂ) : ℂ :=
  if H : 1 ≤ s ∧ X.okT v j0 s t ∧ X.okT v j0 s t' then
    gram Gm X v (j0 + s) w F (snoc h t H.2.1.1 s H.1) (snoc h' t' H.2.2.1 s H.1) else 0

def N0 (j0 : ℕ) (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → Head D j0)
    (κ : Hd → Hd → ℂ) : ℂ :=
  (∑ h, ∑ h', κ h h' * ∏ v, gram Gm X v j0 (w v) (X.Fv χ ε v) (hd h v) (hd h' v)) / (X.brk w : ℂ)

def Ns (j0 s : ℕ) (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → Head D j0)
    (κ : Hd → Hd → ℂ) (t t' : D.what₂.Tau → ℂ) : ℂ :=
  ((∏ v, X.wt v j0 s (t v) * X.wt v j0 s (t' v) : ℝ) : ℂ) *
    (∑ h, ∑ h', κ h h' * ∏ v, gramS Gm X v j0 s (w v) (X.Fv χ ε v) (hd h v) (hd h' v) (t v) (t' v)) /
      (X.brk w : ℂ)

def Ntr (j0 : ℕ) (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → Head D j0)
    (κ : Hd → Hd → ℂ) (σ : D.what₂.Tau → ℂ) : ℂ :=
  ∫ t : D.what₂.Tau → ℂ, Ns Gm X j0 1 w χ ε hd κ t t * ∏ v, fsC (σ v) (t v)

def blockLiftThreshold (C₁ C₂ : ℝ) (Ks j0 s : ℕ) (v : D.what₂.Tau) : ℝ :=
  if j0 + s ≤ D.R.rS then X.abelian₂ C₁ C₂ Ks (s + 1) (j0 + 1) v else 2 * X.LamP C₁ C₂ Ks (j0 + 1) v

def oDiff (t t' : D.what₂.Tau → ℂ) : D.what₂.Tau → ℂ := fun v => (t v)⁻¹ - (t' v)⁻¹

def PatOK (C₁ C₂ : ℝ) (Ks j0 s : ℕ) (p : D.what₂.Tau → Option Bool) (t t' : D.what₂.Tau → ℂ) : Prop :=
  (∀ v, (p v).isSome ↔ blockLiftThreshold X C₁ C₂ Ks j0 s v < ‖oDiff t t' v‖) ∧
    (j0 + s ≤ D.R.rS → ∀ v, p v ≠ some false) ∧
    (∀ v, p v = some true → j0 + s = D.R.rS + 1 → ‖oDiff t t' v‖ / 2 ≤ ‖t v‖⁻¹) ∧
    (∀ v, p v = some false → ‖oDiff t t' v‖ / 2 ≤ ‖t' v‖⁻¹)

def ChargedPairs (Ks j0 s : ℕ) (w : GWord D) (p : D.what₂.Tau → Option Bool) (q : GWord D × GWord D) : Prop :=
  if j0 + s ≤ D.R.rS then ExtDualAt Ks {v | (p v).isSome} w q
  else ExtPlusAt Ks {v | p v = some true} w q.1 ∧ ExtPlusAt Ks {v | p v = some false} w q.2

end Weights

section Lattices

variable (D : D7)

def IsLat (La : AddSubgroup (D.what₂.Tau → ℂ)) (κ : ℝ) : Prop :=
  0 < κ ∧ DiscreteTopology La ∧
    ∃ U : Set (D.what₂.Tau → ℂ), IsAddFundamentalDomain La U volume ∧ volume U = ENNReal.ofReal κ

def dualS (La : AddSubgroup (D.what₂.Tau → ℂ)) : Set (D.what₂.Tau → ℂ) :=
  {σ | ∀ t ∈ La, ∏ v, fsC (σ v) (t v) = 1}

def scId (a : D.what₂.Tau → ℂ) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set (D.what₂.Tau → ℂ) :=
  {σ | ∃ x ∈ aa, ∀ v, σ v = a v * plEmb D v x}

def scNorm (a : D.what₂.Tau → ℂ) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℝ :=
  ((FractionalIdeal.absNorm aa : ℚ) : ℝ) * ∏ v, ‖a v‖ ^ 2

end Lattices

section Estimates

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

def E (k0 : ℕ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ w : GWord D, X.admitted w → Len (NN D Ks) w →
    Tendsto (fun ε => X.energy w χ ε) (𝓝[>] 0) (𝓝 ((X.brk w : ℂ) * X.jn2))

def SingleLevelGramEstimate (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ j0 : ℕ, j0 ≤ D.R.rS → ∀ w : GWord D, X.admitted w → Len (NN D Ks - Ks) w →
    (∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      ∀ (Hd : Type) [Fintype Hd] (hd : Hd → Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        (∃ φ : (D.what₂.Tau → ℂ) → ℂ, Continuous φ ∧
          (∀ t, (∀ v, t v ≠ 0) → φ t = Ns Gm X j0 1 w χ ε hd κ t t) ∧
          ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * ∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ))) ∧
        Ntr Gm X j0 w χ ε hd κ 0 = N0 Gm X j0 w χ ε hd κ) ∧
    ∃ θ : Set D.what₂.Tau → (GWord D →₀ ℝ),
      (∀ A, IsProb (θ A) ∧ ∀ w' ∈ (θ A).support, ExtAt Ks A w w' ∧ X.admitted w') ∧
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        ∀ σ : D.what₂.Tau → ℂ,
          ‖Ntr Gm X j0 w χ ε hd κ σ‖ ≤
            (∏ v, minFac (X.xi C₁ C₂ Ks (j0 + 1) v) ‖σ v‖ Ks) *
              (θ {v | X.xi C₁ C₂ Ks (j0 + 1) v < ‖σ v‖}).sum
                (fun w' c => c * (N0 Gm X j0 w' χ ε hd κ).re)

def BlockLiftEstimate (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ j0 s : ℕ, 1 ≤ s → (j0 + s ≤ D.R.rS ∨ (2 ≤ s ∧ j0 + s = D.R.rS + 1)) →
    ∀ w : GWord D, X.admitted w → Len (NN D Ks - Ks) w →
    ∃ θ : (D.what₂.Tau → Option Bool) → (GWord D × GWord D →₀ ℝ),
      (∀ p, IsProb (θ p) ∧ ∀ q ∈ (θ p).support, ChargedPairs Ks j0 s w p q ∧ X.admitted q.1 ∧ X.admitted q.2) ∧
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → Head D j0)
          (K : Hd × (D.what₂.Tau → ℂ) → Hd × (D.what₂.Tau → ℂ) → ℂ),
          PSDK K → ∀ t t' : D.what₂.Tau → ℂ, (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) →
            ∃ p, PatOK X C₁ C₂ Ks j0 s p t t' ∧
              ‖Ns Gm X j0 s w χ ε hd (fun h h' => K (h, t) (h', t')) t t'‖ ≤
                (∏ v, minFac (blockLiftThreshold X C₁ C₂ Ks j0 s v) ‖oDiff t t' v‖ Ks) *
                  (θ p).sum (fun q c => c *
                    (((Ns Gm X j0 s q.1 χ ε hd (fun h h' => K (h, t) (h', t)) t t).re +
                      (Ns Gm X j0 s q.2 χ ε hd (fun h h' => K (h, t') (h', t')) t' t').re) / 2))

def LargeBlockLiftEstimate (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ j0 s : ℕ, 2 ≤ s → j0 + s ≤ D.R.rS + 1 →
    ∀ w : GWord D, X.admitted w → Len (NN D Ks - (s + 1) * Ks) w →
    ∀ (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (a : D.what₂.Tau → ℂ), (∀ v, a v ≠ 0) →
    (∏ v, X.abelian₂ C₁ C₂ Ks s (j0 + 1) v) ≤ Real.sqrt (scNorm D a aa) →
    ∃ θ : GWord D →₀ ℝ, IsProb θ ∧ (∀ w' ∈ θ.support, ExtAt ((s + 1) * Ks) Set.univ w w' ∧ X.admitted w') ∧
      ∀ (La : AddSubgroup (D.what₂.Tau → ℂ)) (κL : ℝ), IsLat D La κL → dualS D La ⊆ scId D a aa →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        ∀ t₀ : D.what₂.Tau → ℂ, ∃ sv : ℝ,
          HasSum (fun z : La => Ns Gm X j0 s w χ ε hd κ (t₀ + z) (t₀ + z)) (sv : ℂ) ∧
          κL * sv ≤ C₃ ^ (D.R.f * s) *
            (∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG C₁ C₂ Ks s' (j0 + 1) v ^ 2) *
            θ.sum (fun w' c => c * (N0 Gm X j0 w' χ ε hd κ).re)

end Estimates

def LowPos (D : D7) (k0 : ℕ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), Admissible (X.I v) w →
    w.length ≤ NN D Ks → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      PSDK (fun p p' : Point ℂ j => X.gramLow v j hj w (X.Fv χ ε v) p p')

section TopLevel

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

def TopPos (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ (v : D.what₂.Tau) (w : Word), Admissible (X.I v) w →
    w.length ≤ NN D Ks → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      PSDK (fun p p' : List (ℂ × ℕ) => Gm.top (X.B v) (X.I v) w (X.Fv χ ε v) p p')

def TopWave (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ (v : D.what₂.Tau) (w : Word), Admissible (X.I v) w →
    w.length ≤ NN D Ks → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε → ∀ h h' : Point ℂ D.R.rS,
      ∃ φt : ℂ → ℂ, Continuous φt ∧ Integrable φt ∧
        (∀ ζ : ℂ, X.T v * X.T' v < Complex.normSq ζ →
          φt ζ = ((X.wt v D.R.rS 1 ζ ^ 2 : ℝ) : ℂ) *
            Gm.top (X.B v) (X.I v) w (X.Fv χ ε v) (h.1 ++ [(ζ, 1)]) (h'.1 ++ [(ζ, 1)])) ∧
        (∀ ζ : ℂ, Complex.normSq ζ ≤ X.T v * X.T' v → φt ζ = 0) ∧
        ∀ s : ℂ, ∫ ζ, fsC s ζ * φt ζ =
          (X.lv v D.R.rS le_rfl).form
            ((X.lv v D.R.rS le_rfl).wmod (X.R v D.R.rS le_rfl) (X.sg v) (X.B v).u (X.B v).u' w).RR
            (omApply (Vop s w) (fun β => (X.lv v D.R.rS le_rfl).B
              (sliceJ (X.B v) (X.μsec v) D.R.rS le_rfl (X.Th v D.R.rS le_rfl w β (X.Fv χ ε v)) h)))
            (fun β => (X.lv v D.R.rS le_rfl).B
              (sliceJ (X.B v) (X.μsec v) D.R.rS le_rfl (X.Th v D.R.rS le_rfl w β (X.Fv χ ε v)) h'))

end TopLevel

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : ∀ k0 r : ℕ, GramMap k0 r)

def EF (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, E (Fm.D x i) k0 Ks C₀ Cg

def FamilyGramEstimate (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, SingleLevelGramEstimate (Fm.D x i) (Gm k0 (Fm.D x i).R.rS) Ks C₀ Cg C₁ C₂

def FamilyBlockLiftEstimate (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, BlockLiftEstimate (Fm.D x i) (Gm k0 (Fm.D x i).R.rS) Ks C₀ Cg C₁ C₂

def FamilyLiftBlockBound (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, LargeBlockLiftEstimate (Fm.D x i) (Gm k0 (Fm.D x i).R.rS) Ks C₀ Cg C₁ C₂ C₃

def LowPosF (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, LowPos (Fm.D x i) k0 Ks C₀ Cg

def TopPosF (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, TopPos (Fm.D x i) (Gm k0 (Fm.D x i).R.rS) Ks C₀ Cg

def TopWaveF (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ∀ k0 : ℕ, TopWave (Fm.D x i) (Gm k0 (Fm.D x i).R.rS) Ks C₀ Cg

end Family

end Formalism.MainNotions.S.GramWordSpace

end
