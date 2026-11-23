import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.LocalToGlobal.LatticeGeometry.ExtPtHt
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.SharpRestriction.Divisibility.ProductFirstParts

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtThmB (U : ShimU D G jC ng w) where

  hFl : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ →ₗ[ℝ] ℝ
  hFl_homog : ∀ (P : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ) (d : ℕ),
    d ≠ Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1 → P.IsHomogeneous d → hFl P = 0

  PBs : ℝ → MvPolynomial (DV.Rt D.what₂.Tau w.N ⊕ Unit) ℝ

  PBsC : ℝ → U.Comp → MvPolynomial (DV.Rt D.what₂.Tau w.N ⊕ Unit) ℝ

  v0 : D.what₂.Tau → Fin w.N → ℝ

def extThmBJunk (U : ShimU D G jC ng w) : ExtThmB U where
  hFl := 0
  hFl_homog := fun _ _ _ _ => rfl
  PBs := fun _ => 0
  PBsC := fun _ _ => 0
  v0 := fun _ _ => 0

section Defs

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

abbrev YU : DV.ShimX D.what₂.Tau := toShimX U h lev hlev

abbrev Wts (w : Dat D Lev) : Type := D.what₂.Tau → Fin w.N → ℝ

def CompGapsGe (lam : Wts w) (c0 : ℝ) : Prop :=
  ∀ τ (a : ℕ) (ha : a + 1 < w.N), a + 1 ≠ w.j →
    c0 ≤ lam τ ⟨a, by omega⟩ - lam τ ⟨a + 1, ha⟩

def RatW (lam : Wts w) : Prop := ∀ τ i, ∃ q : ℚ, lam τ i = q

variable {U}

def lamPP (E : ExtThmB U) (lam : Wts w) (s : ℚ) : Wts w := fun τ i => lam τ i - (s : ℝ) * E.v0 τ i

def pbs (E : ExtThmB U) (B : ℝ) (lam : Wts w) (s : ℝ) : ℝ :=
  eval (Sum.elim (fun x : DV.Rt D.what₂.Tau w.N => lam x.1 x.2) (fun _ => s)) (E.PBs B)

def pbsC (E : ExtThmB U) (B : ℝ) (c : U.Comp) (lam : Wts w) (s : ℝ) : ℝ :=
  eval (Sum.elim (fun x : DV.Rt D.what₂.Tau w.N => lam x.1 x.2) (fun _ => s)) (E.PBsC B c)

def flagDegW (lam : Wts w) : ℝ := by
  classical
  exact Formalism.DegreeFormula.flagDeg D.what₂.Tau w.N lam

def hFlPoly (E : ExtThmB U) (lam : Wts w) : ℝ :=
  E.hFl (Formalism.DegreeFormula.linRoot lam ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1))

def swapW (lam : Wts w) (τ : D.what₂.Tau) (a : ℕ) (ha : a + 1 < w.N) : Wts w := by
  classical
  exact fun τ' i => if τ' = τ then lam τ (Equiv.swap (⟨a, by omega⟩ : Fin w.N) ⟨a + 1, ha⟩ i) else lam τ' i

end Defs

section Reformulated

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

def ThmBI1 (E : ExtThmB U) : Prop :=
  ∃ C2 : ℝ, ∀ B : ℝ, 2 ≤ B →
    (∃ Q : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ, Q.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1) ∧
      (∀ lam : Wts w, Tendsto (fun R => product_first_partition.PBR (YU U h lev hlev) B R lam) atTop
        (𝓝 (eval (fun x => lam x.1 x.2) Q))) ∧
      ∀ m, |Q.coeff m| ≤ C2 * Real.log B) ∧
    (∀ lam : Wts w, pbs E B lam 0 = product_first_partition.PB (YU U h lev hlev) B lam) ∧
    (∀ m, |(E.PBs B).coeff m| ≤ C2 * Real.log B) ∧
    (∑ c, E.PBsC B c) = E.PBs B ∧ ∀ c m, |(E.PBsC B c).coeff m| ≤ C2 * Real.log B

def ThmBI2 (E : ExtThmB U) : Prop :=
  ∀ c0 Λ : ℝ, 0 < c0 → ∃ s0 : ℝ, 0 < s0 ∧ ∃ C3 : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ (lam : Wts w) (s : ℚ), RatW lam →
    WeightThresholdDefs.supAbs (YU U h lev hlev) lam ≤ Λ → 0 < s → (s : ℝ) ≤ s0 →
    WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) → CompGapsGe (lamPP E lam s) c0 →
    ∀ c, |U.alg.arSelfC (U.alg.Mbar B lam s) c - pbsC E B c (lamPP E lam s) s| ≤ C3 * s

def ThmBI3 (E : ExtThmB U) : Prop :=
  ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 2 ≤ B → RatW lam → 0 < s → WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs (YU U h lev hlev) (lamPP E lam s) ≤
      (B - 2) * WeightThresholdDefs.gap (YU U h lev hlev) (lamPP E lam s) τ) →
    (YU U h lev hlev).semipos ((YU U h lev hlev).Mbar B lam s) ∧
      (YU U h lev hlev).nefFib ((YU U h lev hlev).Mbar B lam s)

def ThmBI3R (E : ExtThmB U) : Prop :=
  ∀ Λ : ℝ, ∃ s0 : ℝ, 0 < s0 ∧ ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 2 ≤ B → RatW lam →
    WeightThresholdDefs.supAbs (YU U h lev hlev) lam ≤ Λ → 0 < s → (s : ℝ) ≤ s0 →
    WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs (YU U h lev hlev) (lamPP E lam s) ≤
      (B - 2) * WeightThresholdDefs.gap (YU U h lev hlev) (lamPP E lam s) τ) →
    (YU U h lev hlev).semipos ((YU U h lev hlev).Mbar B lam s) ∧
      (YU U h lev hlev).nefFib ((YU U h lev hlev).Mbar B lam s)

theorem thmBI3R_of (E : ExtThmB U) (h3 : ThmBI3 U h lev hlev E) : ThmBI3R U h lev hlev E :=
  fun _ => ⟨1, one_pos, fun B lam s hB hr _ hs _ hd hg => h3 B lam s hB hr hs hd hg⟩

def ThmBI5 (P : ExtPtHt U) : Prop :=
  ∀ c0 : ℝ, 0 < c0 → ∃ t0 : ℝ, 0 < t0 ∧ ∃ C4 : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ lam : Wts w, RatW lam →
    WeightThresholdDefs.supAbs (YU U h lev hlev) lam ≤ 1 → ∀ t : ℚ, 0 < t → (t : ℝ) ≤ t0 →
    (∀ τ, (t : ℝ) ≤ WeightThresholdDefs.gap (YU U h lev hlev) lam τ) → CompGapsGe lam c0 →
    ∀ c y, -C4 * Real.log (B / ((t : ℝ) ^ 2)) ≤ P.ht c (U.alg.Mbar B lam (t ^ 2) c) y

def ThmBI6 (P : ExtPtHt U) : Prop :=
  ∀ c0 : ℝ, 0 < c0 → ∃ t0 : ℝ, 0 < t0 ∧ ∃ C5 : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ lam : Wts w, RatW lam →
    WeightThresholdDefs.supAbs (YU U h lev hlev) lam ≤ 1 → ∀ t : ℚ, 0 < t → (t : ℝ) ≤ t0 →
    (∀ τ, (t : ℝ) ≤ WeightThresholdDefs.gap (YU U h lev hlev) lam τ) → CompGapsGe lam c0 →
    ∀ c, ∃ S : Set (P.Pt c), P.dense c S ∧ ∀ y ∈ S, P.ht c (U.alg.Mbar B lam (t ^ 2) c) y ≤ C5 * Real.log B

def ThmBI7 : Prop :=
  ∀ (c : U.Comp) (lam : D.what₂.Tau → Fin w.N → ℤ), (∀ τ (a b : Fin w.N), a ≤ b → lam τ b ≤ lam τ a) →
    G.nef (U.alg.Yv c) (U.alg.Lw c lam)

def ThmBStep2 (E : ExtThmB U) : Prop :=
  (∀ c (γ : U.cx.Γ c), IsOfFinOrder γ → γ = 1) →
  ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 0 < s → WeightThresholdDefs.Dominant (YU U h lev hlev) lam →
    WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ c, 0 ≤ U.alg.degA c (U.alg.Mbar B lam s c)) ∧
      ∑ c, U.alg.degA c (U.alg.Mbar B lam s c) ≤ WeightThresholdDefs.geoDeg (YU U h lev hlev) lam

def ThmBAmple (E : ExtThmB U) (P : ExtPtHt U) : Prop :=
  ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 0 < s → WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs (YU U h lev hlev) (lamPP E lam s) ≤
      (B - 2) * WeightThresholdDefs.gap (YU U h lev hlev) (lamPP E lam s) τ) →
    ∀ c, P.ampleG c (U.alg.Mbar B lam s c)

def ThmBI8 (E : ExtThmB U) : Prop :=
  ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) (a : ℕ) (ha : a + 1 < w.N), a + 1 ≠ w.j → ∀ lam : Wts w,
    product_first_partition.PB (YU U h lev hlev) B (swapW lam τ a ha) - U.cx.vol * hFlPoly E (swapW lam τ a ha) =
      -(product_first_partition.PB (YU U h lev hlev) B lam - U.cx.vol * hFlPoly E lam)

def ThmBI9 (E : ExtThmB U) : Prop :=
  (∀ lam : Wts w, WeightThresholdDefs.Dominant (YU U h lev hlev) lam → (∃ τ, WeightThresholdDefs.gap (YU U h lev hlev) lam τ = 0) →
    hFlPoly E lam = 0) ∧
  ∀ lam : Wts w, WeightThresholdDefs.Dominant (YU U h lev hlev) lam → 0 ≤ hFlPoly E lam

def ThmBGeoLim : Prop :=
  (∀ c (γ : U.cx.Γ c), IsOfFinOrder γ → γ = 1) → ∀ (B : ℝ) (uq : D.what₂.Tau → Fin w.N → ℚ), ∀ c : U.Comp,
    Tendsto (fun s : ℚ => U.alg.degA c (U.alg.Mbar B (product_first_partition.castW (YU U h lev hlev) uq) s c)) (𝓝[>] 0)
      (𝓝 (U.cx.volC c * flagDegW (product_first_partition.castW (YU U h lev hlev) uq)))

end Reformulated

section Targets

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

def ThmBDecomp (E : ExtThmB U) : Prop :=
  ∃ CB : ℝ, ∃ B1 : ℕ, ∀ B : ℕ, B1 ≤ B → ∃ al be : D.what₂.Tau → ℝ,
    ∃ EB : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ, (∀ m, |EB.coeff m| ≤ CB * Real.log B / B) ∧
      ∀ lam : Wts w, product_first_partition.PB (YU U h lev hlev) B lam =
        U.cx.vol * (hFlPoly E lam + ((Formalism.DegreeFormula.dimFl D.what₂.Tau w.N : ℝ) + 1) *
          flagDegW lam *
          ∑ τ, (al τ * ∑ i : Fin w.N, (if (i : ℕ) < w.j then lam τ i else 0) +
            be τ * ∑ i : Fin w.N, (if (i : ℕ) < w.j then 0 else lam τ i))) +
        eval (fun x => lam x.1 x.2) EB

def ThmBTarget0 : Prop :=
  ∀ B : ℝ, ∃ Q : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ, ∀ lam : Wts w,
    Tendsto (fun R => product_first_partition.PBR (YU U h lev hlev) B R lam) atTop (𝓝 (eval (fun x => lam x.1 x.2) Q))

def ThmBTarget1m : Prop :=
  ∀ (uq : D.what₂.Tau → Fin w.N → ℚ) (g : ℝ),
    WeightThresholdDefs.WeightHyp (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g →
    ((product_first_partition.badPr (YU U h lev hlev)).card : ℝ) ≤
      WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g →
    Tendsto (fun s : ℚ => (YU U h lev hlev).arSelf ((YU U h lev hlev).Mbar
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq) s))
      (𝓝[>] 0) (𝓝 (product_first_partition.PB (YU U h lev hlev)
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq))) ∧
    ∀ᶠ s : ℚ in 𝓝[>] 0,
      (YU U h lev hlev).semipos ((YU U h lev hlev).Mbar
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq) s) ∧
      (YU U h lev hlev).nefFib ((YU U h lev hlev).Mbar
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq) s)

def ThmBTarget2 : Prop :=
  ∀ (uq : D.what₂.Tau → Fin w.N → ℚ) (g : ℝ),
    WeightThresholdDefs.WeightHyp (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g →
    ((product_first_partition.badPr (YU U h lev hlev)).card : ℝ) ≤
      WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g →
    (∀ c, ∃ l : ℝ, Tendsto (product_first_partition.slFun (YU U h lev hlev)
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq) c)
        (𝓝[>] 0) (𝓝 l)) ∧
    product_first_partition.PB (YU U h lev hlev) (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g)
                        (product_first_partition.castW (YU U h lev hlev) uq) /
      (((WeightThresholdDefs.dimY (YU U h lev hlev) : ℝ) + 1) *
        WeightThresholdDefs.geoDeg (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq)) =
    (∑ c, limUnder (𝓝[>] (0 : ℚ)) (product_first_partition.slFun (YU U h lev hlev)
        (WeightThresholdDefs.bigB0 (YU U h lev hlev) (product_first_partition.castW (YU U h lev hlev) uq) g) (product_first_partition.castW (YU U h lev hlev) uq) c)) /
      (Fintype.card U.Comp : ℝ)

end Targets

end Formalism.L2.Geo
