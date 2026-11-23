import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.WholeFlag

namespace GlobalTheory.ConstLat

section Linear

variable {K : Type} [Field K] (w : AbsoluteValue K ℝ)

def supN {n : ℕ} (x : Fin n → K) : ℝ := ⨆ i, w (x i)

theorem le_supN {n : ℕ} (x : Fin n → K) (i : Fin n) : w (x i) ≤ supN w x :=
  le_ciSup (f := fun i => w (x i)) (Set.finite_range _).bddAbove i

theorem supN_nonneg {n : ℕ} (x : Fin n → K) : 0 ≤ supN w x :=
  Real.iSup_nonneg fun i => w.nonneg (x i)

theorem supN_le {n : ℕ} {x : Fin n → K} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, w (x i) ≤ r) : supN w x ≤ r :=
  Real.iSup_le h hr

def colMinor {n g : ℕ} (H : Matrix (Fin n) (Fin g) K) (S : Finset (Fin g)) : ℝ :=
  ⨆ σ : S → Fin n, w (H.submatrix σ Subtype.val).det

theorem colMinor_empty {n g : ℕ} (H : Matrix (Fin n) (Fin g) K) : colMinor w H ∅ = 1 := by
  unfold colMinor
  simp

open Classical in

def blkLe {ι : Type} {g : ℕ} (β : Fin g → ι) (i : Fin g) : Finset (Fin g) :=
  Finset.univ.filter fun l => l ≤ i ∧ β l = β i

open Classical in

def blkLt {ι : Type} {g : ℕ} (β : Fin g → ι) (i : Fin g) : Finset (Fin g) :=
  Finset.univ.filter fun l => l < i ∧ β l = β i

end Linear

def compl {R : Type} [CommRing R] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R) (L : Matrix (Fin g) (Fin (g + g)) R)
    (Ji : Matrix (Fin (g + g)) (Fin (g + g)) R) : Matrix (Fin (g + g)) (Fin (g + g)) R :=
  Matrix.of fun i k => Fin.addCases (motive := fun _ => R) (fun l => U i l) (fun l => (Ji * L.transpose) i l.rev) k

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isNonarchimedean_w {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) : IsNonarchimedean e.w := by
  have key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b := by
    intro a b hab
    by_cases h0 : b = 0
    · subst h0
      simpa using hab
    have hb0 : 0 < e.w b := e.w.pos h0
    have h1 : a / b ∈ e.O := (e.mem_O _).2 (by rw [map_div₀]; exact (div_le_one hb0).2 hab)
    have h2 : a / b + 1 ∈ e.O := add_mem h1 e.O.one_mem
    have h3 : a + b = (a / b + 1) * b := by field_simp
    rw [h3, map_mul]
    exact (mul_le_mul_of_nonneg_right ((e.mem_O _).1 h2) (e.w.nonneg _)).trans_eq (one_mul _)
  intro a b
  rcases le_total (e.w a) (e.w b) with h | h
  · exact (key a b h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (key b a h).trans (le_max_left _ _)

def AtTest (V : Cover Y) (W : Y.X.Opens) (p : ℕ)
    (Q : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v), AlgPt Y → (Sp (AlgebraicClosure F) ⟶ V.G) → (Sp e.O ⟶ V.X) → Prop) :
    Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
    ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      Q v e y z yt

variable {C : CxSt F} {g : ℕ}

def LineBase (V : Cover Y) (d : Y.X → Fin g → Y.Fnˣ) (A : Fin g → Adl C Y) (p : ℕ) : Prop :=
  (∀ i y, UnitAt y (genAt (A i).D y * d y i)) ∧
    ∃ (L : Fin g → LB V.X) (m : ℕ), 0 < m ∧ ∀ i, (L i).IsLB ∧
      NormsAt V (L i) p ⊤ (fun y => genAt (A i).D y ^ m) fun v e y => m * (A i).lg v e y

def ChartReg (V : Cover Y) (U : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) : Prop :=
  ∀ z : V.G, V.j z ∈ U → ∀ k l, RegAt z ((H * ((T (V.π z)).map V.φ)⁻¹) k l)

def MinorNorm (V : Cover Y) (W : Y.X.Opens) (U : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (A : Fin g → Adl C Y) (p : ℕ) : Prop :=
  AtTest V W p fun v e y z yt => ⊤ ≤ yt ⁻¹ᵁ U → 0 < colMinor e.w (valMat V H (T (below y.1)) z) Finset.univ ∧
    ∀ i, (A i).lg v e y = Real.log (e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i))) +
      Real.log (colMinor e.w (valMat V H (T (below y.1)) z) (Finset.Iic i)) -
        Real.log (colMinor e.w (valMat V H (T (below y.1)) z) (Finset.Iio i))

def BlockNorm {ι : Type} (V : Cover Y) (W : Y.X.Opens) (U : V.X.Opens)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (A : Fin g → Adl C Y) (β : Fin g → ι) (sh : ι → ℝ) (p : ℕ) : Prop :=
  AtTest V W p fun v e y z yt => ⊤ ≤ yt ⁻¹ᵁ U →
    ∀ i, (A i).lg v e y = Real.log (e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i))) +
      Real.log (colMinor e.w (valMat V H (T (below y.1)) z) (blkLe β i)) -
        Real.log (colMinor e.w (valMat V H (T (below y.1)) z) (blkLt β i)) +
          sh (β i) * Real.log (e.w (p : AlgebraicClosure F))

def IsoAgree (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens)
    (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (p k : ℕ) : Prop :=
  AtTest V W p fun _ e y z yt => ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    (∀ u u' : Fin g → AlgebraicClosure F, supN e.w ((valMat V (H a) (T (below y.1)) z).mulVec u) ≤ 1 →
      supN e.w ((valMat V (H a) (T (below y.1)) z).mulVec u') ≤ 1 →
      e.w (dotProduct ((valMat V (H a) (T (below y.1)) z).mulVec u)
        ((J.map (Int.castRingHom (AlgebraicClosure F))).mulVec ((valMat V (H a) (T (below y.1)) z).mulVec u'))) ≤
        e.w (p : AlgebraicClosure F) ^ k) ∧
    ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin g → AlgebraicClosure F,
      supN e.w ((valMat V (H a) (T (below y.1)) z).mulVec u) ≤ 1 →
      supN e.w ((valMat V (H b) (T (below y.1)) z).mulVec u - (valMat V (H a) (T (below y.1)) z).mulVec u) ≤
        e.w (p : AlgebraicClosure F) ^ k

def EqData {E : Type} [Field E] [NumberField E] (A A' : Fin g → Adl C Y) (β : Fin g → (E →+* F)) (sh : (E →+* F) → ℝ)
    (ρ : 𝓞 E →+* Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (p k : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn), genericPoint Y.X ∈ W ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) ∧
    LineBase V d A p ∧ LineBase V d A' p ∧
    (∀ a, ChartReg V (U a) (H a) T ∧ MinorNorm V W (U a) (H a) d T A p ∧ BlockNorm V W (U a) (H a) d T A' β sh p) ∧
    IsoAgree V W U H T J p k ∧
    AtTest V W p fun _ e y z yt => ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → ∀ (α : 𝓞 E) (u : Fin g → AlgebraicClosure F),
      supN e.w ((valMat V (H a) (T (below y.1)) z).mulVec u) ≤ 1 →
      supN e.w (((ρ α).map (Int.castRingHom (AlgebraicClosure F))).mulVec ((valMat V (H a) (T (below y.1)) z).mulVec u) -
        (valMat V (H a) (T (below y.1)) z).mulVec fun l => algebraMap F (AlgebraicClosure F) (β l (α : E)) * u l) ≤
        e.w (p : AlgebraicClosure F) ^ k

def SecondLat {N : ℕ} (J : Matrix (Fin N) (Fin N) ℤ) (p n : ℕ) (P Q : Matrix (Fin N) (Fin N) F) : Prop :=
  P * Q = 1 ∧ (∀ i j, IsIntegral ℤ ((n : F) * P i j) ∧ IsIntegral ℤ ((n : F) * Q i j)) ∧
    ∃ s : ℕ, s.Coprime p ∧ ∀ i j, IsIntegral ℤ ((s : F) * (Q.transpose * J.map (Int.castRingHom F) * Q) i j) ∧
      IsIntegral ℤ ((s : F) * (P * (J.map (Int.castRingHom F))⁻¹ * P.transpose) i j)

def EigBasis {E : Type} [Field E] [NumberField E] {N : ℕ} (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ)
    (J : Matrix (Fin N) (Fin N) ℤ) (sh : (E →+* F) → ℝ) (p n : ℕ) (P Q : Matrix (Fin N) (Fin N) F) : Prop :=
  SecondLat J p n P Q ∧ ∃ (b : Fin N → (E →+* F)) (α : 𝓞 E),
    P * (ρ α).map (Int.castRingHom F) * Q = Matrix.diagonal (fun r => b r (α : E)) ∧
    (∀ σ τ : E →+* F, σ ≠ τ → σ (α : E) ≠ τ (α : E) ∧ IsIntegral ℤ ((n : F) / (σ (α : E) - τ (α : E)))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : Ext v) (τ : E →+* F) (y : Fin N → AlgebraicClosure F),
      (∀ r, b r ≠ τ → y r = 0) →
        supN e.w y = e.w (p : AlgebraicClosure F) ^ sh τ * supN e.w ((Q.map (algebraMap F (AlgebraicClosure F))).mulVec y)

def RelData (A A' : Fin g → Adl C Y) (p n k : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F), IsUnit J.det ∧ SecondLat J p n P Q ∧ genericPoint Y.X ∈ W ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) ∧
    LineBase V d A p ∧ LineBase V d A' p ∧
    (∀ a, ChartReg V (U a) (H a) T ∧ MinorNorm V W (U a) (H a) d T A p ∧
      ChartReg V (U a) (P.map (V.φ.comp (algebraMap F Y.Fn)) * H a) T ∧
      MinorNorm V W (U a) (P.map (V.φ.comp (algebraMap F Y.Fn)) * H a) d T A' p) ∧
    IsoAgree V W U H T J p k

def FrameOn (V : Cover Y) (W : Y.X.Opens) (U : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (A : Fin g → Adl C Y) (p : ℕ)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ) : Prop :=
  Lf * Um = 1 ∧ (∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ k l, RegAt x (Um k l) ∧ RegAt x (Lf l k)) ∧
    (∀ i (z : V.G), V.j z ∈ U → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c i)) ∧
    AtTest V W p fun v e y z yt => ⊤ ≤ yt ⁻¹ᵁ U →
      (∀ i, (A i).lg v e y = Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c i : V.G.functionField))))) ∧
      ∃ B : Matrix (Fin g) (Fin g) (AlgebraicClosure F), B.BlockTriangular id ∧
        (∀ i, B i i = valAt z (V.φ (d (below y.1) i : Y.Fn) / (c i : V.G.functionField))) ∧
        Um.map (valAt (z ≫ V.j)) = valMat V H (T (below y.1)) z * B

def DualAt (A B : Fin g → Adl C Y) (p : ℕ) : Prop :=
  (∀ k x, UnitAt x (genAt (B k).D x * genAt (A (Fin.rev k)).D x)) ∧
    ∀ k v, resP v = p → ∀ (e : Ext v) (y : AlgPt Y), (B k).lg v e y = -(A (Fin.rev k)).lg v e y +
      Real.log (e.w (valAt y.1 (genAt (B k).D (below y.1) * genAt (A (Fin.rev k)).D (below y.1))))

end GlobalTheory.ConstLat

end
