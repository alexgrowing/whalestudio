import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto
open scoped TensorProduct Matrix

namespace UpperTheory.Gal.KunnethLefschetz.Di

def IsFirstChernClassOfLineBundle (q : ℕ) {Y : Scheme.{0}} (D : CrystallineSemistableComparison.E.LineData Y) (x : Ht q (sch.obj Y) 2 1) : Prop :=
  ∃ L : cech D.f ⟶ ofCat (glCat 1), D.IsMap L ∧ pull _ (cechAug D.f) _ 2 x = c1 q L

def untw (q : ℕ) {X : Scheme.{0}} (x : Ht q (sch.obj X) 2 1) (ρ : Ht q (sch.obj X) 0 (-1)) : Ht q (sch.obj X) 2 0 :=
  (cup q x ρ).cast (add_zero 2) (add_neg_cancel 1)

def pow0 (q : ℕ) {X : Scheme.{0}} (x : Ht q (sch.obj X) 2 0) : ∀ j : ℕ, Ht q (sch.obj X) (2 * j) 0
  | 0 => one q (sch.obj X)
  | j + 1 => cup0 q (by push_cast; ring) (pow0 q x j) x

def ProjectiveBundleFormulaTorsion (q N : ℕ) {E Z : Scheme.{0}} (r : E ⟶ Z) (x : Ht q (sch.obj E) 2 0) : Prop :=
  ∀ n : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj Z) (n - 2 * (j : ℕ)) 0 =>
    ∑ j : Fin N, (cup0 q (sub_add_cancel n _) (pull _ (sch.map r) _ _ (a j)) (pow0 q x j) : Ht q _ n 0)

section Adic
variable (l : ℕ) [Fact l.Prime]

def PBV (N : ℕ) {E Z : Scheme.{0}} (r : E ⟶ Z) (ξ : V l E 2) : Prop :=
  ∀ n : ℤ, Function.Bijective fun a : ∀ j : Fin N, V l Z (n - 2 * (j : ℕ)) =>
    ∑ j : Fin N, cupV l E (sub_add_cancel n _) (pb l r _ (a j)) (powV l ξ j)

abbrev TT (X : Scheme.{0}) (n : ℕ) : Type 1 := Hl l (sch.obj X) n 0

variable {l}

abbrev toV {X : Scheme.{0}} {n : ℤ} (x : Hl l (sch.obj X) n 0) : V l X n := (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x

def CupL {X : Scheme.{0}} {i j : ℕ} (x : TT l X i) (y : TT l X j) (z : TT l X (i + j)) : Prop :=
  ∀ k, z.1 k = cup0 (l ^ k) (Nat.cast_add i j).symm (x.1 k) (y.1 k)

def castL {X : Scheme.{0}} {i j : ℕ} (h : i = j) (x : TT l X i) : TT l X j := h ▸ x

variable (l) in

def DiagQ (d : ℕ) {X P W : Scheme.{0}} (p₁ p₂ : P ⟶ X) (π : W ⟶ P) (e : V l W ((2 : ℕ) : ℤ)) : Prop :=
  ∃ (δ : V l P ((2 + 2 * d : ℕ) : ℤ)) (m : V l W ((2 * d : ℕ) : ℤ)) (s : ℕ) (a : Fin s → V l X ((2 + 2 * d : ℕ) : ℤ))
    (b : Fin s → V l X ((0 : ℕ) : ℤ)) (t : ℕ) (i j : Fin t → ℕ) (h : ∀ c, i c + j c = 2 + 2 * d) (u : ∀ c, V l X (i c))
    (v : ∀ c, V l X (j c)),
    pb l π _ δ = cupV l W (Nat.cast_add _ _).symm e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ c, b c = oneV l X ∧ (∀ c, j c ≠ 0) ∧
    δ = ∑ c, cupV l P (add_zero _) (pb l p₁ _ (a c)) (pb l p₂ _ (b c)) +
      ∑ c, cupV l P (by rw [← h c, Nat.cast_add]) (pb l p₁ _ (u c)) (pb l p₂ _ (v c))

variable (l) in

def DiagL (d : ℕ) {X P W : Scheme.{0}} (p₁ p₂ : P ⟶ X) (π : W ⟶ P) (v : TT l W 2) : Prop :=
  ∃ (c : TT l P (2 + 2 * d)) (w : TT l W (2 * d)) (z : TT l W (2 + 2 * d))
    (m₀ : ℕ) (a₀ : Fin m₀ → TT l X (2 + 2 * d)) (b₀ : Fin m₀ → TT l X 0) (ab₀ : Fin m₀ → TT l P (2 + 2 * d + 0))
    (m : ℕ) (i j : Fin m → ℕ) (hij : ∀ s, i s + j s = 2 + 2 * d) (a : ∀ s, TT l X (i s)) (b : ∀ s, TT l X (j s))
    (ab : ∀ s, TT l P (i s + j s)) (one₀ : TT l X 0) (N : ℚ_[l]),
    CupL v w z ∧ toV (pullHl l (sch.map π) _ 0 c) = toV z ∧
    (∀ s, CupL (pullHl l (sch.map p₁) _ 0 (a₀ s)) (pullHl l (sch.map p₂) _ 0 (b₀ s)) (ab₀ s)) ∧
    (∀ s, CupL (pullHl l (sch.map p₁) _ 0 (a s)) (pullHl l (sch.map p₂) _ 0 (b s)) (ab s)) ∧ (∀ s, j s ≠ 0) ∧
    toV c = ∑ s, toV (show TT l P (2 + 2 * d) from ab₀ s) + ∑ s, toV (castL (hij s) (ab s)) ∧
    (∀ k, one₀.1 k = one (l ^ k) (sch.obj X)) ∧ N ≠ 0 ∧
    LinearIndependent ℚ_[l] (fun s => toV (a₀ s)) ∧ ∑ s, toV (b₀ s) = N • toV one₀

end Adic

def GeoPB : Prop := ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω],
  (∀ {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ q = p),
    IsPullback (pullback.fst _ _) (GlobalTheory.Et.geomMap Ω p u hu) u (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) ∧
  ∀ {X P : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (q : P ⟶ Spec (CommRingCat.of K)) (p₁ p₂ : P ⟶ X) (h₁ : p₁ ≫ p = q)
    (h₂ : p₂ ≫ p = q), IsPullback p₁ p₂ p p →
    IsPullback (GlobalTheory.Et.geomMap Ω q p₁ h₁) (GlobalTheory.Et.geomMap Ω q p₂ h₂) (pullback.snd p _) (pullback.snd p _)

def GeoM : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (∀ (M : Model l K) (d : ℕ), M.Sm → SmoothOfRelativeDimension d M.p →
    SP d (pullback.snd _ _ : CrystallineSemistableComparison.E.gb M ⟶ S (PadicAlgCl l)) ∧ IsProj (pullback.snd _ _ : CrystallineSemistableComparison.E.gb M ⟶ S (PadicAlgCl l))) ∧
  (∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p), M.Sm → N.Sm → IsProper (Model.genMap u hu)) ∧
  ∀ (M P : Model l K) (p₁ p₂ : P.X ⟶ M.X) (h₁ : p₁ ≫ M.p = P.p) (h₂ : p₂ ≫ M.p = P.p), IsPullback p₁ p₂ M.p M.p →
    IsPullback (Model.genMap p₁ h₁) (Model.genMap p₂ h₂) M.q M.q

def FirstChernClassBaseChange : Prop := In → ∀ (q : ℕ) [NeZero q] {Y Y₁ Y₂ : Scheme.{0}} (D : CrystallineSemistableComparison.E.LineData Y) (a : Y₁ ⟶ Y) (c : Y₂ ⟶ Y₁)
  (D' : CrystallineSemistableComparison.E.LineData Y₂) (π : D'.Y ⟶ D.Y), D.IsBC (c ≫ a) D' π → IsUnit (q : Γ(Y₂, ⊤)) → ∀ x, IsFirstChernClassOfLineBundle q D' x → IsFirstChernClassOfLineBundle q ((D.pb a).pb c) x

def RootNat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
  pull _ (sch.map g) _ 0 (rootClass i ζ) = rootClass i (ζ.map g.appTop.hom)

def PowRoot : Prop := In → ∀ (q : ℕ) [NeZero q] {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) (x : Ht q (sch.obj E) 2 1) (j : ℕ),
  pow0 q (untw q x (rootClass (-1) ζ)) j =
    (cup q (cpow q x j) (rootClass (-(j : ℤ)) ζ)).cast (add_zero _) (add_neg_cancel _)

def Untw : Prop := In → RootNat → PowRoot → ∀ (q : ℕ) [NeZero q] (N : ℕ) {E Z : Scheme.{0}} (r : E ⟶ Z) (ζ : Prim q Γ(Z, ⊤))
  (x : Ht q (sch.obj E) 2 1), PBT q N r x → ProjectiveBundleFormulaTorsion q N r (untw q x (rootClass (-1) (ζ.map r.appTop.hom)))

def PBLim : Prop := In → ∀ (l : ℕ) [Fact l.Prime], Ring l → ∀ (N : ℕ) {E Z : Scheme.{0}} (r : E ⟶ Z), IsUnit (l : Γ(Z, ⊤)) →
  ∀ v : Hl l (sch.obj E) 2 0, (∀ k, ProjectiveBundleFormulaTorsion (l ^ k) N r (v.1 k)) → PBV l N r (toV v)

def PBQOf : Prop := ∀ (l : ℕ) [Fact l.Prime], Ring l → (∀ (X : Scheme.{0}) (n : ℤ), n < 0 → Subsingleton (V l X n)) →
  ∀ (N : ℕ), 2 ≤ N → ∀ {E Z : Scheme.{0}} (r : E ⟶ Z), IsUnit (l : Γ(Z, ⊤)) → ∀ ξ : V l E 2, PBV l N r ξ → PBQ l r ξ

def DiagSq : Prop := QDiag → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l →
  ∀ (d : ℕ) {X P : Scheme.{0}} (p : X ⟶ S k) (p₁ p₂ : P ⟶ X) (Δ : X ⟶ P), IsPullback p₁ p₂ p p → Δ ≫ p₁ = 𝟙 _ → Δ ≫ p₂ = 𝟙 _ →
  SP (d + 1) p → IsProj p → ∀ {W E : Scheme.{0}} (π : W ⟶ P) (i : E ⟶ W) (r : E ⟶ X) (c : ℕ), IsPullback i r π Δ →
    IsPair 1 c (π ≫ p₁ ≫ p) i → IsProper r → ∀ (U : W.Opens), Off i U → ∀ e : V l W 2, pb l U.ι 2 e = 0 →
    PBQ l r (pb l i 2 e) → DiagQ l d p₁ p₂ π e

def Clear : Prop := In → ∀ (l : ℕ) [Fact l.Prime], Ring l → ∀ (d : ℕ) {X P W : Scheme.{0}} (p₁ p₂ : P ⟶ X) (π : W ⟶ P),
  IsUnit (l : Γ(X, ⊤)) → ∀ v : TT l W 2, DiagQ l d p₁ p₂ π (toV v) → DiagL l d p₁ p₂ π v

end UpperTheory.Gal.KunnethLefschetz.Di
