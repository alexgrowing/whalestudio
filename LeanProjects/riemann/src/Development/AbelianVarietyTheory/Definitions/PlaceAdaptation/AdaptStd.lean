import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PlaceInt

section Formal
variable {V : Type} [CommRing V]
open Classical in

def evC {σ τ : Type} (a : σ → MvPowerSeries τ V) (f : MvPowerSeries σ V) : MvPowerSeries τ V :=
  if h : ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j then h.choose f else 0
variable {d : ℕ}

def evV {m n : ℕ} (a : Fin m → Pt V n d) (f : PS V m d) : PS V n d := evC (fun p : Fin m × Fin d => a p.1 p.2) f

def cpt {n : ℕ} (α : Fin d → V) : Pt V n d := fun i => MvPowerSeries.C (α i)

def Small [IsLocalRing V] (α : Fin d → V) : Prop := ∀ i, α i ∈ maximalIdeal V

def addV {n : ℕ} (F : Fin d → PS V 2 d) (a b : Pt V n d) : Pt V n d := fun i => evV ![a, b] (F i)

def compV {n : ℕ} (φ : Pt V 1 d) (a : Pt V n d) : Pt V n d := fun i => evV ![a] (φ i)

def shift {n : ℕ} (F : Fin d → PS V 2 d) (α : Fin n → Fin d → V) (f : PS V n d) : PS V n d :=
  evV (fun b => addV F (pt V d b) (cpt (α b))) f
variable {O : Type} [CommRing O] [StarRing O]

def matV (B : FB V d O) {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (x : Fin n → Pt V m d) : Fin n → Pt V m d :=
  fun i => (List.ofFn fun j => compV (B.A.act (mu i j)) (x j)).foldr (addV B.G.F) 0

def pullM (B : FB V d O) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (f : PS V n d) : PS V n d :=
  evV (matV B mu fun j => pt V d j) f

def kerM [IsLocalRing V] (B : FB V d O) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) : Set (Fin n → Fin d → V) :=
  {α | (∀ b, Small (α b)) ∧ matV B (m := 0) mu (fun j => cpt (α j)) = 0}

def SplitKer (B : FB V d O) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra V Ω], Function.Injective (algebraMap V Ω) → ∀ χ : PS V n d →ₐ[V] Ω,
    (∀ b i, χ (matV B mu (fun j => pt V d j) b i) = 0) → ∀ p, χ (MvPowerSeries.X p) ∈ (algebraMap V Ω).range

def FinHt [IsLocalRing V] (B : FB V d O) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField V) 1 d)) ^ M ≤
    Ideal.span (Set.range fun i => MvPowerSeries.map (residue V) (B.A.act (N : O) i))

def jacM (B : FB V d O) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) : V :=
  Matrix.det (Matrix.of fun p q : Fin n × Fin d =>
    MvPowerSeries.coeff (Finsupp.single q 1) (matV B mu (fun j => pt V (n := n) d j) p.1 p.2))
variable (B : FB V d O) (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O)

def IsTheta (Θ : PS V 3 d) : Prop :=
  let L := fun a : Pt K 3 d => ev (n := 3) ![a] (B.hL K h w0)
  let s := addOf (n := 3) (B.FK K)
  FB.toK K Θ = FB.expS K (L (s (s (pt K d 0) (pt K d 1)) (pt K d 2)) - L (s (pt K d 0) (pt K d 1)) - L (s (pt K d 0) (pt K d 2))
    - L (s (pt K d 1) (pt K d 2)) + L (pt K d 0) + L (pt K d 1) + L (pt K d 2))

def IsIota (jo : PS V 1 d) : Prop :=
  FB.toK K jo = FB.expS K (ev (n := 1) ![B.actK K (-1)] (B.hL K h w0) - B.hL K h w0)

def IsKappa {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d) : Prop :=
  FB.toK K κ = FB.expS K (∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)
    - (N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0))
variable {K h w0}

structure TrUnit (Θ : PS V 3 d) (jo : PS V 1 d) (k : ℕ) (α : Fin d → V) (u : PS V 1 d) : Prop where
  unit : IsUnit u
  mul : evV (n := 2) ![addV B.G.F (pt V d 0) (pt V d 1)] u * MvPowerSeries.C (MvPowerSeries.constantCoeff u) =
    evV (n := 2) ![pt V d 0] u * evV (n := 2) ![pt V d 1] u * evV (n := 2) ![pt V d 0, pt V d 1, cpt α] Θ ^ k
  order : (fun f : PS V 1 d => u * shift B.G.F (fun _ => α) f)^[k] 1 = 1
  sym : MvPowerSeries.C (MvPowerSeries.constantCoeff u) * evV (n := 0) ![cpt α] jo ^ k *
    evV (n := 0) ![compV (B.A.act (-1)) (cpt α)] u = 1
end Formal

section Sections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecN {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ) : Type :=
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x))

def sqN {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (N : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x))) : SecN Xo x (N ^ 2) :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.zCast Xo.univ.t.G (Nat.cast_pow N 2).symm F

def Pulls {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (a : 𝓞 E) {k k' : ℕ} (F : SecN Xo x k) (F' : SecN Xo x k') : Prop :=
  IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act a) (k' : ℤ) (k : ℤ) F F'

def Moves {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {k : ℕ} (b : ptO Xo x ⟶ Xo.univ.t.G) (F F' : SecN Xo x k) : Prop :=
  IsSymAct Xo.univ.t.G Xo.univ.t.PP k b F F'

inductive Reach {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s : SecN Xo x 1) : ∀ k : ℕ, SecN Xo x k → Prop
  | base : Reach s 1 s
  | pull (k N k' : ℕ) (a : 𝓞 E) (F : SecN Xo x k) (F' : SecN Xo x k') : Reach s k F → (k = 1 ∨ 4 ≤ k) → Odd N →
      a * H.bar a = (N : 𝓞 E) → k' = k * N → Pulls Xo a F F' → Reach s k' F'
  | move (k : ℕ) (b : ptO Xo x ⟶ Xo.univ.t.G) (F F' : SecN Xo x k) : Reach s k F → Moves Xo b F F' → Reach s k F'

def hv (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) {n : ℕ}
    (F : Fin n → SecN Xo y.x k) (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y (k : ℤ) (F b) (colOf m b)

abbrev HH (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))

def pushL {n : ℕ} (ga : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) : MvPolynomial (LtN Dw n) c.F :=
  MvPolynomial.aeval (fun ℓ : LtN Dw n => ∑ b, MvPolynomial.C (embF c ℓ.1 (ga b ℓ.2.2)) *
    MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : LtN Dw n)) P

def Kills {T : Over Xo.X} {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  ∀ i, (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (mu i j)).prod = 1

def IsSim (H : Host E) {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (N : ℕ) : Prop :=
  ∀ j k, ∑ i, H.bar (mu i j) * mu i k = if j = k then (N : 𝓞 E) else 0

def AllRat {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ψ : K →+* Ω) (w : ptO Xo (spMap ψ ≫ x) ⟶ Xo.univ.t.G), w ^ M = 1 →
    ∃ a : ptO Xo x ⟶ Xo.univ.t.G, w.left = spMap ψ ≫ a.left
variable {Xo c}

def IsExt {T T' : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e : ℕ)
    (y' : IntFr Xo c T' (iT.comp io)) : Prop :=
  0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧
    letI := io.toAlgebra
    letI := (iT.comp io).toAlgebra
    ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ y.1 y'.1
variable {T : CDVR} {io : c.F →+* T.Fr}

abbrev xOf (y : IntFr Xo c T io) : Sp T.Fr ⟶ Xo.X := letI := io.toAlgebra; y.1.x

abbrev sOf1 (y : IntFr Xo c T io) : SecN Xo (xOf y) 1 := letI := io.toAlgebra; y.1.s
variable [StarRing (𝓞 E)] {y : IntFr Xo c T io}

def Good3 (C : IntegralChartA3 Xo c T io y) : Prop :=
  FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT ∧ ∃ P : PELUnif (maximalIdeal T.V) C.I.G, P.TorsionIso

def GermIs (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F : SecN Xo (xOf y) k) (f : PS T.V 1 (chD C.ch)) : Prop :=
  letI := io.toAlgebra
  IsGerm y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP k F (MvPowerSeries.map (algebraMap T.V T.Fr) f)

def Regular (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F : SecN Xo (xOf y) k) : Prop :=
  ∃ σ, ReciprocityTheory.ChartRestriction.G.PullbackSections.SecTie C.I k F σ

def IsBT (C : IntegralChartA3 Xo c T io y) (B : FB T.V (chD C.ch) (𝓞 E)) : Prop :=
  B.G.F = C.FT ∧ B.A.act = C.actT ∧ B.ph1 = C.ph1T ∧ B.ph2 = C.ph2T ∧ B.sy = C.syT ∧ B.ad = C.adT

abbrev gaugeOf (C : IntegralChartA3 Xo c T io y) : PS T.Fr 2 (chD C.ch) := letI := io.toAlgebra; C.ch.h

def FormPt (C : IntegralChartA3 Xo c T io y) (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (α : Fin (chD C.ch) → T.V) : Prop :=
  Small α ∧ ∃ (aV : Sp T.V ⟶ C.I.G.G.left) (r : Sp T.Fr ⟶ C.I.t'.G.left), aV ≫ C.I.G.G.hom = 𝟙 _ ∧ r ≫ C.I.t'.G.hom = 𝟙 _ ∧
    r ≫ C.I.m1.φ = a.left ∧ r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV ∧
    ∀ m : ℕ, ∃ ψ : Jet T.V (Fin 1 × Fin (chD C.ch)) m →ₐ[T.V] T.V ⧸ maximalIdeal T.V ^ (m + 1),
      (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧
      spMap (Ideal.Quotient.mk (maximalIdeal T.V ^ (m + 1))) ≫ aV =
        spMap (ψ : Jet T.V (Fin 1 × Fin (chD C.ch)) m →+* T.V ⧸ maximalIdeal T.V ^ (m + 1)) ≫ (C.xT m).left

def ChBound (C : IntegralChartA3 Xo c T io y) (e : ℕ) (ρ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, ((-ρ : ℝ) : EReal) ≤ nuLocC C e k a n
end Sections

section Lattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Adapt {n : ℕ} (Λ : GenLat E n) (N ℓ : ℕ) where
  k : ℕ
  k₁ : ℕ
  ga : Matrix (Fin n) (Fin n) E
  p : Matrix (Fin n) (Fin n) (𝓞 E)
  q : Matrix (Fin n) (Fin n) (𝓞 E)
  g : Matrix (Fin n) (Fin n) (𝓞 E)
  odd : Odd k
  cop : Nat.Coprime k ℓ
  cop₁ : Nat.Coprime k₁ ℓ
  unitary : ∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0
  into : ∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n
  onto : ∀ v ∈ stdLat E n, ∃ w ∈ Λ.La, (k : E) • v = ga.mulVec w
  prod : (p * q).map (algebraMap (𝓞 E) E) = ((k * N : ℕ) : E) • ga
  cols : ∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ Λ.Ln
  spans : ∀ w ∈ Λ.Ln, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v
  gq : g * q = ((k₁ * N : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E))

def adaptStd (n N ℓ : ℕ) : Adapt (⟨stdLat E n⟩ : GenLat E n) N ℓ where
  k := 1
  k₁ := 1
  ga := 1
  p := 1
  q := (N : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E))
  g := 1
  odd := odd_one
  cop := Nat.coprime_one_left ℓ
  cop₁ := Nat.coprime_one_left ℓ
  unitary i j := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply]
    · intro b _ hb; simp [Matrix.one_apply_ne hb]
    · simp
  into v hv := by simpa using hv
  onto v hv := ⟨v, hv, by simp⟩
  prod := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  cols v hv := by
    have : (1 : Matrix (Fin n) (Fin n) (𝓞 E)).map (algebraMap (𝓞 E) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.one_mulVec]; exact ⟨hv, hv⟩
  spans w hw := by
    have : (1 : Matrix (Fin n) (Fin n) (𝓞 E)).map (algebraMap (𝓞 E) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    exact ⟨w, hw.1, by rw [this, Matrix.one_mulVec]; simp⟩
  gq := by simp
end Lattice

end GlobalTheory.PlaceInt
