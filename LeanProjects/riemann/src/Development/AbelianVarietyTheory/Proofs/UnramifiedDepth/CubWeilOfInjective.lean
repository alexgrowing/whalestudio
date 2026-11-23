import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlphaPair

section Eval

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def evP {n d : ℕ} (v : Fin n → Fin d → A) (f : PS R n d) : A := nEval f (fun q : Fin n × Fin d => v q.1 q.2)

def addP {d : ℕ} (F : Fin d → PS R 2 d) (a b : Fin d → A) : Fin d → A := fun j => evP ![a, b] (F j)

def cv {d : ℕ} (ga : Fin d → PowerSeries R) (t : A) : Fin d → A :=
  fun j => nEval (σ := Unit) (ga j) (fun _ => t)

variable {κ : Type} [Fintype κ] [DecidableEq κ] {a : κ → A} (ha : ∀ i, IsNilpotent (a i))

def evHom : MvPowerSeries κ R →+* A :=
  (MvPowerSeries.constantCoeff : MvPowerSeries Empty A →+* A).comp
    (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C a ha)).toRingHom

theorem evHom_apply (f : MvPowerSeries κ R) : evHom ha f = nEval f a := by
  simp [evHom, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f a ha]

include ha

theorem nEval_add (f g : MvPowerSeries κ R) : nEval (f + g) a = nEval f a + nEval g a := by
  simp only [← evHom_apply ha, map_add]

theorem nEval_sub (f g : MvPowerSeries κ R) : nEval (f - g) a = nEval f a - nEval g a := by
  simp only [← evHom_apply ha, map_sub]

theorem nEval_one : nEval (1 : MvPowerSeries κ R) a = 1 := by simp only [← evHom_apply ha, map_one]

end Eval

section Points

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev Fam (s : Sp Ω ⟶ S) (G : Over S) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], A → (overAt s A ⟶ G)

def IsAlpha (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 →
    g B (f a) = homAt s f ≫ g A a) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → g A (a + a') = g A a * g A a'

def Orth (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (g : Fam s G) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ e : A, e ^ 2 = 0 →
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → z ^ p = 1 → CubWeil c p (g A e) z 1

def NonDeg (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ g : Fam s G, IsAlpha p s G g → Orth p s G c g → g (DualNumber Ω) DualNumber.eps = 1

def Perf (n : ℕ) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 →
    (∀ (T' : Over S) (ρ : T' ⟶ T) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1) → x = 1

abbrev PtHom (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (overAt s A ⟶ G) →* (overAt s' A ⟶ B)

abbrev TorHom (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Multiplicative X →* Aˣ) →* (overAt s A ⟶ G)

def IsTorExt (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (X : Type)
    [AddCommGroup X] (τ : PtHom s s' G B) (io : TorHom s G X) : Prop :=
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (x : overAt s A ⟶ G),
    τ A' (homAt s f ≫ x) = homAt s' f ≫ τ A x) ∧
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A')
    (χ : Multiplicative X →* Aˣ), io A' ((Units.map (f : A →* A')).comp χ) = homAt s f ≫ io A χ) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], Function.Injective (io A)) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), τ A x = 1 ↔ ∃ χ, io A χ = x) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    ∀ y : overAt s' A ⟶ B, homAt s' π ≫ y = 1 → ∃ x : overAt s A ⟶ G, homAt s π ≫ x = 1 ∧ τ A x = y

def Transfer (n : ℕ) {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] [IsCommMonObj G] {B : Over S'} [GrpObj B]
    [IsCommMonObj B] {L : RigLB G} (c : CubicalStr G L) {M : RigLB B} (c' : CubicalStr B M) (τ : PtHom s s' G B) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (x y : overAt s A ⟶ G), CubWeil c n x y 1 → CubWeil c' n (τ A x) (τ A y) 1

abbrev PtFam (s : Sp Ω ⟶ S) (G : Over S) (d : ℕ) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Fin d → A) → (overAt s A ⟶ G)

def IsJetPt {V : Type} [CommRing V] (β : V →+* Ω) {G : Over (Sp V)} {d : ℕ}
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (P : PtFam (spMap β) G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A),
    (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) →
    (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))).left = spMap ψ ≫ (x m).left

def IsPtLaw (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (F : Fin d → PS Ω 2 d) (P : PtFam s G d) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : Fin d → A),
    (∀ j, IsNilpotent (a j)) → P B (fun j => f (a j)) = homAt s f ≫ P A a) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], P A 0 = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a b : Fin d → A), (∀ j, IsNilpotent (a j)) → (∀ j, IsNilpotent (b j)) →
    P A (addP F a b) = P A a * P A b

def IsPtUniv (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z

def IsPtCube (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {d : ℕ}
    (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (I : Ideal A), IsNilpotent I →
    ∀ (z : (overAt s A).left) (J), Good L.L z J →
    ∃ e : (Fin d → A) → (Fin d → A) → ((overAt s A).left.presheaf.stalk z)ˣ,
      ∀ a b u : Fin d → A, (∀ j, a j ∈ I) → (∀ j, b j ∈ I) → (∀ j, u j ∈ I) →
        (cubV c z J (P A a) (P A b) (P A u) * e a u * e b u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph1)) * (e (addP F a b) u).val ∧
        (cubV c z J (P A b) (P A u) (P A a) * e a b * e a u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph2)) * (e a (addP F b u)).val

section Basic

variable {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] {p : ℕ}

theorem hom_comp {A B C : Type} [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] [CommRing C] [Algebra Ω C]
    (f : A →ₐ[Ω] B) (g : B →ₐ[Ω] C) : homAt s g ≫ homAt s f = homAt s (g.comp f) :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp s f g

theorem hom_id {A : Type} [CommRing A] [Algebra Ω A] : homAt s (AlgHom.id Ω A) = 𝟙 _ :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id s

theorem IsAlpha.zero {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) (A : Type) [CommRing A] [Algebra Ω A] :
    g A 0 = 1 := by
  have := h.2 A 0 0 (zero_pow hp) (zero_pow hp)
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem IsAlpha.nsmul {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A] [Algebra Ω A] {a : A}
    (ha : a ^ p = 0) (n : ℕ) : g A (n * a) = g A a ^ n := by
  induction n with
  | zero => simpa using h.zero hp A
  | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, h.2 A _ _ (by rw [mul_pow, ha, mul_zero]) ha, ih, pow_succ]

theorem IsAlpha.pow_eq_one [CharP Ω p] {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A]
    [Algebra Ω A] {a : A} (ha : a ^ p = 0) : g A a ^ p = 1 := by
  rw [← h.nsmul hp ha, ← map_natCast (algebraMap Ω A), CharP.cast_eq_zero, map_zero, zero_mul, h.zero hp]

theorem IsAlpha.map {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}
    (hτ : IsTorExt s s' G B X τ io) {g : Fam s G} (h : IsAlpha p s G g) :
    IsAlpha p s' B (fun A _ _ a => τ A (g A a)) :=
  ⟨fun A A' _ _ _ _ f a ha => by beta_reduce; rw [h.1 A A' f a ha, hτ.1],
    fun A _ _ a a' ha ha' => by beta_reduce; rw [h.2 A a a' ha ha', map_mul]⟩

theorem cubWeil_of_injective [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (hf : Function.Injective f) {x y : overAt s A ⟶ G}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (h : CubWeil c n (homAt s f ≫ x) (homAt s f ≫ y) 1) : CubWeil c n x y 1 := by
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx hy
  have e := congrArg Units.val ((hζ.comp (homAt s f)).unique h)
  have inj : Function.Injective (homAt s f).left.appTop.hom := by
    have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
    have h₂ : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom (f : A →+* B)).hom :=
      hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
    rw [← h₁] at h₂
    exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom) h₂
  obtain rfl : ζ = 1 := Units.ext (inj (e.trans (map_one _).symm))
  exact hζ

theorem cubWeil_mul_right [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {T : Over S} {x y y' : T ⟶ G}
    (h : CubWeil c n x y 1) (h' : CubWeil c n x y' 1) : CubWeil c n x (y * y') 1 := by
  simpa using (h.symm.mul_left h'.symm).symm

end Basic

end Points

section Series

def c2 {R : Type} [CommRing R] {d : ℕ} (ph2 : PS R 3 d) (u : Fin d → R) : PS R 2 d :=
  fun mu => ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph2

def AddMod (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω) : Prop :=
  ∀ i (mu : Fin 2 →₀ ℕ), mu 0 < p → mu 1 < p → MvPowerSeries.coeff mu
    (MvPowerSeries.subst (fun q : Fin 2 × Fin d => Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) = 0

def Degenerate (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ph2 : PS Ω 3 d) : Prop :=
  ∃ ga : Fin d → PowerSeries Ω, (∀ i, PowerSeries.constantCoeff (ga i) = 0) ∧ (∃ i, PowerSeries.coeff 1 (ga i) ≠ 0) ∧
    AddMod p F ga ∧ ∃ b : PS Ω 1 d, c2 ph2 (fun i => PowerSeries.coeff 1 (ga i)) =
      ev (n := 2) ![addOf F (pt Ω d 0) (pt Ω d 1)] b - ev (n := 2) ![pt Ω d 0] b - ev (n := 2) ![pt Ω d 1] b

end Series

end GlobalTheory.AlphaPair
end
