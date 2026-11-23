import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatumAOne

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

structure GDatum where
  F : Type
  [fld : Field F]
  [nf : NumberField F]
  [cm : IsCMField F]
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  ω : 𝓞 F
  tr : ℤ
  nm : ℤ
  tr_eq : ω + bar ω = (tr : 𝓞 F)
  nm_eq : ω * bar ω = (nm : 𝓞 F)
  disc_neg : tr ^ 2 - 4 * nm < 0
  O : Type
  [rng : Ring O]
  [alg : Algebra (𝓞 F) O]
  freeO : Module.Free ℤ O
  finO : Module.Finite ℤ O
  m : ℕ
  m_pos : 0 < m
  rankO : Module.finrank ℤ O = m ^ 2 * Module.finrank ℚ F
  central : ∀ x : O, (∀ y, x * y = y * x) → ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c
  star : O ≃+* Oᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x
  star_F : ∀ c : 𝓞 F, star (algebraMap (𝓞 F) O c) = MulOpposite.op (algebraMap (𝓞 F) O (bar c))

  splitSome : ∃ (q : ℕ) (_ : Fact q.Prime),
    Nonempty ((O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[q]))
  La : Type
  [acg : AddCommGroup La]
  [modO : Module O La]
  freeLa : Module.Free ℤ La
  finLa : Module.Finite ℤ La
  n : ℕ
  n_pos : 1 ≤ n
  rankLa : Module.finrank ℤ La = m * n * Module.finrank ℚ F
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : Function.Injective EF
  adj : ∀ (b : O) x y, EF (b • x) y = EF x ((star b).unop • y)
  a : ℕ
  ρc : ℂ
  ρc_root : ρc ^ 2 - tr * ρc + nm = 0
  tau : Fin a ↪ (F →+* ℂ)
  tau_ω : ∀ i, tau i (ω : F) = ρc
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    (∀ (b : O) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) → J ∘ₗ A = A ∘ₗ J) ∧
    ∀ (c : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (algebraMap (𝓞 F) O c • x)) →
      let S : ℂ := (m : ℂ) * (∑ i, tau i (c : F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : F →+* ℂ => τ (ω : F) = (starRingEnd ℂ) ρc), (n : ℂ) * τ (c : F) -
        ∑ i, (starRingEnd ℂ) (tau i (c : F)))
      LinearMap.trace ℝ _ A = 2 * S.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * S.im

attribute [instance] GDatum.fld GDatum.nf GDatum.cm GDatum.rng GDatum.alg GDatum.acg GDatum.modO

def _root_.GlobalTheory.UPel.HT.Datum.toG {p : ℕ} [Fact p.Prime] (D : Datum p) : GDatum where
  F := D.F
  bar := D.bar
  bar_eq := D.bar_eq
  ω := D.ω
  tr := D.tr
  nm := D.nm
  tr_eq := D.tr_eq
  nm_eq := D.nm_eq
  disc_neg := D.disc_neg
  O := D.O
  freeO := D.freeO
  finO := D.finO
  m := D.m
  m_pos := D.m_pos
  rankO := D.rankO
  central := D.central
  star := D.star
  star_star := D.star_star
  star_F := D.star_F
  splitSome := ⟨p, inferInstance, D.splitP⟩
  La := D.La
  freeLa := D.freeLa
  finLa := D.finLa
  n := D.n
  n_pos := D.n_pos
  rankLa := D.rankLa
  EF := D.EF
  alt := D.alt
  nondeg := D.nondeg
  adj := D.adj
  a := D.a
  ρc := D.ρc
  ρc_root := D.ρc_root
  tau := D.tau
  tau_ω := D.tau_ω
  dom := D.dom

structure GBase (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] where
  ρ : R
  ρ_root : ρ ^ 2 - G.tr * ρ + G.nm = 0
  t : Fin G.a → (𝓞 G.F →+* R)
  t_ω : ∀ i, t i G.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤

variable {S : Scheme.{0}}

structure GTateIso (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → G.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : G.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * G.EF x y))

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

def actF {A : Over S} [GrpObj A] (act : OActN G.O A) : OAct (𝓞 G.F) A where
  act c := act.act (algebraMap (𝓞 G.F) G.O c)
  hom c := act.hom _
  one := by rw [map_one]; exact act.one
  mul b c := by rw [← act.mul, ← map_mul, mul_comm]
  add b c := by rw [map_add]; exact act.add _ _

structure GObj (b : GBase G R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN G.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  rosati : ∀ c : G.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (G.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 G.F) G.O G.ω) (β b.ρ) v →
      ∃ w : Fin G.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 G.F, IsTanScal act x (algebraMap (𝓞 G.F) G.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (actF act) x (β.comp (b.t i)) G.m
  eta : G.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : G.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : GTateIso G k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] GObj.grp GObj.comm

structure GObjMap {b : GBase G R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : GObj b N s') (o : GObj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

structure GenModel (b : GBase G R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : GObj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : GObj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (GObjMap o univ f)

theorem exists_gDatum_one_one_one : ∃ G : GDatum, G.a = 1 ∧ G.n = 1 ∧ G.m = 1 := by
  obtain ⟨_, D, ha, hn, hm⟩ := GlobalTheory.UPel.HT.exists_datum_a_one
  exact ⟨D.toG, ha, hn, hm⟩

instance nonempty_gDatum : Nonempty GDatum := ⟨exists_gDatum_one_one_one.choose⟩

instance nonempty_gBase_complex (G : GDatum) : Nonempty (GBase G ℂ) := ⟨{
  ρ := G.ρc
  ρ_root := G.ρc_root
  t i := (G.tau i).comp (algebraMap (𝓞 G.F) G.F)
  t_ω i := G.tau_ω i
  comax i j hij := by
    have hne : (G.tau i).comp (algebraMap (𝓞 G.F) G.F) ≠ (G.tau j).comp (algebraMap (𝓞 G.F) G.F) := fun h =>
      hij (G.tau.injective (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 G.F)) h))
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨x, rfl⟩)
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hx)) }⟩

example {p : ℕ} [Fact p.Prime] {D : Datum p} (b : Base D R) : GBase D.toG R :=
  ⟨b.ρ, b.ρ_root, b.t, b.t_ω, b.comax⟩

example {p : ℕ} [Fact p.Prime] (D : Datum p) :
    D.toG.La = D.La ∧ D.toG.EF = D.EF ∧ D.toG.a = D.a ∧ D.toG.m = D.m ∧ D.toG.n = D.n :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) (x : G.La) : I.ev 1 x = 1 :=
  (I.ker 1 one_pos x).2 ⟨x, (one_nsmul x).symm⟩

end GlobalTheory.UPel.HT.Gen
