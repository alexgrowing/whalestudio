import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeTorsionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSubalgebraStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionInjectiveSubalgebraStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx

theorem lie_pack (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li)
    (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li) (h₀ : M₀.IsActOf act.act ρ₀)
    (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω]
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap (algebraMap R Ω) ≫ x = ξ) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L)
      (toLi : L →ₗ[R] Li) (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li),
      Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧
      (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧
      IsBaseChange Ω j ∧ (∀ u v, j u (toLi v) = algebraMap R Ω (u v)) ∧
      ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  obtain ⟨L, i1, i2, M, ρ, toLi, hf, hp, ha, hb, hpt, hρ⟩ := GlobalTheory.T.lie_model_action_subalgebra X G Ω ξ Li M₀ B act ρ₀ h₀ O R x hx
  obtain ⟨j, hj, hj'⟩ := GlobalTheory.T.dual_lattice_base_change Ω O R L Li toLi hb
  exact ⟨L, i1, i2, M, ρ, toLi, j, hf, hp, ha, hb, hpt, hj, hj', hρ⟩

theorem isIso_spMap_fracToField {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : IsIso (spMap (fracToField R)) := by
  have hs : Function.Surjective (fracToField R) := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    refine ⟨algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b, ?_⟩
    have h : ∀ r : R, fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r := fun r =>
      IsFractionRing.lift_algebraMap _ r
    rw [map_div₀, h, h]
  have : IsIso (CommRingCat.ofHom (fracToField R)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(fracToField R).injective, hs⟩
  infer_instance

theorem finite_torsT (E : Type) [Field E] [NumberField E] (N n : ℕ) (hn : n ≠ 0) : Finite (TorsT E N n) := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  exact inferInstanceAs (Finite (Fin N → (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)})))

theorem qhom_surjective (E : Type) [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := fun t => by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  refine ⟨Multiplicative.ofAdd f, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact hf i

theorem qhom_eq_one_iff (E : Type) [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have h1 : qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, (n : 𝓞 E) ∣ y i := by
    constructor
    · intro h i
      have h2 := congrFun (congrArg Multiplicative.toAdd h) i
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h i))
  rw [h1]
  constructor
  · intro h
    choose f hf using h
    exact ⟨f, by funext i; simp [hf i, nsmul_eq_mul]⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp [nsmul_eq_mul]⟩

theorem chartPack_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → Nonempty (ChartPack G O c') := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hv hpq p _ hpS hHT hp2 hdisc A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' hc
  obtain ⟨hΩ, hno, hic, hfr, x, hx⟩ := GlobalTheory.T.arith_variety_prime_torsion E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hv p hpS A m hm O c' hc
  haveI := hno; haveI := hic; haveI := hfr; haveI := hΩ
  haveI : CharZero (CR O y c') := ⟨fun a b h => by
    have h2 := congrArg (algebraMap (CR O y c') Ω) h
    simpa using h2⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨L, i1, i2, M, ρ, toLi, j, hfin, hproj, hact, hbc, hpt, hjbc, hj, hρ⟩ :=
    lie_pack 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M (𝓞 E) 𝔐.t.act 𝔐.ρ 𝔐.act O (CR O y c') x hx
  have hR : 0 < 𝔐.R p := by have := 𝔐.R_ge p hpS; omega
  obtain ⟨Γ₁, i₁, ht₁, hp₁⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₁.pt p (p ^ 𝔐.R p)
    (Fact.out : p.Prime).one_lt.le (dvd_pow_self p hR.ne') (𝔐.tors p hpS) G.t₁.inj G.t₁.onto
  obtain ⟨Γ₂, i₂', ht₂, hp₂⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₂.pt (p ^ 𝔐.R p) (p ^ 𝔐.R p)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) dvd_rfl (𝔐.tors p hpS) G.t₂.inj G.t₂.onto
  have hn0 : p ^ 𝔐.R p ≠ 0 := (pow_pos (Fact.out : p.Prime).pos _).ne'
  have hmem : ∀ z : Ω, z ^ (p ^ 𝔐.R p) = 1 → z ∈ CR O y c' := fun z hz => by
    have hi : IsIntegral ℤ z := IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_one)
    have h := IsIntegralClosure.algebraMap_mk' A z hi
    rw [← h, IsScalarTower.algebraMap_apply A O Ω]
    exact (CR O y c').algebraMap_mem _
  have hz1 : G.ζ ^ (p ^ 𝔐.R p) = 1 := G.ζ_prim.pow_eq_one
  have hz2 : (G.ζ⁻¹) ^ (p ^ 𝔐.R p) = 1 := by rw [inv_pow, hz1, inv_one]
  have hne : G.ζ ≠ 0 := G.ζ_prim.ne_zero hn0
  obtain ⟨ζ, hζ⟩ : ∃ u : (CR O y c')ˣ, ((u : CR O y c') : Ω) = G.ζ :=
    ⟨⟨⟨G.ζ, hmem _ hz1⟩, ⟨G.ζ⁻¹, hmem _ hz2⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩
  haveI hfinT : Finite (TorsT E (D.p + D.q) (p ^ 𝔐.R p)) := finite_torsT E _ _ hn0
  have hsurj : Function.Surjective (qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p)) := qhom_surjective E _ _
  have hker : ∀ y₁, qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p) (Multiplicative.ofAdd y₁) = 1 ↔ ∃ y', y₁ = (p ^ 𝔐.R p) • y' :=
    qhom_eq_one_iff E _ _
  haveI hiso := isIso_spMap_fracToField (CR O y c')
  have hlin : ∀ (a : 𝓞 E) y₁, (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left ≫ i₂' =
        (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ i₂' ≫ (𝔐.t.act.act a).left := by
    intro a y₁
    rw [← cancel_epi (spMap (fracToField (CR O y c')))]
    have h1 := hp₂ (qhom _ _ (Multiplicative.ofAdd (a • y₁)))
    have h2 := hp₂ (qhom _ _ (Multiplicative.ofAdd y₁))
    have h3 : (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left =
        (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ (𝔐.t.act.act a).left :=
      congrArg (fun f => f.left) (G.t₂.lin a y₁)
    rw [← h1, h3, h2]
    simp only [Category.assoc]
  have hzpow : ζ ^ (p ^ 𝔐.R p) = 1 := by
    apply Units.ext
    apply Subtype.ext
    show (((ζ : CR O y c') ^ (p ^ 𝔐.R p) : CR O y c') : Ω) = 1
    rw [SubmonoidClass.coe_pow, hζ, hz1]
  have hbar : ∀ a : 𝓞 E, RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := fun a => by
    ext
    rw [H.bar_eq]
    rfl
  obtain ⟨Dh, hDe, hHT⟩ := GlobalTheory.T.HTChartExists_holds (CR O y c') Ω E (HT.cmConj E) p (𝔐.R p) (D.p + D.q) _ Γ₂ 𝔐.X 𝔐.t.G x i₂' ht₂ hsm
    𝔐.t.act.act 𝔐.t.act.hom L M ρ hact (Module.Dual Ω 𝔐.Li) j hjbc (qhom _ _) hsurj hker hlin ζ hzpow G.e G.alt
    (fun a y₁ z => by rw [hbar]; exact G.adj a y₁ z) G.e_surj G.e_inj
  have hform : ∀ (b : 𝓞 E) (w : Module.Dual (CR O y c') L), j (w ∘ₗ ρ b) = j w ∘ₗ 𝔐.ρ b := by
    intro b w
    ext e
    refine hbc.inductionOn e (fun e => j (w ∘ₗ ρ b) e = (j w ∘ₗ 𝔐.ρ b) e) (by simp) ?_ ?_ ?_
    · intro v
      simp only [LinearMap.comp_apply]
      rw [hj, ← hρ, hj]
      rfl
    · intro s n hn
      simp only [map_smul, hn]
    · intro n₁ n₂ h₁ h₂
      simp only [map_add, h₁, h₂]
  have hact' : ∀ (a : 𝓞 E) (u : Module.Dual Ω 𝔐.Li), Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a) := by
    intro a u
    refine hjbc.inductionOn u (fun u => Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a)) (by simp) ?_ ?_ ?_
    · intro w
      rw [hHT.2.1, hbar, hform]
    · intro s n hn
      rw [map_smul, hn]
      rfl
    · intro n₁ n₂ h₁ h₂
      rw [map_add, h₁, h₂]
      rfl
  exact ⟨{ x := x, x_gen := hx, L := L, fin := hfin, proj := hproj, M := M, ρ := ρ, act := hact, toLi := toLi, toLi_bc := hbc,
           toLi_pt := hpt, j := j, j_bc := hjbc, j_apply := hj, Γ₁ := Γ₁, i₁ := i₁, tors₁ := ht₁, pts₁ := hp₁,
           Γ₂ := Γ₂, i₂ := i₂', tors₂ := ht₂, pts₂ := hp₂, ζ := ζ, ζ_eq := hζ, Dh := Dh, Dh_e := hDe, Dh_act := hact', isHT := hHT }⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx
