import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieIndep

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}

theorem lieTie_add {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp C ⟶ S} {ψ : P.A.A.left ⟶ G.left}
    (hψ : IsGrpPullback P.A.A G y ψ) {x x' : LieG P.Gt}
    {u u' : Over.mk (spMap (algebraMap C (DualNumber C)) ≫ y) ⟶ G}
    (h : LieTie P ψ x u.left) (h' : LieTie P ψ x' u'.left) : LieTie P ψ (lieAdd x x') (u * u').left := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  refine ⟨lieAdd xG xG', w * w', h1.mul h1', (hψ.2 _ w w' u u' h2.symm h2'.symm).symm, ?_⟩
  let d : Over.mk ((specO C (DualNumber C)).hom ≫ spMap (algebraMap O C)) ⟶ specO O (DualNumber O) :=
    Over.homMk (spMap (dualMap (algebraMap O C))) (by
      refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
      ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  refine (P.gen_pull.2 _ w w' (d ≫ xG.1) (d ≫ xG'.1) h3.symm h3'.symm).symm.trans ?_
  rw [← MonObj.comp_mul]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem lieTie_unique_right {Y : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {x : LieG P.Gt} {u u' : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P ψ x u') : u = u' := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => (Fact.out : ¬ IsUnit (p : O)) (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have e : xG.1 = xG'.1 := (existsUnique_right hp (isAdicComplete_dualNumber p) x.1).unique h1 h1'
  have e1 : w.left = w'.left :=
    P.gen_pull.1.hom_ext (by rw [h3, h3', e]) ((Over.w w).trans (Over.w w').symm)
  rw [← h2, ← h2', e1]

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem linearIndependent_evLie {n : ℕ} (x : Fin n → LieG P.Gt)
    (h : ∀ a : Fin n → O, (∀ f : omega P.Gt, ∑ j, a j * f.1 (x j) = 0) → ∀ j, a j = 0) :
    LinearIndependent C (fun j => evLie P (x j)) := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) g
  choose a ha using hb
  have h0 := h a (fun f => P.integers.hom_inj (by
    have h1 := congrArg (fun L : P.OmC →ₗ[C] C => (b : O) • L ((1 : C) ⊗ₜ f)) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_zero, Finset.smul_sum] at h1
    rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ha, ← smul_assoc, smul_eq_mul]
    congr 1
    simp [evLie])) j
  have h2 := ha j
  rw [h0, map_zero, Algebra.smul_def] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left
    ((map_ne_zero_iff _ P.integers.hom_inj).2 (nonZeroDivisors.ne_zero b.2))

end GlobalTheory.CompHt.TieIndep

namespace GlobalTheory.CompHt

open TieIndep in

theorem linearIndependent_evLie_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → LinearIndependent C (fun j => evLie P (x j)) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  have hψ : IsGrpPullback P.A.A Xo.univ.t.G z.x ψ := hz.1 ▸ hP.isGrpPullback
  obtain ⟨N, _, _, w, ρ, -, htan, hcomb, hρ, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo C z.x
  choose b hb using fun j => (htan _).1 (z.tan τ j)
  have hadd : ∀ {y y' : LieG P.Gt} {m m' : N}, LieTie P ψ y (w m) → LieTie P ψ y' (w m') →
      LieTie P ψ (lieAdd y y') (w (m + m')) := fun {y y' m m'} h h' => by
    obtain ⟨u, h1, h2⟩ := (hcomb 2 ![m, m'] ![1, 1] (w (m + m'))).2 (by simp)
    have e0 : (u 0).left = w m := (h1 0).trans ((hsm 1 m).symm.trans (by rw [one_smul]))
    have e1 : (u 1).left = w m' := (h1 1).trans ((hsm 1 m').symm.trans (by rw [one_smul]))
    rw [← h2, show (List.ofFn u).prod = u 0 * u 1 by simp]
    exact lieTie_add hψ (e0 ▸ h) (e1 ▸ h')
  have hsc : ∀ (a : O) j, LieTie P ψ (AvDefs.lieScale P.Gt a (x j)) (w (algebraMap O C a • b j)) := fun a j => by
    rw [hsm, hb]
    exact (hx j).scale a
  refine linearIndependent_evLie x fun a ha j => ?_
  have h0 := hsc 0 j
  rw [map_zero, zero_smul] at h0
  have hs : ∀ s : Finset (Fin (Dw.mult τ)), ∃ y, LieTie P ψ y (w (∑ i ∈ s, algebraMap O C (a i) • b i)) ∧
      ∀ f : omega P.Gt, f.1 y = ∑ i ∈ s, a i * f.1 (x i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨_, h0, fun f => by rw [omega_lieScale, zero_mul, Finset.sum_empty]⟩
    | insert i s hi ih =>
      obtain ⟨y, h1, h2⟩ := ih
      rw [Finset.sum_insert hi]
      exact ⟨_, hadd (hsc (a i) i) h1, fun f => by rw [omega_lieAdd, omega_lieScale, h2, Finset.sum_insert hi]⟩
  obtain ⟨y, h1, h2⟩ := hs Finset.univ
  have e : y = AvDefs.lieScale P.Gt 0 (x j) :=
    (Point.omega_free_finite_bijective p C v O (𝓞 E) P).2.2.1 (LinearMap.ext fun f => by
      change f.1 y = f.1 _
      rw [h2, ha, omega_lieScale, zero_mul])
  have e2 := lieTie_unique_right h0 (e ▸ h1)
  have hu : z.u τ = fun i => w (b i) := funext fun i => (hb i).symm
  have e3 := (z.basis τ (w 0) ((htan _).2 ⟨0, rfl⟩) fun t => by rw [← hρ, ← hsm, map_zero, smul_zero]).unique
    (y₁ := fun i => algebraMap O C (a i)) (y₂ := 0) (by rw [hu, hcomb]; exact e2) (by rw [hu, hcomb]; simp)
  exact P.integers.hom_inj ((congrFun e3 j).trans (map_zero _).symm)

end GlobalTheory.CompHt
