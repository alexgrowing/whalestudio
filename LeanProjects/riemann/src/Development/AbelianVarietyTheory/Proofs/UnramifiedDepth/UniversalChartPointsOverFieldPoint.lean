import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetUniv

open GlobalTheory.ChartBaseChange (fib fibLift fibFst fibSnd fib_cond fib_ker exists_pt_of_aug pt_eps_self)

def unitSec {S : Scheme.{0}} (G : Over S) [GrpObj G] : S ⟶ G.left := (η[G]).left

def lft {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : T ⟶ G.left := y.left

theorem lft_w {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : lft y ≫ G.hom = f := Over.w y

theorem lft_inj {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} {y z : Over.mk f ⟶ G} (h : lft y = lft z) : y = z :=
  Over.OverMorphism.ext h

theorem unitSec_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ G.hom = 𝟙 S := Over.w (η[G])

theorem eq_one_iff {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} (y : Over.mk f ⟶ G) :
    y = 1 ↔ lft y = f ≫ unitSec G := by
  have e : lft (1 : Over.mk f ⟶ G) = f ≫ unitSec G := by
    show (toUnit (Over.mk f) ≫ η[G]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  exact ⟨fun h => h ▸ e, fun h => lft_inj (h.trans e.symm)⟩

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {κ : Type}

theorem aug_X (m : ℕ) (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = 0
  simp

theorem ker_aug_pow (m : ℕ) : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ≤ (orig V κ).map (Ideal.Quotient.mk _) := fun z hz => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h0 : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0 := hz
    have h1 : MvPolynomial.constantCoeff p = 0 := by simpa using h0
    have h2 := sub_const_mem_orig p
    rw [h1, map_zero, sub_zero] at h2
    exact Ideal.mem_map_of_mem _ h2
  rw [eq_bot_iff]
  refine (Ideal.pow_right_mono hle _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def toSp {A : Type} [CommRing A] [Algebra V A] (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp {A : Type} [CommRing A] [Algebra V A] (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem one_at_iff {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) : homAt (𝟙 (Sp V)) f ≫ y = 1 ↔ Chart.spMap f ≫ toSp y = 1 := by
  rw [eq_one_iff, eq_one_iff]
  have e : (spMap (algebraMap V B) ≫ 𝟙 (Sp V)) ≫ unitSec G = spMap (algebraMap V B) ≫ unitSec G := by
    rw [Category.comp_id]
  rw [e]
  rfl

theorem univ_over [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap q ≫ y = 1) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y.left = spMap (ψ : Jet V κ m →+* A) ≫ (x m).left := by
  obtain ⟨C⟩ := Chart.exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug : Jet V κ m →ₐ[V] V)
    (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (ker_aug_pow m) (toSp (x m)) ((one_at_iff _ _).1 (hx.2.1 m))
  have hk' : (x m).left = (Chart.pt C k).left := congrArg CommaMorphism.left hk
  have mv : ∀ {B : Type} [CommRing B] [Algebra V B] (v : Jet V κ m →ₐ[V] B),
      spMap (v : Jet V κ m →+* B) ≫ (x m).left = (Chart.pt C (v.comp k)).left := by
    intro B _ _ v
    rw [hk', ← Chart.spMap_pt]
    rfl
  let h₀ := fibLift q (Chart.eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ofSp (Chart.pt C h₀)) (by
    rw [one_at_iff]
    show Chart.spMap _ ≫ Chart.pt C h₀ = 1
    rw [Chart.spMap_pt]
    exact pt_eps_self C)
  have h0 : h₀ = ψ₀.comp k :=
    Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hψ₀).trans (mv ψ₀)))
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, fib_cond, ← AlgHom.comp_apply (fibFst q), ha, aug_X, map_zero]
  · rw [mv, AlgHom.comp_assoc, ← h0, hh]
    rfl
  · rintro v ⟨hv0, hv1⟩
    have hv : q.comp v = (Algebra.ofId V Ω).comp jetAug :=
      Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext fun i => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, hv0, aug_X, map_zero]
    have hvk : h = v.comp k :=
      Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hh).symm.trans (hv1.trans (mv v))))
    have e := hu (fibLift q jetAug v hv) ⟨rfl, Over.OverMorphism.ext (by
      refine Eq.trans ?_ (mv _).symm
      show (Chart.pt C h₀).left = _
      congr 2
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s)⟩
    rw [← e]
    rfl

theorem univ_left [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Sp A ⟶ G.left) (hw : y ≫ G.hom = spMap (algebraMap V A))
    (hy : spMap (q : A →+* Ω) ≫ y = spMap (algebraMap V Ω) ≫ unitSec G) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y = spMap (ψ : Jet V κ m →+* A) ≫ lft (x m) :=
  univ_over hx q hq hJ (Over.homMk y hw) ((eq_one_iff _).2 hy)

theorem aug_left {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) (A : Type) [CommRing A] [Algebra V A]
    (m : ℕ) : spMap (algebraMap V A) ≫ unitSec G =
      spMap (((Algebra.ofId V A).comp jetAug : Jet V κ m →ₐ[V] A) : Jet V κ m →+* A) ≫ lft (x m) := by
  have h2 : Chart.spMap ((Algebra.ofId V A).comp jetAug) ≫ toSp (x m) = 1 := by
    rw [← Chart.spMap_comp, Category.assoc, (one_at_iff _ _).1 (hx.2.1 m), MonObj.comp_one]
  exact ((eq_one_iff _).1 h2).symm

section Field

variable {Ω : Type} [Field Ω] [Algebra V Ω] {A : Type} [CommRing A] [Algebra Ω A] [Algebra V A] [IsScalarTower V Ω A]

theorem hom_eq : spMap (algebraMap Ω A) ≫ spMap (algebraMap V Ω) = spMap (algebraMap V A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem exists_jetHom {B : Type} [CommRing B] [Algebra V B] {m : ℕ} {I : Ideal B} (hI : I ^ (m + 1) = ⊥) (a : κ → B)
    (ha : ∀ i, a i ∈ I) : ∃ ψ : Jet V κ m →ₐ[V] B, ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i :=
  ⟨liftJet (MvPolynomial.aeval a) (by
      rw [eq_bot_iff, ← hI]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨i, rfl⟩
      simpa using ha i), fun i => MvPolynomial.aeval_X a i⟩

theorem universalJetCoordinates_points_over_field [IsLocalRing V] {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {P : PtFam (spMap (algebraMap V Ω)) G d}
    (hP : IsJetPt (algebraMap V Ω) x P) (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π)) :
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt (spMap (algebraMap V Ω)) A ⟶ G, homAt _ π ≫ z = 1 →
      ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z := by
  have hq : Function.Surjective (π.restrictScalars V) := fun r => ⟨algebraMap Ω A r, π.commutes r⟩
  obtain ⟨m, hm⟩ := hπ
  have hJ : RingHom.ker (π.restrictScalars V) ^ (m + 1) = ⊥ := by
    show RingHom.ker π ^ (m + 1) = ⊥
    rw [pow_succ, hm, zero_mul]
    rfl
  have hP' : ∀ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
      lft (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) =
        spMap (ψ : Jet V (Fin 1 × Fin d) m →+* A) ≫ lft (x m) := fun ψ =>
    hP A m (ψ : Jet V (Fin 1 × Fin d) m →+* A) fun v =>
      (ψ.commutes v).trans (IsScalarTower.algebraMap_apply V Ω A v)
  refine ⟨fun a ha h1 => ?_, fun z hz => ?_⟩
  · have ha0 : ∀ j, π.restrictScalars V (a j) = 0 := fun j => ((ha j).map (π.restrictScalars V)).eq_zero
    obtain ⟨ψ, hψ⟩ := exists_jetHom (V := V) hJ (fun p : Fin 1 × Fin d => a p.2) fun p => ha0 p.2
    have hl := hP' ψ
    rw [show (fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) = a from funext fun j => hψ _,
      (eq_one_iff _).1 h1, hom_eq] at hl
    have e := (univ_left hx _ hq hJ (spMap (algebraMap V A) ≫ unitSec G)
      (by rw [Category.assoc, unitSec_w, Category.comp_id])
      (by rw [← Category.assoc, spMap_comp_alg])).unique (y₁ := ψ)
      (y₂ := (Algebra.ofId V A).comp jetAug) ⟨fun i => by rw [hψ, ha0], hl⟩
      ⟨fun i => by rw [AlgHom.comp_apply, aug_X, map_zero, map_zero], aug_left hx A m⟩
    funext j
    have h3 := hψ (0, j)
    rw [e, AlgHom.comp_apply, aug_X, map_zero] at h3
    exact h3.symm
  · obtain ⟨ψ, ⟨h0, h1⟩, -⟩ := univ_left hx _ hq hJ (lft z) ((lft_w z).trans hom_eq) (by
      have h3 : spMap (π : A →+* Ω) ≫ lft z = _ := (eq_one_iff _).1 hz
      rw [hom_eq (A := Ω)] at h3
      exact h3)
    refine ⟨fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))), fun j => ⟨m + 1, ?_⟩,
      lft_inj ((hP' ψ).trans h1.symm)⟩
    have := Ideal.pow_mem_pow (RingHom.mem_ker.2 (h0 (0, j))) (m + 1)
    rwa [hJ, Ideal.mem_bot] at this

end Field

end GlobalTheory.AlphaPair.JetUniv

namespace GlobalTheory.AlphaPair

theorem jetUniv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  intro E _ _ _ H V _ _ t d x hx Ω _ β P hP A _ _ π hπ
  letI : Algebra V Ω := β.toAlgebra
  letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
  haveI : IsScalarTower V Ω A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact JetUniv.universalJetCoordinates_points_over_field hx hP π hπ

end GlobalTheory.AlphaPair
end
