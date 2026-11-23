import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CardLeOfLinearIndependentTheta

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

instance neZero_level_A : NeZero l.A := ⟨l.A_pos.ne'⟩

instance neZero_level_M : NeZero l.M := ⟨by have := l.three_le; omega⟩

theorem AnArc.exists_rep {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] :
    ∃ (C : Type) (_ : Fintype C) (rep : C → A.X), ∀ α₀, ∃! t, ∃ mu, rep t = α₀ + j • mu := by
  classical
  set S : Submodule ℤ A.X := LinearMap.range ((j : ℤ) • LinearMap.id) with hS
  have hmem : ∀ mu : A.X, j • mu ∈ S := fun mu => ⟨mu, by simp⟩
  have htor : Module.IsTorsion ℤ (A.X ⧸ S) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective S q
    refine ⟨⟨(j : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne j)⟩, ?_⟩
    show (j : ℤ) • Submodule.Quotient.mk x = (0 : A.X ⧸ S)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, natCast_zsmul]
    exact hmem x
  have : Finite (A.X ⧸ S) := Module.finite_of_fg_torsion _ htor
  refine ⟨A.X ⧸ S, Fintype.ofFinite _, fun t => Quotient.out t, fun α₀ => ⟨Submodule.Quotient.mk α₀, ?_, ?_⟩⟩
  · have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk α₀ : A.X ⧸ S)) =
        (Submodule.Quotient.mk α₀ : A.X ⧸ S) := Quotient.out_eq _
    rw [Submodule.Quotient.eq] at h
    obtain ⟨mu, hmu⟩ := h
    refine ⟨mu, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hmu
    rw [hmu]; abel
  · rintro t ⟨mu, hmu⟩
    have hmu' : Quotient.out t = α₀ + j • mu := hmu
    have h : (Submodule.Quotient.mk (Quotient.out t) : A.X ⧸ S) = t := Quotient.out_eq _
    rw [← h, hmu', Submodule.Quotient.eq, add_sub_cancel_left]
    exact hmem mu

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

structure GtAn₀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ}
    (a : ArcIn D l β ℂ b) extends @GtDict (𝓞 E) _ H.starRing _ _ a.D₀ a.mod a.oa where

  be_eq : letI := H.starRing; ∀ x y, a.be (eX x) (eX y) = A.be x y

structure GtAn [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ}
    (a : ArcIn D l β ℂ b) extends GtAn₀ a where

  sec : letI := H.starRing; toGtAn₀.toGtDict.SecFn

def AnArc.ofForm (O : Type) [CommRing O] [StarRing O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [Module O X] (be : LinearMap.BilinForm ℤ X) (symm : ∀ x y, be x y = be y x) (pos : ∀ x, x ≠ 0 → 0 < be x x)
    (adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (even : ∀ x, (2 : ℤ) ∣ be x x) : AnArc O where
  gB := 0
  abelian₂ := ⊥
  discrete := inferInstance
  full := Subsingleton.elim _ _
  Hm := 0
  Hm_herm := Matrix.isHermitian_zero
  Hm_pos z hz := absurd (Subsingleton.elim _ _) hz
  Ef := 0
  Ef_eq l m := by simp [hermForm]
  Ef_bij := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  chi _ := 1
  chi_norm _ := norm_one
  chi_add l m := by simp [hermForm]
  chi_neg _ := rfl
  F := ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩
  F_mem a l _ := Subsingleton.elim (α := Fin 0 → ℂ) _ _
  F_adj a z w := by simp [hermForm]
  X := X
  ct := 0
  ct_smul _ _ := Subsingleton.elim _ _
  T := 0
  T_symm _ _ := rfl
  T_adj _ _ _ := rfl
  psi _ := 1
  psi_neg _ := rfl
  psi_add _ _ := by simp
  be := be
  be_symm := symm
  be_pos := pos
  be_adj := adj
  be_even := even

theorem nonempty_gtAn_of_toric {b : O →+* ℂ} (a : ArcIn D l β ℂ b) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (hD : a.D₀ = ToricData.toricPre ℂ X fun _ => 1) : Nonempty (GtAn a) := by
  letI := H.starRing
  obtain @⟨D₀, mod, oa, nontriv, even, bimult, gen, w0, be, be_symm, be_pos, be_adj, be_dvd, eta, etaA, geom⟩ := a
  dsimp only at hD
  subst hD
  letI : Module (𝓞 E) X := mod
  have heven : ∀ x : X, (2 : ℤ) ∣ be x x := fun x => dvd_trans (dvd_mul_right 2 _) (be_dvd x x)
  have hadj : ∀ (r : 𝓞 E) (y x : X), be (r • y) x = be y (star r • x) := be_adj
  let A : AnArc (𝓞 E) := AnArc.ofForm (𝓞 E) X be be_symm be_pos hadj heven
  let q : A.X → (FractionRing ℂ)ˣ := fun _ => 1
  have hq : ∀ x, algebraMap (FractionRing ℂ) ℂ (q x) = A.psi x := fun x => by
    simp [q, A, AnArc.ofForm]
  have h : ∀ (r : 𝓞 E) (y z : A.X), ToricData.polar q (r • y) z = ToricData.polar q y (star r • z) :=
    fun _ _ _ => by simp [ToricData.polar, q]
  haveI : IsEmpty (Fin A.gB) := inferInstanceAs (IsEmpty (Fin 0))
  have hoa : oa = ToricData.toricOAct q (𝓞 E) h := by
    rcases oa with ⟨⟨⟨act, hom, one, mul, add⟩, rosati⟩, c_lin, tau_bal⟩
    have hact : act = (ToricData.toricOAct q (𝓞 E) h).onB.act := funext fun _ => toUnit_unique _ _
    subst hact
    rfl
  subst hoa
  exact ⟨{ toGtDict := ToricDict.dict A q hq h, be_eq := fun _ _ => rfl, sec := ToricDict.secFn A q hq h }⟩

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

example (τ₀ : ℂ) : ∃ (_ : Algebra (FractionRing ℂ) ℂ) (_ : IsScalarTower ℂ (FractionRing ℂ) ℂ),
    Nonempty (ToricDict.tate τ₀).SecFn :=
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  ⟨_, this, ⟨ToricDict.secFn (AnArc.tate τ₀) _ (ToricDict.algebraMap_psiFrac _) _⟩⟩

theorem nonempty_gtAn_arcIn (c : Coeff l) (bF : c.F →+* ℂ) : Nonempty (GtAn (HostModel.arcIn c ℂ bF)) :=
  nonempty_gtAn_of_toric (HostModel.arcIn c ℂ bF) (𝓞 E) rfl

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem exists_gtAn_arcIn : ∃ (_ : Algebra (FractionRing ℂ) ℂ) (_ : IsScalarTower ℂ (FractionRing ℂ) ℂ),
    Nonempty (GtAn (HostModel.arcIn (HostModel.coeff (HostModel.level HostModel.host 5 (by norm_num))) ℂ
      (HostModel.coeff _).F.val.toRingHom)) := by
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  exact ⟨inferInstance, inferInstance, nonempty_gtAn_arcIn _ _⟩

namespace GtAn₀

variable {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a)

def y : letI := H.starRing; Λ.A.La →ₗ[𝓞 E] a.D₀.X :=
  letI := H.starRing; Λ.eX.toLinearMap ∘ₗ Λ.A.yLin

@[simp] theorem y_apply : letI := H.starRing; ∀ la : Λ.A.La, Λ.y la = Λ.eX la.y := by
  letI := H.starRing
  intro la
  show Λ.eX (Λ.A.yLin la) = Λ.eX la.y
  rw [AnArc.yLin_apply]

theorem y_onto : Function.Surjective Λ.y := by
  letI := H.starRing
  intro x
  obtain ⟨la, hla⟩ := Λ.A.yLin_surjective (Λ.eX.symm x)
  refine ⟨la, ?_⟩
  rw [y_apply, ← AnArc.yLin_apply, hla, LinearEquiv.apply_symm_apply]

theorem ker_y : letI := H.starRing; ∀ v, (Λ.ex₀ v).IsZero ↔ ∃ la, Λ.y la = 0 ∧ v = Λ.A.P0 la := by
  letI := H.starRing
  intro v
  rw [Λ.ker v]
  simp only [y_apply, LinearEquiv.map_eq_zero_iff]

theorem shift_be : letI := H.starRing; ∀ (w : ℂ) (la : Λ.A.La),
    IsTorusPt (Λ.ex₀ (w • Λ.A.N la)) fun x => eTwoPi (w * a.be (Λ.y la) x) := by
  letI := H.starRing
  intro w la
  have h := Λ.toGtDict.shift w la
  convert h using 3 with x
  rw [y_apply, ← Λ.be_eq, LinearEquiv.apply_symm_apply]

theorem dvd_be : letI := H.starRing; ∀ x y, (2 * l.M' : ℤ) ∣ Λ.A.be x y := by
  letI := H.starRing
  intro x y
  rw [← Λ.be_eq]
  exact a.be_dvd _ _

theorem A_dvd_be : letI := H.starRing; ∀ x y, (l.A : ℤ) ∣ Λ.A.be x y := by
  letI := H.starRing
  intro x y
  have hA : l.A ∣ l.M' := Nat.dvd_lcm_right l.M l.A
  exact dvd_trans (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hA) 2) (Λ.dvd_be x y)

theorem M_dvd_be : letI := H.starRing; ∀ x y, (l.M : ℤ) ∣ Λ.A.be x y := by
  letI := H.starRing
  intro x y
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  exact dvd_trans (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hM) 2) (Λ.dvd_be x y)

def Lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing; Λ.A.La → Prop :=
  letI := H.starRing
  fun la => ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ (Λ.toGtDict.qk k la) q'

theorem exists_lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing
    ∃ la : Λ.A.La, ∀ la', Λ.Lifts p la' ↔ ∃ m, la' = la + k • m := by
  letI := H.starRing
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨q, hq, huniq⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) hf p
  obtain ⟨la, rfl⟩ := Λ.toGtDict.qk_surjective k q
  refine ⟨la, fun la' => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (Λ.toGtDict.qk_equiv_iff k la' la).1 (h _ hq)
    exact ⟨-m, by rw [hm, smul_neg, add_neg_cancel_right]⟩
  · rintro ⟨m, rfl⟩ q' hq'
    rw [huniq q' hq']
    exact TorusExt.equiv_symm a.bimult (Λ.toGtDict.qk_equiv_add k la m)

theorem y_of_lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing
    ∀ la : Λ.A.La, Λ.Lifts p la → ∃ z, p.y = Λ.y la + k • z := by
  letI := H.starRing
  intro la h
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨q, hq, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) hf p
  have hqy : q.y = p.y := by
    rw [(TorusExt.qkExt_iff a.bimult _ hf p q).1 hq, TorusExt.qkExt, TorusExt.qkMk_y]
  obtain ⟨z, hz, -⟩ := (TorusExt.equiv_iff a.bimult _ _).1 (h q hq)
  refine ⟨z, ?_⟩
  rw [← hqy, hz, Λ.toGtDict.qk_y, y_apply]

end GtAn₀

abbrev GtAn.fn {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (j : ℕ) [NeZero j] : letI := H.starRing
    ∀ α : Λ.A.X, a.D₀.SecB j (Λ.eX α) ≃ Λ.A.Theta j α :=
  letI := H.starRing; Λ.sec.fn j

end GlobalTheory
