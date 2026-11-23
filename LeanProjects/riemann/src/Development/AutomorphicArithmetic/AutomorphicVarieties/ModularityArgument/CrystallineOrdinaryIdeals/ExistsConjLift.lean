import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementNotMemMinimalPrimesReducedOrdinStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryComponentUniquePrimeDimThirteenNearBaseStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ReducedOrdinaryIdealLeKerOfConjOfSaturatingNeZerStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.RootConjugation

private theorem map_conj {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (h : GL (Fin 3) A)
    (r : G →* GG 3 A) (g : G) :
    GG.map f (conjBy h r g) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) * GG.map f (r g) *
      (GG.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹ := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  have e2 : conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl
  rw [e2, map_mul, map_mul, map_inv, e]

private theorem push_conj {O A B G : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [Group G] (f : A →ₐ[O] B) (h : GL (Fin 3) A) (r : G →* GG 3 A) :
    push f (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map (f : A →+* B) h) (push f r) :=
  MonoidHom.ext fun g => map_conj _ h r g

private theorem conjBy_one {A G : Type} [CommRing A] [Group G] (r : G →* GG 3 A) : conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  have e2 : conjBy 1 r g = GG.ofGL 1 * r g * (GG.ofGL 1)⁻¹ := rfl
  rw [e2, map_one, one_mul, inv_one, mul_one]

private theorem exists_conjLift {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) (h : GL (Fin 3) R) (hh : CongOne (maximalIdeal R) h) :
    ∃ r' : GLift O η Ψ R, r'.hom = conjBy h r.hom := by
  refine ⟨⟨conjBy h r.hom, fun a b N => ?_, fun g => ?_⟩, rfl⟩
  · have h1 : IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ N)) (r.hom g) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have h2 : ∀ᶠ y in nhds x, ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ N) ((r.hom y).mat a b) =
          Ideal.Quotient.mk (maximalIdeal R ^ N) ((r.hom x).mat a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (r.cont a b N).eventually_eq x
      filter_upwards [h2, hη.eventually_eq x] with y h3 h4
      refine SemidirectProduct.ext (Units.ext (Matrix.ext h3)) ?_
      rw [GG.map_right, GG.map_right, r.hasMult y, r.hasMult x, h4]
    have h5 := h1.comp fun z => GG.mat (GG.ofGL (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk _) h) * z *
      (GG.ofGL (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk _) h))⁻¹) a b
    convert h5 using 2 with g
    rw [Function.comp_apply, ← map_conj]
    rfl
  · have e : Matrix.GeneralLinearGroup.map (res O R : R →+* ResidueField O) h = 1 := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      have h1 := (res_eq_zero_iff O R _).2 (hh a b)
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
      refine h1.trans ?_
      simp only [Matrix.one_apply, Units.val_one]
      split_ifs <;> simp
    rw [map_conj, e, map_one, one_mul, inv_one, mul_one, r.red]

private theorem eta_lc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) : IsLocallyConstant D.η := by
  haveI := D.Kv.2
  have ho : IsOpen (GK D.Kv : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen D.Kv.1
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (GK D.Kv : Set (GQ l)), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have h1 := (D.η_ker _).2 hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

private theorem exists_univMat (R : Type) [CommRing R] :
    ∃ h : GL (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R), ∀ a b,
      h.val a b = (1 : Matrix (Fin 3) (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R)) a b + MvPowerSeries.X (a, b) := by
  let M : Matrix (Fin 3) (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R) := 1 + Matrix.of fun a b => MvPowerSeries.X (a, b)
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (MvPowerSeries.constantCoeff (σ := Fin 3 × Fin 3) (R := R)).mapMatrix M = 1 := by
      rw [map_add, map_one]
      ext a b
      simp
    rw [this, Matrix.det_one]
    exact isUnit_one
  exact ⟨hM.unit, fun a b => rfl⟩

private theorem gl_ext {S C : Type} [CommRing S] [CommRing C] (F : S →+* C) (u : GL (Fin 3) S) (h : GL (Fin 3) C)
    (x : Fin 3 × Fin 3 → S) (hu : ∀ a b, (u : Matrix (Fin 3) (Fin 3) S) a b = (1 : Matrix (Fin 3) (Fin 3) S) a b + x (a, b))
    (hx : ∀ a b, F (x (a, b)) = ((h : Matrix (Fin 3) (Fin 3) C) - 1) a b) :
    Matrix.GeneralLinearGroup.map F u = h := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  show F ((u : Matrix (Fin 3) (Fin 3) S) a b) = _
  rw [hu, map_add, hx, Matrix.sub_apply]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.OrdLoc.RootConjugation

open GlobalTheory.OrdLoc.RootConjugation in

theorem GlobalTheory.OrdLoc.rtConj :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (r : GQ l →* GG 3 C) (h : GL (Fin 3) C), UpperTheory.V.UnitaryThreeInertia.InHat h → GlobalTheory.OrdLoc.On D U r → GlobalTheory.OrdLoc.On D U (conjBy h r) := by
  intro hP l _ O _ _ _ _ _ _ _ D U C _ _ _ r h hh hr
  obtain ⟨f, rfl, hf⟩ := hr
  obtain ⟨hpr, hprime, hl, hIt, -, -, -⟩ := GlobalTheory.T.ordinaryComponent_unique_prime_dim_thirteen_near_base hP D U
  have hmin : GlobalTheory.OrdLoc.It D U ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes := by
    have : GlobalTheory.OrdLoc.It D U ∈ GlobalTheory.OrdLoc.primesAt0 D U := by rw [hpr]; rfl
    exact this.1
  haveI := hprime
  let q : U.R →ₐ[O] GlobalTheory.OrdLoc.Rt D U := Ideal.Quotient.mkₐ O (GlobalTheory.OrdLoc.It D U)
  haveI : IsCO O (GlobalTheory.OrdLoc.Rt D U) := co_quot O U.R _ q (Ideal.Quotient.mkₐ_surjective O _)
  let S := MvPowerSeries (Fin 3 × Fin 3) (GlobalTheory.OrdLoc.Rt D U)
  haveI : IsCO O S := co_mvps O _ _
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  let i : U.R →ₐ[O] S := (IsScalarTower.toAlgHom O (GlobalTheory.OrdLoc.Rt D U) S).comp q
  have hi : ∀ a, i a = MvPowerSeries.C (q a) := fun a => rfl
  have hiI : ∀ a ∈ GlobalTheory.OrdLoc.It D U, i a = 0 := fun a ha => by
    rw [hi, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  obtain ⟨u, hu⟩ := exists_univMat (GlobalTheory.OrdLoc.Rt D U)
  have hu1 : CongOne (maximalIdeal S) u := fun a b => by
    rw [Matrix.sub_apply, hu, add_sub_cancel_left]
    intro hx
    have := MvPowerSeries.isUnit_constantCoeff _ hx
    simp at this
  obtain ⟨r', hr'⟩ := exists_conjLift (eta_lc D) (U.r.map i) u hu1
  obtain ⟨α, hα, -⟩ := (U.rep S).2 r' trivial
  have hα' : push α U.r.hom = conjBy u (push i U.r.hom) := (congrArg GLift.hom hα).trans hr'
  have hcomp : ∀ {T : Type} [CommRing T] [Algebra O T] (y : S →ₐ[O] T), push (y.comp α) U.r.hom =
      conjBy (Matrix.GeneralLinearGroup.map (y : S →+* T) u) (push (y.comp i) U.r.hom) := fun y => by
    show push y (push α U.r.hom) = _
    rw [hα', push_conj]
    rfl
  have hIY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker i := fun a ha =>
    hiI a (hIt (Ideal.le_radical ha))
  have hdel : i (GlobalTheory.OrdLoc.del D U.r.hom) ≠ 0 := by
    rw [hi]
    intro h0
    have h1 : q (GlobalTheory.OrdLoc.del D U.r.hom) = 0 := by
      have := congrArg MvPowerSeries.constantCoeff h0
      simpa using this
    exact GlobalTheory.T.saturatingElement_notMem_minimalPrimes_reducedOrdinaryIdeal D U _ hmin (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h1 : GlobalTheory.OrdLoc.Icr D U ≤ RingHom.ker α := GlobalTheory.T.reducedOrdinaryIdeal_le_ker_of_conj_of_saturating_ne_zero D U S i α u hα' hIY hdel
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := co_ev O (GlobalTheory.OrdLoc.Rt D U) (GlobalTheory.OrdLoc.Rt D U) (Fin 3 × Fin 3) (AlgHom.id O _) 0 fun _ => zero_mem _
  have h2 : c.comp α = q := by
    have e1 : c.comp i = q := AlgHom.ext fun a => hc1 _
    refine ((U.rep (GlobalTheory.OrdLoc.Rt D U)).2 (U.r.map q) trivial).unique (GLift.ext ?_) rfl
    show push (c.comp α) U.r.hom = push q U.r.hom
    rw [hcomp, e1, gl_ext (c : S →+* GlobalTheory.OrdLoc.Rt D U) u 1 _ hu fun a b => (hc2 _).trans (by simp), conjBy_one]
  have h3 : RingHom.ker α ≤ GlobalTheory.OrdLoc.It D U := fun a ha => by
    have : q a = 0 := by
      rw [← h2, AlgHom.comp_apply, show α a = 0 from ha, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have h4 : GlobalTheory.OrdLoc.It D U ≤ RingHom.ker α := hmin.2 ⟨RingHom.ker_isPrime α, h1⟩ h3
  obtain ⟨F, ⟨hF1, hF2⟩, -⟩ := co_ev O (GlobalTheory.OrdLoc.Rt D U) C (Fin 3 × Fin 3) (Ideal.Quotient.liftₐ (GlobalTheory.OrdLoc.It D U) f fun a ha => hf ha)
    (fun s => ((h : Matrix (Fin 3) (Fin 3) C) - 1) s.1 s.2) fun s => hh s.1 s.2
  refine ⟨F.comp α, ?_, fun a ha => ?_⟩
  · have e1 : F.comp i = f := AlgHom.ext fun a => hF1 _
    rw [hcomp, e1, gl_ext (F : S →+* C) u h _ hu fun a b => hF2 _]
  · show F (α a) = 0
    rw [show α a = 0 from h4 ha, map_zero]
