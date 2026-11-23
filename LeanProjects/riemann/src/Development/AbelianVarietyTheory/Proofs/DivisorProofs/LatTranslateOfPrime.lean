import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesTranslationLatticeBoundedNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClass

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BigOn.Exp.TupLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AllPts (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}, PtAt ex Csz → Fin D.R.m → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz) (j : Fin D.R.m), p.Rows → More p → Q p j

open Classical in

def PlacesSt : Prop := AllPts fun {D _ _ _ _ _ _ _ ex _} p j => ∀ w : D.what₂.places.Pl, D.plEq w ∈ p.R.twPl →
  IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) →
  ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) →
  p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
    (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi →
  SplitSet (p.R.Q (p.R.mu (D.plEq w))) ∧
    (∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) ∧
    idem (p.R.Q (p.R.mu (D.plEq w))) + cA D (idem (p.R.Q (p.R.mu (D.plEq w)))) =
      idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q) +
        cA D (idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q))

open Classical in

def FlatSt : Prop := AllPts fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)) (ψ : Twist D Circle) (t : p.P.T),
  B.Good → BaseOf (R2 p) j B → ψ.Good → B.admitted ψ.Q → (R2 p).xi t = B.de.chi * ψ.chi →
  idem ((R2 p).Q t) + cA D (idem ((R2 p).Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) →
  ∃ (z : GA D (Vc D j)) (c : ℂ), SuppAt (idem ((R2 p).Q t)) (Vc D j) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) t) c ∧
    (princ B).vecFlat ψ = c • (R2 p).ωP j t (z⁻¹, 1) ((R2 p).vP j t)

def TraceSt : Prop := AllPts fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp →
  ∀ (i : D.ntw.Tw) (b : Bool) (ψ : Twist D Circle) (ω : PairRep (Vc D j) (Wc D j)), ψ.Good → (ρ.B i j b).admitted ψ.Q →
    (ρ.B i j b).IsWeil ψ.chi ω → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (series (ρ.B i j b).F ω ((princ (ρ.B i j b)).vecFlat ψ) h P) =
        series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat ψ) h P

def CoefSt : Prop := AllPts fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ c : ℂ, c ≠ 0 → IsScale p.R p.v₀ B c → ∀ u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ,
    (∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j _ τ) → ∀ O' : Subring ℂ, IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ h ∈ GfC (Vc D j), ∀ v, InCoefLat (R2 p) j h v →
      ∃ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h), (R2 p).ioP j (PiTensorProduct.tprod ℂ u) v = c • P

def SmallSt : Prop := AllPts fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ O O' : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ (h : GA D (Vc D j)), ∀ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h),
      P ∈ Submodule.span O' (B.coefLat (embLL0 D) (labLL0 D) O (finPt (Vc D j) h) : Set (PolF D (Wc D j).rank (Vc D j).rank))

section Units

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨u0, a, a1, a2⟩ := hu
  obtain ⟨v0, b, b1, b2⟩ := hv
  refine ⟨mul_ne_zero u0 v0, a + b, ?_, ?_⟩
  · rw [show (N : ℂ) ^ (a + b) * (u * v) = ((N : ℂ) ^ a * u) * ((N : ℂ) ^ b * v) by ring]; exact a1.mul b1
  · rw [show (N : ℂ) ^ (a + b) * (u * v)⁻¹ = ((N : ℂ) ^ a * u⁻¹) * ((N : ℂ) ^ b * v⁻¹) by rw [mul_inv]; ring]; exact a2.mul b2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨u0, a, a1, a2⟩ := hu
  exact ⟨inv_ne_zero u0, a, a2, by rwa [inv_inv]⟩

theorem unitOff_root {N n : ℕ} {u : ℂ} (hn : n ≠ 0) (hu : u ^ n = 1) : UnitOff N u := by
  refine ⟨fun h => ?_, 0, ?_, ?_⟩
  · rw [h, zero_pow hn] at hu; exact zero_ne_one hu
  · rw [pow_zero, one_mul]; exact IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [hu]; exact isIntegral_one)
  · rw [pow_zero, one_mul]; exact IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [inv_pow, hu, inv_one]; exact isIntegral_one)

variable {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem mem_of_integral {a : K} (h : IsIntegral ℤ a) : ∃ b : O, algebraMap O K b = a :=
  IsIntegrallyClosed.isIntegral_iff.1 (h.tower_top (A := O))

theorem mem_of_ringOfIntegers {F : Type} [Field F] (f : F →+* K) (a : 𝓞 F) : ∃ b : O, algebraMap O K b = f a :=
  mem_of_integral (a.isIntegral_coe.map f.toIntAlgHom)

theorem mem_of_unitOff (e : K →+* ℂ) {N : ℕ} (hN : IsUnit (N : O)) {a : K} (h : UnitOff N (e a)) :
    ∃ b : O, algebraMap O K b = a := by
  obtain ⟨-, n, h1, -⟩ := h
  have h2 : IsIntegral ℤ ((N : K) ^ n * a) := by
    rw [← isIntegral_algHom_iff e.toIntAlgHom e.injective]
    simpa using h1
  obtain ⟨b, hb⟩ := mem_of_integral (O := O) h2
  obtain ⟨v, hv⟩ := hN
  refine ⟨(v⁻¹ : Oˣ) ^ n * b, ?_⟩
  rw [map_mul, hb, ← map_natCast (algebraMap O K), ← hv, ← mul_assoc, ← map_pow, ← map_mul, ← mul_pow]
  simp

end Units

section Read

variable {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
  {L : Type} [Field L] [Algebra (D.ntw.O i) L] (e : L →+* ℂ) (he : ∀ c : D.ntw.O i, e (algebraMap _ L c) = ρ.eO i b c)

def rdL : L ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b →ₛₗ[e] (GA D (Wc D j) → ℂ) :=
  let φ : L ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (e a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun c a f => by
      change e (c • a) • rd f = e a • rd (c • f)
      rw [rd_smul, Algebra.smul_def c a, map_mul, he, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun c x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change e (c • a) • rd f = e c • e a • rd f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdL_tmul (a : L) (f : D.nexp.Fm i ((j : ℕ) + 1) b) : rdL rd e he (a ⊗ₜ f) = e a • rd f := rfl

include he in
theorem exists_coord (x : L ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) : ∃ c : _ → L,
    x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing (D.ntw.O i)) (D.nexp.Fm i ((j : ℕ) + 1) b) a := by
  set v := Module.finBasis (FractionRing (D.ntw.O i)) (D.nexp.Fm i ((j : ℕ) + 1) b)
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (D.ntw.O i)) fun c => v.repr f c
    choose y hy using hd
    have d0 : algebraMap (D.ntw.O i) L d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d
      (ρ.eO_injective i b (by rw [← he, h, map_zero, map_zero]))
    refine ⟨fun c => y c • ((algebraMap (D.ntw.O i) L d)⁻¹ * a), ?_⟩
    have e1 : (a ⊗ₜ[D.ntw.O i] f : L ⊗[D.ntw.O i] _) = ((algebraMap (D.ntw.O i) L d)⁻¹ * a) ⊗ₜ ((d : D.ntw.O i) • f) := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_inv_cancel_left₀ d0]
    rw [e1]
    conv_lhs => rw [← v.sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing (D.ntw.O i)) (y c), hy, smul_assoc]

theorem eq_smul_of_read (hF : Faithful rd) {x y : L ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b} {u : ℂ}
    (h : rdL rd e he x = u • rdL rd e he y) : x = 0 ∨ ∃ a : L, e a = u ∧ x = a • y := by
  obtain ⟨c, rfl⟩ := exists_coord e he x
  obtain ⟨c', rfl⟩ := exists_coord e he y
  have hl := Fintype.linearIndependent_iff.1 (hF _ _ (Module.finBasis (FractionRing (D.ntw.O i))
    (D.nexp.Fm i ((j : ℕ) + 1) b)).linearIndependent) (fun a => e (c a) - u * e (c' a)) (by
      simp only [map_sum, rdL_tmul, Finset.smul_sum, smul_smul] at h
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  by_cases h0 : ∀ a, c' a = 0
  · left
    refine Finset.sum_eq_zero fun a _ => ?_
    have := hl a
    rw [h0 a, map_zero, mul_zero, sub_zero, map_eq_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · obtain ⟨a, ha⟩ := not_forall.1 h0
    have hu : e (c a / c' a) = u := by
      rw [map_div₀, div_eq_iff ((map_ne_zero e).2 ha)]
      exact sub_eq_zero.1 (hl a)
    refine Or.inr ⟨c a / c' a, hu, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact e.injective (by rw [map_mul, hu]; exact sub_eq_zero.1 (hl k))

end Read

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

def genFns (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (ρ : Setup D.ntw) : Set (GA D (Wc D j) → ℂ) :=
  {g | ∃ s h P, ρ.IsDatum (c.twI w) j (c.sd w) s h P ∧
    g ∈ ρ.gens (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (GlobalTheory.TwistIndex.chosenChar c w) h P}

abbrev imO (c : NChoice D) (w : D.what₂.places.Pl) (e : FractionRing (c.Oe w) →+* ℂ) : Subring ℂ :=
  (e.comp (algebraMap (c.Oe w) (FractionRing (c.Oe w)))).range

variable {p w j}

theorem le_of_comb {ρ : Setup D.ntw} (hρ : ρ.Good) {ν : ℂ} {rd : Can p w j} (hc : IsCan p rd) (hR : RatAt p w j hρ ν)
    (hF : Faithful (rdAt p w j hρ ν)) (hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm)
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    {N : ℕ} (hN : IsUnit (N : ex.nch.Oe w)) {S : Set (Fin ((R2 p).nW j) → D.what₂.LL)}
    (hS : ∀ x ∈ S, ∃ u, UnitOff N u ∧ ∃ G ∈ Submodule.span (imO ex.nch w e) (genFns ex.nch w j ρ),
      ν⁻¹ • adForm (R2 p) j x (p.v₀ j _) = u • G) :
    Submodule.span (ex.nch.Oe w) (rd '' (Submodule.span (𝓞 D.what₂.LL) S : Set _)) ≤ twLat p w j hρ ν := by
  have hO : ∀ c : D.ntw.O (ex.nch.twI w), e (algebraMap _ _ c) = ρ.eO (ex.nch.twI w) (ex.nch.sd w) c := fun c => by
    rw [← hρ.ek_e _ _ (ex.nch.k' w), ← h2, ← IsScalarTower.algebraMap_apply (D.ntw.O (ex.nch.twI w)) _ (ex.nch.Oe w),
      ← IsScalarTower.algebraMap_apply]
  let Φ := rdL (rdAt p w j hρ ν) e hO
  have a1 : ∀ y, Φ (incl D.nexp (ex.nch.twI w) _ (ex.nch.sd w) (ex.nch.Oe w) (ex.nch.k' w) y) =
      rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a f => rw [rdK_tmul, ← h2]; rfl
  have a2 : ∀ G ∈ Submodule.span (imO ex.nch w e) (genFns ex.nch w j ρ), ∃ y ∈ twLat p w j hρ ν, Φ y = G := fun G hG => by
    induction hG using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨s, h, P, hd, hg⟩ := hg
      obtain ⟨y, hy⟩ := hR.2 s h P hd hg
      exact ⟨_, Submodule.subset_span ⟨y, ⟨s, h, P, hd, hy ▸ hg⟩, rfl⟩, (a1 y).trans hy⟩
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add _ _ _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩
    | smul c _ _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨_, c, rfl⟩ := c
      refine ⟨c • x, Submodule.smul_mem _ c hx, ?_⟩
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) c x, map_smulₛₗ]
      rfl
  have a3 : ∀ x, Φ (rd x) = ν⁻¹ • adForm (R2 p) j x (p.v₀ j _) := fun x => by
    obtain ⟨x, rfl⟩ := (p.nexp.fi j).e.surjective x
    let rd' : p.Sx.WL ((j : ℕ) + 1) →ₛₗ[ex.nch.embW w] Tgt ex w j := LinearMap.comp rd (p.nexp.fi j).e.toLinearMap
    change Φ (rd' x) = ν⁻¹ • evW p.nexp p.v₀ j x
    obtain ⟨n, bb, hbK, -, -, -, hsp⟩ := hK
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range bb) := hsp ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    rw [map_sum, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, map_smulₛₗ, h1, evW_smul, smul_comm ν⁻¹]
    congr 1
    refine (congrArg Φ (hc ⟨bb k, hbK k⟩)).trans ?_
    refine (rdL_tmul _ e hO _ _).trans ?_
    rw [map_one, one_smul]
    refine (realRd_tmul p.nexp p.v₀ hρ _ j _ ν 1 ⟨bb k, hbK k⟩).trans ?_
    rw [show ρ.e (ex.nch.twI w) (ex.nch.sd w) (1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) = 1 from map_one _, mul_one]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  change rd x ∈ twLat p w j hρ ν
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, G, hG, eq⟩ := hS x hx
    obtain ⟨y, hy, rfl⟩ := a2 G hG
    rcases eq_smul_of_read (rdAt p w j hρ ν) e hO hF ((a3 x).trans eq) with h0 | ⟨a, rfl, ha⟩
    · rw [h0]; exact zero_mem _
    · obtain ⟨b, rfl⟩ := mem_of_unitOff e hN hu
      rw [ha, algebraMap_smul]
      exact Submodule.smul_mem _ b hy
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    rw [show a • x = (a : D.what₂.LL) • x from rfl, map_smulₛₗ, ← hb, algebraMap_smul]
    exact Submodule.smul_mem _ b hx

end Point

section Move

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
include hρ

theorem lat_translate_of_prime {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) (hl : ∀ P ∈ Q, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    {h hQ : GA D (Vc D j)} (hsupp : SuppAt (idem Q) (Vc D j) hQ) {P} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    P ∈ ρ.lat i j b (ρ.eO i b).range (h * hQ) := by
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := GlobalTheory.LatCmpQ.latAt_translate_bounded D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (GlobalTheory.LatTranslate.normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.NabScale.nabAtr_smul_pow_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0
    (GlobalTheory.LatFull.latAt_isLattice D ρ hρ i j b h) (GlobalTheory.LatFull.latAt_isLattice D ρ hρ i j b (h * hQ)) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
    have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) :=
      Nat.Coprime.prod_right fun P hP => GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime i).out P (hl P hP)
    obtain ⟨u, hu⟩ := GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
    refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
    have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
    rw [← h1]
    exact map_units_inv (ρ.eO i b) u
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  refine GlobalTheory.LatTranslate.coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam le_rfl
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv (fun F hF => ?_) hP.2
  have := ha F hF
  rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]

theorem exists_rep (ψ : Twist D Circle) (h : GA D (Vc D j)) :
    ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (k : (ρ.B i j b).levJ ψ), SplitSet s ∧
      (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧ SuppAt (idem s) (Vc D j) h' ∧
      (ρ.B i j b).levLam ψ k = 1 ∧ finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (k : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS ψ)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k →
      FWT.fin (Vc D j) k ∈ ((ρ.B i j b).levLam ψ).ker.map ((ρ.B i j b).levJ ψ).subtype := fun k hk hc =>
    ⟨⟨finPt _ k, ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1⟩,
      Units.ext (((ρ.B i j b).levLam_finPt ψ _).trans (hK k hk hc).2), rfl⟩
  obtain ⟨h', ⟨hh', hs⟩, γ, ⟨_, k, hk, rfl⟩, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' (Nat.pos_of_ne_zero (hρ.bad_ne i)) (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  exact ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', by rw [idem_eq hP]; exact hsupp, hk, e⟩

theorem series_eq_gen {k Q ψ} (hok : IntegralHeckeForms.TwOK i k Q ψ) {ω : PairRep (Vc D j) (Wc D j)}
    (hω : (ρ.B i j b).IsWeil (ρ.tw i b k Q ψ).chi ω) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {P}
    (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) : ∃ s h' P', ρ.IsDatum i j b s h' P' ∧ ∃ g ∈ ρ.gens i j b k Q ψ h' P',
      ∃ a : D.ntw.Ok i k, series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P = ρ.eOk i b k a • g := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hok
  have hB := hρ.base i j b
  obtain ⟨γ, s, h', κ, h1, h2, h3, h4, h5, h6⟩ := exists_rep hρ i j b (ρ.tw i b k Q ψ) h
  have hP' : (ρ.B i j b).act (γ⁻¹ : GQ (Vc D j)) P ∈ ρ.lat i j b (ρ.eO i b).range h' := by
    have := Base.act_mem_coefLat hB.frame (hρ.isCoefRing i b) γ⁻¹ (finPt _ h) (κ⁻¹ : (ρ.B i j b).levJ (ρ.tw i b k Q ψ))
      (Base.mem_St_of_mem_levJ (κ⁻¹).2) hP
    rwa [h6, map_inv, Subgroup.coe_inv, show ∀ x y z : Bridge.Gf (Vc D j), x⁻¹ * (x * y * z) * z⁻¹ = y from fun x y z => by group]
      at this
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h')
  refine ⟨s, h', _, ⟨h1, h2, h3, h4, hP'⟩, _, ⟨1, fun a c => ?_, rfl⟩, ((u⁻¹ : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k), ?_⟩
  · rw [show Formalism.L2.Theta.mt (Vc D j) 1 - 1 = 0 from sub_self _, Matrix.zero_apply, mul_zero]
  · have law := GlobalTheory.TwTraceCx.dualLaw_kern hB (D.sp.V_sig _) ht hadm hω γ (finPt _ h') κ ((ρ.B i j b).act (γ⁻¹ : GQ (Vc D j)) P)
    have e1 : GlobalTheory.TwTraceCx.ratAct (ρ.B i j b) γ ((ρ.B i j b).act (γ⁻¹ : GQ (Vc D j)) P) = P := by
      change (ρ.B i j b).act γ ((ρ.B i j b).act (γ⁻¹ : GQ (Vc D j)) P) = P
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h5, ← h6, e1, GlobalTheory.TwTraceCx.kern, GlobalTheory.TwTraceCx.kern, GlobalTheory.TwTraceCx.lift_finPt _ hh, GlobalTheory.TwTraceCx.lift_finPt _ h3,
      Units.val_one, map_one, one_smul] at law
    rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul hB ht hadm (hρ.weil_base i j b) hω, law, smul_smul, map_units_inv, detChar, hu,
      inv_mul_cancel₀ ((u.isUnit.map (ρ.eOk i b k)).ne_zero), one_smul]

end Move

section Assembly

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem realTw_le (s1 : PlacesSt) (s2 : FlatSt) (s3 : TraceSt) (s4 : CoefSt) (s5 : SmallSt) (hr : p.Rows) (hm : More p)
    (hL : Links2 p) (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin p.R p.cG ρ) (hlev : ρ.LevelOf D.nexp)
    (hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)))
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    {ν : ℂ} (hν : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν) (hR : RatAt p w j hρ ν) {rd : Can p w j} (hc : IsCan p rd) :
    realTw p rd ≤ twLat p w j hρ ν := by
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hK := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)
  obtain ⟨Z⟩ := hm.2.2.series
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ ρ hρ _ j _ ν hν.1 hL.2.2.1
    p.charW.base.models.HW (Z.vec j) hK
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z, cz, hz, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  have hO' : IsCoefRing D.what₂.embLL (labLL D) (imO ex.nch w e) := by
    refine ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ?_⟩
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    exact ⟨b, by rw [RingHom.comp_apply, hb, h1]⟩
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hs
  refine le_of_comb hρ hc hR hF hK e h1 h2 hN ?_
  rintro x ⟨h, hh, v, hv, hx⟩
  obtain ⟨P, hP, hio⟩ := s4 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 c c0 hs u hu _ hO' h hh v hv
  have hP' := s5 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 _ _ (hρ.isCoefRing (ex.nch.twI w) (ex.nch.sd w)) hO' h P hP
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hzf
  refine ⟨ν⁻¹ * c * cz⁻¹, unitOff_mul (unitOff_root hn ?_) (unitOff_inv hcz),
    series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]
  · clear hP hio
    induction hP' using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨s, h', P', hd, g, hg, a, ea⟩ := series_eq_gen hρ _ j _ hok hω hhz (lat_translate_of_prime hρ _ j _ p1 p2 hz hQ)
      rw [ea]
      exact Submodule.smul_mem _ (⟨_, ⟨algebraMap _ _ a, h2 a⟩⟩ : imO ex.nch w e) (Submodule.subset_span ⟨s, h', P', hd, hg⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
    | smul a y _ hy =>
      rw [show a • y = (a : ℂ) • y from rfl, map_smul]
      exact Submodule.smul_mem _ a hy
  · have e1 : adForm (R2 p) j x (p.v₀ j _) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
        (ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v) :=
      ((congrArg (adForm (R2 p) j x) (funext hu)).symm.trans (hx u)).trans (one_smul _ _)
    have e2 : ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v = (c * cz⁻¹) •
        series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
            (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P := by
      rw [mul_comm, mul_smul, ← map_smul, ← hio]
      refine Eq.trans ?_ (congrArg (cz⁻¹ • ·) (hB0.series_eq_ser _ _ u (h * z) v)).symm
      rw [hfl]
      funext g
      have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z⁻¹ cz (inv_mem hzf) u (h * z) v g
      rw [mul_inv_cancel_right] at e3
      refine Eq.trans ?_ (congrArg (cz⁻¹ * ·) e3).symm
      exact (inv_mul_cancel_left₀ hcz.1 _).symm
    rw [e1, e2, map_smul, s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, smul_smul, mul_assoc]

end Assembly

end GlobalTheory.BigOn.Exp.TupLe

end
