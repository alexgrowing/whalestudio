import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts

section Field

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (φ : F →+* ℂ_[p])

theorem norm_int_le_one (a : 𝓞 F) : ‖φ (a : F)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (φ (a : F)) := by
    convert map_isIntegral_int φ a.isIntegral_coe
    exact Subsingleton.elim _ _
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (φ (a : F)) := hx.tower_top
  have h3 : ‖φ (a : F)‖₊ ≤ 1 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  exact_mod_cast h3

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']
  exact Padic.norm_p_lt_one

def placeAt [NumberField F] : HeightOneSpectrum (𝓞 F) where
  asIdeal :=
    { carrier := {a | ‖φ (a : F)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        have e : ((a + b : 𝓞 F) : F) = (a : F) + (b : F) := by simp
        simp only [Set.mem_ofPred_eq, e, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have e : ((c * a : 𝓞 F) : F) = (c : F) * (a : F) := by simp
        simp only [Set.mem_ofPred_eq, smul_eq_mul, e, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one φ c)).trans_lt ha }
  isPrime :=
    { ne_top' := fun h => by
        have h1 := (Ideal.eq_top_iff_one _).1 h
        change ‖φ ((1 : 𝓞 F) : F)‖ < 1 at h1
        simp at h1
      mem_or_mem' := fun {a b} h => by
        change ‖φ ((a * b : 𝓞 F) : F)‖ < 1 at h
        change ‖φ (a : F)‖ < 1 ∨ ‖φ (b : F)‖ < 1
        have e : ((a * b : 𝓞 F) : F) = (a : F) * (b : F) := by simp
        rw [e, map_mul, norm_mul] at h
        by_contra hn
        rw [not_or, not_lt, not_lt] at hn
        exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2)) }
  ne_bot := fun h => by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := by
      rw [← h]
      change ‖φ (((p : ℕ) : 𝓞 F) : F)‖ < 1
      have e : (((p : ℕ) : 𝓞 F) : F) = (p : F) := by simp
      rw [e, map_natCast]
      exact norm_p_lt_one
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 h1))

theorem mem_placeAt [NumberField F] (a : 𝓞 F) : a ∈ (placeAt φ).asIdeal ↔ ‖φ (a : F)‖ < 1 := Iff.rfl

theorem natCast_mem_placeAt [NumberField F] : ((p : ℕ) : 𝓞 F) ∈ (placeAt φ).asIdeal := by
  have e : (((p : ℕ) : 𝓞 F) : F) = (p : F) := by simp
  rw [mem_placeAt, e, map_natCast]
  exact norm_p_lt_one

def kurC : Subfield ℂ_[p] := (φ.fieldRange ⊔ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p).topologicalClosure

theorem mem_kurC (a : F) : φ a ∈ kurC φ :=
  Subfield.le_topologicalClosure _ ((le_sup_left : φ.fieldRange ≤ _) ⟨a, rfl⟩)

theorem kur_le_kurC : Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ≤ kurC φ := le_sup_right.trans (Subfield.le_topologicalClosure _)

theorem root_mem_kurC {ζ : ℂ_[p]} {n : ℕ} (hn : ¬ p ∣ n) (h : ζ ^ n = 1) : ζ ∈ kurC φ :=
  kur_le_kurC φ (Subfield.le_topologicalClosure _ (Subfield.subset_closure
    ⟨n, Nat.pos_of_ne_zero fun h0 => hn (h0 ▸ dvd_zero p), hn, h⟩))

theorem kurC_congr {F' : Type} [Field F'] {φ' : F' →+* ℂ_[p]} (h : φ.fieldRange = φ'.fieldRange) : kurC φ = kurC φ' := by
  rw [kurC, kurC, h]

def PAt (_φ : F →+* ℂ_[p]) : Type := ℂ_[p]

instance : Field (PAt φ) := inferInstanceAs (Field ℂ_[p])
instance : IsAlgClosed (PAt φ) := inferInstanceAs (IsAlgClosed ℂ_[p])
instance : Algebra F (PAt φ) := φ.toAlgebra

def toCp : PAt φ →+* ℂ_[p] := RingHom.id ℂ_[p]

theorem toCp_algebraMap (a : F) : toCp φ (algebraMap F (PAt φ) a) = φ a := rfl

structure IsReading (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]) : Prop where
  comp : ∀ a, k (io a) = φ a
  int : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x

variable {φ} in

def IsReading.alg {T : CDVR} {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (h : IsReading φ T io k) :
    letI := io.toAlgebra; T.Fr →ₐ[F] PAt φ :=
  letI := io.toAlgebra
  { (show T.Fr →+* PAt φ from k) with commutes' := h.comp }

end Field

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p])

variable {Xo c φ} in

def IsReadPt {T : CDVR} {io : c.F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (h : IsReading φ T io k) (y : IntFr Xo c T io)
    (u : Ix Dw → (PAt φ)ˣ) (z : FrPt Xo c (PAt φ)) : Prop :=
  letI := io.toAlgebra
  ∃ w : FrPt Xo c (PAt φ), FrMap h.alg y.1 w ∧ FrBor u w z

variable {Xo c φ} in

def IsIntPt (z : FrPt Xo c (PAt φ)) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (k : T.Fr →+* ℂ_[p]) (h : IsReading φ T io k) (y : IntFr Xo c T io)
    (u : Ix Dw → (PAt φ)ˣ), y.IsAlg ∧ (∀ a, ‖toCp φ (u a)‖ = 1) ∧ IsReadPt h y u z

def PtC : Type := {z : FrPt Xo c (PAt φ) // IsIntPt z}

variable {Xo c φ}

def valC (z : FrPt Xo c (PAt φ)) (f : Rul Xo c) : ℂ_[p] := toCp φ (evR Xo c f z)

theorem valC_add (z : FrPt Xo c (PAt φ)) (f g : Rul Xo c) : valC z (f + g) = valC z f + valC z g :=
  evalAt_add _ _ f g z

theorem valC_smul (z : FrPt Xo c (PAt φ)) (a : c.F) (f : Rul Xo c) : valC z (a • f) = φ a * valC z f :=
  evalAt_smul _ _ a f z

theorem valC_zero (z : FrPt Xo c (PAt φ)) : valC z 0 = 0 := evalAt_zero _ _ z

theorem IsReadPt.valC {T : CDVR} {io : c.F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} {h : IsReading φ T io k} {y : IntFr Xo c T io}
    {u : Ix Dw → (PAt φ)ˣ} {z : FrPt Xo c (PAt φ)} (hz : IsReadPt h y u z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : valC z f = toCp φ (wchar (ex Dw a n) u) * k (evI y f) := by
  letI := io.toAlgebra
  have hL : GlobalTheory.Reg.EvLaws Xo c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).1
  obtain ⟨w, hw, hb⟩ := hz
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test _ y.1
  have e1 : evR Xo c f w = k (evI y f) := by
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (h.alg.comp χ) y₀ w (PullbackSections.frMap_trans χ h.alg hy₀ hw)]
    exact congrArg k (GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ y.1 hy₀).symm
  rw [GeoTie.valC, hL.wt a n f hf _ u w z (hL.test _ _) (hL.test _ _) hb, map_mul, e1]
  rfl

theorem norm_wchar {u : Ix Dw → (PAt φ)ˣ} (hu : ∀ a, ‖toCp φ (u a)‖ = 1) (e : Ix Dw → ℕ) : ‖toCp φ (wchar e u)‖ = 1 := by
  simp [wchar, norm_prod, hu]

theorem PtC.exists_valC (z : PtC Xo c φ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (k : T.Fr →+* ℂ_[p]) (_ : IsReading φ T io k) (y : IntFr Xo c T io) (u : ℂ_[p]),
      y.IsAlg ∧ ‖u‖ = 1 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * k (evI y f) := by
  obtain ⟨T, io, k, h, y, u, hy, hu, hz⟩ := z.2
  exact ⟨T, io, k, h, y, _, hy, norm_wchar hu _, fun f hf => hz.valC hf⟩

theorem PtC.exists_of_reading {T : CDVR} {io : c.F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (h : IsReading φ T io k)
    (y : IntFr Xo c T io) (hy : y.IsAlg) :
    ∃ z : PtC Xo c φ, ∀ a n, ∀ f ∈ sec Xo c a n, valC z.1 f = k (evI y f) := by
  letI := io.toAlgebra
  obtain ⟨w, hw⟩ := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).1.bc _ _ h.alg y.1
  have hb : FrBor 1 w w :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ w w w).1 1).2 ⟨fun _ => 1, fun _ _ _ h => Matrix.one_apply_ne h.ne,
      fun _ _ => Matrix.one_apply_eq _, (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ w w w).1⟩
  have hr : IsReadPt h y 1 w := ⟨w, hw, hb⟩
  refine ⟨⟨w, T, io, k, h, y, 1, hy, fun a => by simp, hr⟩, fun a n f hf => ?_⟩
  rw [hr.valC hf]
  simp [wchar]

abbrev HkKer (𝔓 : Ideal (𝓞 E)) (q i : ℕ) (z : FrPt Xo c (PAt φ)) : Type := hkKer (Xo := Xo) 𝔓 q i (PAt φ) z

def IsHkQuot (𝔓 : Ideal (𝓞 E)) (q i : ℕ) (z : FrPt Xo c (PAt φ)) (C : HkKer 𝔓 q i z) (z' : FrPt Xo c (PAt φ)) : Prop :=
  hkRelFr 𝔓 q i (GlobalTheory.ThetaTrace.hkTr Xo c q) (PAt φ) z C z'

end Points

example (p : ℕ) [Fact p.Prime] : ((p : ℕ) : 𝓞 ℚ) ∈ (placeAt (Rat.castHom ℂ_[p])).asIdeal ∧
    (1 : 𝓞 ℚ) ∉ (placeAt (Rat.castHom ℂ_[p])).asIdeal :=
  ⟨natCast_mem_placeAt _, by simp [mem_placeAt]⟩

end GlobalTheory.GeoTie

end
