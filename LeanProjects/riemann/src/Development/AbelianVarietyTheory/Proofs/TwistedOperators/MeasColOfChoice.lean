import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMeas

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_sub_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ v - v) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ v) := by
  have e3 : (frGL β y).1 = β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem mem_princGL_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ GlobalTheory.Grid.princGL β I ↔ x ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v - v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  rw [GlobalTheory.Grid.mem_princGL, ← stabilizer_eq_stabilizer_lattice F E n Λ β hfr]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨y, rfl⟩, fun v hv => ?_⟩
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I, frame_sub_eq]
    intro i
    have hw := (hfr v).1 hv
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun k => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hw k) ⟨_, hy i k, GlobalTheory.LevRedTriv.coe_sub_one_apply y i k⟩
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, rfl, fun i j => ?_⟩
    have h1 := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I _).1 (h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hfr j)) i
    have e : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [frame_sub_eq, e, Matrix.mulVec_single_one] at h1
    obtain ⟨s, hs, e⟩ := h1
    have : s = (y.1 - 1) i j := Subtype.ext (e.trans (GlobalTheory.LevRedTriv.coe_sub_one_apply y i j).symm)
    exact this ▸ hs

theorem princ_eq_congLev [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) :
    UA hc J ⊓ GlobalTheory.Grid.princGL β I = congLev hc J Λ I := by
  ext x
  rw [Subgroup.mem_inf, mem_princGL_iff hfr, mem_congLev]

end General

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

open GlobalTheory.GridJoin

theorem exists_measDat {D : D7} (N : GlobalTheory.Grid.Node D) {V : HSp D} (hsp : SameSp V N.V)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hlat : HEq N.Λ Λ) (hfr : IsFrame N.β N.Λ)
    (I : Ideal (𝓞 D.host.E)) {ν : Measure (GA D V)} {fd : Set (GA D V)}
    (hm : Lev.IsMeasFD V (congLev D.sp.cm V.gram Λ I) ν fd) :
    ∃ md : N.MeasDat, HEq md.ν ν ∧ HEq md.fd fd ∧ md.Is False (N.princ I) := by
  obtain ⟨L, h1, h2, e⟩ := hsp
  obtain ⟨V', S, M, Λ', β⟩ := N
  simp only at e hlat hfr ⊢
  subst e
  obtain rfl := eq_of_heq hlat
  refine ⟨⟨ν, fd⟩, HEq.rfl, HEq.rfl, fun h => h.elim, fun _ => ?_⟩
  unfold GlobalTheory.Grid.Node.princ
  rw [princ_eq_congLev _ _ hfr]
  exact hm

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

theorem measCol_of_choice : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
    (G : GlobalTheory.Grid.GridPre R), G.IsMeas → GlobalTheory.GridJoin.SpMatch G ch.W →
    (∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ) → ch.M.IsRow →
    ∃ (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat),
      (GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).IsMeas ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).ν (ch.M.ν (.grid i 0))) ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).fd (ch.M.fd (.grid i 0))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch G hG hsp hfr hrow
  have H : ∀ i, ∃ md : (G.V i 0).MeasDat, i ≤ D.R.m → HEq md.ν (ch.M.ν (.grid i 0)) ∧
      HEq md.fd (ch.M.fd (.grid i 0)) ∧ md.Is False ((G.V i 0).princ (G.lvl R)) := by
    intro i
    by_cases hi : i ≤ D.R.m
    · have hN := hsp.vert i 0 hi (Nat.zero_le _)
      have hr := hrow.row i hi
      have hne : GlobalTheory.ChiGrid.Node.neg D.R.m (.grid i 0) ≠ 0 := by
        simp only [GlobalTheory.ChiGrid.Node.neg, Nat.sub_zero]
        have := D.R.two_le_m
        omega
      unfold Vol.IsAt at hr
      rw [if_neg hne] at hr
      obtain ⟨md, h1, h2, h3⟩ := exists_measDat (G.V i 0) hN.sp hN.lat (hfr i hi) _ hr
      exact ⟨md, fun _ => ⟨h1, h2, hsp.lvl ▸ h3⟩⟩
    · exact ⟨G.measCol i, fun h => absurd h hi⟩
  choose f hf using H
  refine ⟨f 0, fun i j => match j with | 0 => f (i + 1) | j + 1 => G.mV i (j + 1),
    ⟨fun i hi => ?_, fun i j hi hj => hG.vert i j hi hj, hG.P, hG.X⟩, fun i hi => ?_, fun i hi => ?_⟩
  · cases i <;> exact (hf _ hi).2.2
  · cases i <;> exact (hf _ hi).1
  · cases i <;> exact (hf _ hi).2.1

end GlobalTheory.ColMeas

end
