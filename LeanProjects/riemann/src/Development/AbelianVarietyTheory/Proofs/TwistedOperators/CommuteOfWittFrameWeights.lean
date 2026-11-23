import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Cusp.WeightCommute

open Matrix

variable {D : D7} {V : HSp D}

theorem ratAct_mul' (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one' (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem hT_ratAct (γ : GF V) (a b : V.V) :
    V.hT (GlobalTheory.Cusp.ratAct D.sp.cm V γ a) (GlobalTheory.Cusp.ratAct D.sp.cm V γ b) = V.hT a b := by
  have hγ : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hc : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 = Matrix.conjTranspose γ.1.1 := by
    ext i j; rfl
  rw [hc] at hγ
  have hr : ∀ w, V.frame.repr (GlobalTheory.Cusp.ratAct D.sp.cm V γ w) = γ.1.1 *ᵥ V.frame.repr w := fun w => by
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
  have hform : ∀ x y : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, hr, hr, hform, hform, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hγ]

theorem hT_frame (Φ : WittFrame V) (i j : Fin (wittIndex V)) :
    V.hT (Φ.f j) (Φ.e i) = (if i = j then 1 else 0) ∧ V.hT (Φ.e j) (Φ.f i) = (if i = j then 1 else 0) ∧
    V.hT (Φ.e j) (Φ.e i) = 0 ∧ V.hT (Φ.f j) (Φ.f i) = 0 := by
  refine ⟨Φ.ef i j, ?_, Φ.ee i j, Φ.ff i j⟩
  rw [← V.herm.eq (Φ.f i) (Φ.e j)]
  have h : V.hT (Φ.f i) (Φ.e j) = if j = i then 1 else 0 := Φ.ef j i
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

end GlobalTheory.Cusp.WeightCommute

open GlobalTheory.Cusp.WeightCommute in

theorem GlobalTheory.Cusp.WeightCommute.commute_of_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  intro D V Φ u γ g t h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin (wittIndex V) → V.V, ∀ i, xv i = if u i = 1 then Φ.e i else Φ.f i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : Fin (wittIndex V) → V.V, ∀ i, yv i = if u i = 1 then Φ.f i else Φ.e i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (wittIndex V)), ∀ i, i ∈ S ↔ u i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => u i ≠ 0), fun i => by simp⟩
  have hsgn : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  have hne : (-1 : SignType) ≠ 1 := by decide
  have hs : ∀ i ∈ S, u i = 1 ∨ u i = -1 := fun i hi => hsgn _ ((hS i).1 hi)
  have key := hT_frame Φ
  have neq : ∀ i j, u i = 1 → u j = -1 → i ≠ j := by
    rintro i j a b rfl; rw [a] at b; exact hne b.symm

  have mx : ∀ i ∈ S, xv i ∈ Φ.sub u := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hxv, if_pos a]; exact Submodule.subset_span (Or.inl ⟨i, a, rfl⟩)
    · rw [hxv, if_neg (by rw [a]; exact hne)]; exact Submodule.subset_span (Or.inr ⟨i, a, rfl⟩)
  have my : ∀ i ∈ S, yv i ∈ Φ.sub (-u) := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hyv, if_pos a]
      exact Submodule.subset_span (Or.inr ⟨i, show -(u i) = -1 by rw [a], rfl⟩)
    · rw [hyv, if_neg (by rw [a]; exact hne)]
      exact Submodule.subset_span (Or.inl ⟨i, show -(u i) = 1 by rw [a]; rfl, rfl⟩)

  have genX : ∀ z, (∀ i ∈ S, V.hT (xv i) z = 0) → ∀ w ∈ Φ.sub u, V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub u ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = 1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_pos (show u i = 1 from hi)] at this
        exact this
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = -1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_neg (by rw [show u i = -1 from hi]; exact hne)] at this
        exact this
    exact hle hw
  have genY : ∀ z, (∀ i ∈ S, V.hT (yv i) z = 0) → ∀ w ∈ Φ.sub (-u), V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have a : u i = -1 := neg_eq_iff_eq_neg.1 (show -(u i) = 1 from hi)
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_neg (by rw [a]; exact hne)] at this
        exact this
      · have a : u i = 1 := by
          have h' : -(u i) = -1 := hi
          simpa using h'
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_pos a] at this
        exact this
    exact hle hw

  have pxx : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (xv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.1
    · rw [(key i j).1, if_neg (neq i j a b)]
    · rw [(key i j).2.1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.2
  have pyy : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (yv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.2
    · rw [(key i j).2.1, if_neg (neq i j a b)]
    · rw [(key i j).1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.1
  have pyx : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (xv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).1
    · rw [(key i j).2.2.1, if_neg (neq i j a b)]
    · rw [(key i j).2.2.2, if_neg (neq j i b a).symm]
    · exact (key i j).2.1
  have pxy : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (yv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.1
    · rw [(key i j).2.2.2, if_neg (neq i j a b)]
    · rw [(key i j).2.2.1, if_neg (neq j i b a).symm]
    · exact (key i j).1

  have decomp : ∀ v : V.V, ∃ x ∈ Φ.sub u, ∃ y ∈ Φ.sub (-u), ∃ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) ∧
      (∀ w ∈ Φ.sub (-u), V.hT w z = 0) ∧ v = x + y + z := by
    intro v
    refine ⟨∑ i ∈ S, V.hT (yv i) v • xv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (mx i hi)),
      ∑ i ∈ S, V.hT (xv i) v • yv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (my i hi)),
      v - (∑ i ∈ S, V.hT (yv i) v • xv i) - ∑ i ∈ S, V.hT (xv i) v • yv i, genX _ ?_, genY _ ?_, by abel⟩
    · intro j hj
      rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pxx i hi j hj, smul_zero]),
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pxy i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        map_smul, pxy j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp
    · intro j hj
      rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pyx i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pyy i hi j hj, smul_zero]),
        map_smul, pyx j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp

  have inv_app : ∀ w, GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ w) = w := by
    intro w; rw [← ratAct_mul', mul_inv_cancel, ratAct_one']
  have zX : ∀ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) →
      ∀ w ∈ Φ.sub u, V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h3 w hw)
  have zY : ∀ z, (∀ w ∈ Φ.sub (-u), V.hT w z = 0) →
      ∀ w ∈ Φ.sub (-u), V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h4 w hw)
  have hmat : (g * γ).1.1 = (γ * g).1.1 := by
    apply (Matrix.toLin V.frame V.frame).injective
    apply LinearMap.ext
    intro v
    show GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ) v = GlobalTheory.Cusp.ratAct D.sp.cm V (γ * g) v
    rw [ratAct_mul', ratAct_mul']
    obtain ⟨x, hx, y, hy, z, hzX, hzY, rfl⟩ := decomp v
    simp only [map_add]
    rw [h5 _ (h1 x hx), h6 _ (h2 y hy), h7 _ (zX z hzX) (zY z hzY), h5 x hx, h6 y hy, h7 z hzX hzY,
      map_smul, map_smul]
  exact Subtype.ext (Units.ext hmat)
