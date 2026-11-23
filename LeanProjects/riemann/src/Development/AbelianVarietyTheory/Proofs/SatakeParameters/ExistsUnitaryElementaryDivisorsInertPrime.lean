import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertExist

section Local

open GlobalTheory.SelfDualGenus GlobalTheory.PlaceComp GlobalTheory.HeckeLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (x i) := by
  show x ∈ Formalism.L2.Col.stdLat E n ↔ _
  simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

theorem antiJ_herm (n : ℕ) (a b : Fin n) :
    ReciprocityTheory.ChartRestriction.G.FD.cc (Formalism.UG.antiJ E n a b) = Formalism.UG.antiJ E n b a := by
  simp only [Formalism.UG.antiJ, add_comm b.val a.val]
  split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]

theorem antiJ_det_ne_zero (n : ℕ) : (Formalism.UG.antiJ E n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem selfDual_antiJ (n : ℕ) (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔
      ∀ y ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)),
        IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm (Formalism.UG.antiJ E n) x y) := by
  rw [mem_stdLat_iff]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff] at hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
    refine ((hx a).mul ?_).mul ?_
    · unfold Formalism.UG.antiJ; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
  · intro h i
    have hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) := by
      rw [mem_stdLat_iff]
      intro j
      by_cases hj : j = i.rev
      · subst hj; simpa using isIntegral_one
      · simpa [hj] using isIntegral_zero
    have := h _ hy
    convert this using 1
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by have := i.2; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hc; apply hb; ext; have := i.2; have := b.2; omega
    · intro h; exact absurd (Finset.mem_univ i) h

theorem locLattice_le {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {x : Fin n → LocAlg v} (hx : x ∈ locLattice v (Formalism.L2.Col.stdLat E n)) (i : Fin n) : x i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i := ⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩
    show locEmb v (y i) ∈ locOrder v
    rw [← hz]
    exact locEmb_mem_locOrder v z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Subalgebra.smul_mem _ hx c

theorem mulVec_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, M i j ∈ O) {z : Fin n → R} (hz : ∀ i, z i ∈ O) (i : Fin n) : (M *ᵥ z) i ∈ O := by
  show ∑ j, M i j * z j ∈ O
  exact O.sum_mem fun j _ => mul_mem (hM i j) (hz j)

theorem single_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} (j i : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_antiFrame [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) :
    ∃ h : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 *
        (Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)) * h.1 = 1 ∧
      (∀ i j, h.1 i j ∈ ordAt E v) ∧ ∀ i j, (h⁻¹).1 i j ∈ ordAt E v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n)
    ⟨Formalism.L2.Col.stdLat_lattice.fg, Formalism.L2.Col.stdLat_lattice.span_eq_top⟩ (selfDual_antiJ n) v
  have hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]
      intro i
      by_cases hi : i = j
      · subst hi; simpa using isIntegral_one
      · simpa [hi] using isIntegral_zero
    · funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  refine ⟨h, ?_, fun i j => ?_, fun i j => ?_⟩
  · have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.transpose_one] at h3
    have hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v) := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]
    rw [hT] at h3
    exact h3
  · rw [mem_ordAt_iff]
    have hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
      rw [h2]
      intro k
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact single_int (O := (locOrder v).toSubring) j k
    have := locLattice_le v hm i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · rw [mem_ordAt_iff]
    have := (h2 _).1 (hs j) i
    rw [Matrix.mulVec_single_one] at this
    exact this

theorem exists_std [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) {ϖ : E} (h0 : ϖ ≠ 0) (hσ : hc.sig ϖ = ϖ) (d : ℕ → ℤ) (hd : ∀ i : Fin n, d i.rev.1 = -d i.1) :
    ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
      StdDiv (ordAt E v) 1 (fun i : Fin n => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) u.1 := by
  obtain ⟨h, hh, hi, hi'⟩ := exists_antiFrame hc v n
  have hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) =
      inclR (Fv (maximalRealSubfield E) v) (hc.sig x) := fun x => by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)
  let t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))
  have tt : ∀ i, t i * t' i = 1 := fun i => by
    simp only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
  let T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    ⟨Matrix.diagonal t, Matrix.diagonal t',
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩
  have hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig)
      ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v))) := by
    show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _
    rw [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = i.rev := Fin.ext (by rw [Fin.val_rev]; omega)
      subst hj
      simp only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]
      show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) *
        inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1
      rw [hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
    · simp only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]
  have hu := conj_mem_UJ _ hh hT
  have hTv : ∀ w, T.1 *ᵥ w = t * w := fun w => funext fun k => by
    show (Matrix.diagonal t *ᵥ w) k = t k * w k
    rw [Matrix.mulVec_diagonal]
  refine ⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩,
    fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩
  · rw [one_smul]; exact mulVec_int hi' hz i
  · rw [one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]
  · have hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]

end Local

section Host

open GlobalTheory.PlaceComp

theorem exists_suppF_divAt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e x ϖ d hP hx h1 h2 hlen hdual
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by
    rcases id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩
    · rw [← he] at a3
      exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
    · exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _)
  have hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ := by
    rw [hx]
    exact D.sp.cm.sig.commutes _
  have hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0 := fun i => by
    have := GlobalTheory.DualDivU.getD_dualLab d hlen i
    rw [hdual] at this
    rw [this, neg_neg]
  obtain ⟨u, hu, hs⟩ := GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd
  obtain ⟨g, hg, hg'⟩ := (GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E)
    (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩
  exact ⟨g, hg, hlen, hg'⟩

end Host

end GlobalTheory.InertExist
