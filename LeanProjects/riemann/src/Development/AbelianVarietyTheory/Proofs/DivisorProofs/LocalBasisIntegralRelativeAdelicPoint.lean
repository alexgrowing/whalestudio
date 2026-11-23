import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_inc_le_one (inc : E →+* PadicAlgCl l) (r : 𝓞 E) : ‖inc (r : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((RingOfIntegers.isIntegral_coe r).map inc.toIntAlgHom)

theorem norm_natCast_eq_one' {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : PadicAlgCl l)‖ = 1 := by
  have h : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hm

theorem norm_ev_latHat_le_one (inc : E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) (hev : EvOk inc ev) {M : ℕ}
    (L : Set (Fin M → E)) (hL : ∀ x ∈ L, ∀ i, x i ∈ (algebraMap (𝓞 E) E).range)
    (z : Fin M → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (hz : z ∈ StandardLattice.latHat F E L) (a : Fin M) :
    ‖ev (z a)‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    obtain ⟨r, hr⟩ := hL x hx a
    have e : c ⊗ₜ[F] x a = (c ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show ‖ev (c ⊗ₜ[F] x a)‖ ≤ 1
    rw [e, map_mul, norm_mul, hev.1, ← hr]
    exact mul_le_one₀ (hev.2.1 c hc) (norm_nonneg _) (norm_inc_le_one inc r)
  | zero => simp
  | add y w _ _ hy hw =>
    show ‖ev (y a + w a)‖ ≤ 1
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hw)
  | neg y _ hy =>
    show ‖ev (-(y a))‖ ≤ 1
    rwa [map_neg, norm_neg]

end General

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem selfDualLattice_frame_span_integral_coordinates (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    (x : Fin V.rank → D.host.E) (hx : x ∈ StandardLattice.L0c D V) (i : Fin V.rank) :
    x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hx' : ∑ j, x j • V.frame j ∈ V.L0 := hx
  rw [hL0, Submodule.mem_span_range_iff_exists_fun] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hc' : ∑ j, ((c j : D.host.E)) • V.frame j = ∑ j, x j • V.frame j := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    exact (algebraMap_smul D.host.E (c j) (V.frame j))
  have h2 := congrArg (fun v => V.frame.repr v i) hc'
  simp only [Module.Basis.repr_sum_self] at h2
  exact ⟨c i, h2⟩

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem norm_ev_hLat_le_one (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l) (hev : EvOk inc ev)
    (y : Bridge.Gf V) (x : Fin V.rank → D.host.E) (hx : x ∈ Bridge.hLat V y) (a : Fin V.rank) :
    ‖ev (Matrix.mulVec ((y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))⁻¹).val
      (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) a)‖ ≤ 1 := by
  unfold Bridge.hLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' := hx
    simp only [Set.mem_ofPred, Subgroup.coe_inv] at hx'
    exact norm_ev_latHat_le_one inc ev hev (StandardLattice.L0c D V) (fun x hx i => selfDualLattice_frame_span_integral_coordinates V hL0 x hx i) _ hx' a
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero]
    rw [show (fun _ : Fin V.rank => (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) = 0 from rfl]
    simp
  | add x w _ _ hx hw =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (x + w) i) =
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) +
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] w i) := by
      funext i; simp [TensorProduct.tmul_add]
    rw [e, Matrix.mulVec_add, Pi.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hw)
  | smul r x _ hx =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r • x) i) =
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) •
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      congr 1
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1]
    exact mul_le_one₀ (norm_inc_le_one inc r) (norm_nonneg _) hx

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

theorem locBasis_integral : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  intro D V l _ inc ev hev hL0 y B hB a b
  obtain ⟨s, hs, hmem⟩ := (hB (fun k => B.val k b)).2 ⟨1, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), fun c => by
    have e : Matrix.mulVec (B⁻¹).val (fun k => B.val k b) c = ((B⁻¹).val * B.val) c b := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩⟩
  have h := norm_ev_hLat_le_one V hL0 inc ev hev y _ hmem a
  have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((s : D.host.E) • fun k => B.val k b) i)) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) •
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] B.val i b) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1, map_natCast,
    norm_natCast_eq_one' hs, one_mul] at h
  rw [← map_inv, Units.val_mul, Matrix.mul_apply]
  refine le_of_eq_of_le (congrArg norm ?_) h
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, hev.1]
  rfl

end GlobalTheory.LocBasisInt
