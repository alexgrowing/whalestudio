import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing

noncomputable section

namespace Formalism.MainNotions.LocalModelPeriodLattices

section Global

open NumberField NumberField.IsCMField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
open scoped BigOperators nonZeroDivisors

variable {D : Formalism.BasicNotions.D7}

theorem gS_pos (D : Formalism.BasicNotions.D7) : 0 < Lat.gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem dual_one_eq (D : Formalism.BasicNotions.D7) :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
  unfold Formalism.BasicNotions.Host.ddE
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv]

theorem dualPsiG_le_of_core (ν : ℤ) (L : Set D.host.E) (h2 : ∀ t ∈ gdd (D := D) 2 ν, t ∈ L) :
    ∀ l ∈ dualPsiG (D := D) L, l ∈ gdd (D := D) (-1) (-(ν + 1)) := by
  intro l hl
  have key := Formalism.FourierDecayAlt.P.dual_third_group_holds D.host.E _ (dual_one_eq D) ν ((Lat.gS D : ℕ) : ℤ)
    (by exact_mod_cast (gS_pos D).ne')
    (((gdd (D := D) 2 ν : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ)
    (by
      intro y hy
      simp only [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe]
      unfold gdd
      rw [mul_comm]
      simpa using hy) l
    (by
      intro y hy
      simp only [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe] at hy
      obtain ⟨z, hz⟩ := hl y (h2 y hy)
      exact ⟨z, by simpa using hz.symm⟩)
  unfold gdd
  rw [mul_comm]
  simpa using key

theorem cmE (D : Formalism.BasicNotions.D7) : IsCMField D.host.E :=
  D.host.isCMField_hostE

theorem deg_eq (D : Formalism.BasicNotions.D7) : letI := cmE D; Formalism.FourierDecayAlt.S6.deg D.host.E = D.R.f := by
  have := cmE D
  have h1 := (Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).1
  have h2 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h3 : D.R.f = 2 * D.R.ord := rfl
  rw [h2] at h1
  omega

theorem rd_eq (D : Formalism.BasicNotions.D7) : letI := cmE D; Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
  simp [Formalism.FourierDecayAlt.S6.rd, Formalism.BasicNotions.Host.rdE, one_div]

theorem gdd_eq_idl (D : Formalism.BasicNotions.D7) (a b : ℤ) :
    letI := cmE D; gdd (D := D) a b = Formalism.FourierDecayAlt.S6.idl D.host.E (Lat.gS D) a b := by
  simp only [gdd, Formalism.FourierDecayAlt.S6.idl, Formalism.FourierDecayAlt.S6.dd, Formalism.BasicNotions.Host.ddE]
  rw [mul_comm]

def PlacesTau (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ l : D.host.E, ∏ τ : D.what₂.Tau, ‖D.host.emb (D.eTau τ) l‖ = ∏ w : InfinitePlace D.host.E, w l

theorem rdE_pos (D : Formalism.BasicNotions.D7) : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  exact abs_pos.2 this

theorem sqrt_absNorm_gdd (D : Formalism.BasicNotions.D7) (a : ℕ) :
    Real.sqrt (FractionalIdeal.absNorm (gdd (D := D) (-1) (-(a : ℤ))) : ℝ) =
      ((Lat.gS D : ℝ) * D.host.rdE ^ a) ^ (-(D.R.f : ℤ)) := by
  have := cmE D
  have h := Formalism.FourierDecayAlt.P.scaledIdealNorm D.host.E (Lat.gS D) (-1) (-(a : ℤ)) (gS_pos D)
  rw [← gdd_eq_idl, deg_eq, rd_eq] at h
  rw [h]
  simp only [zpow_neg, zpow_natCast, zpow_one]
  rw [← mul_inv, inv_pow]

theorem period_lattice_index_of_known (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (i : ℕ) (hi : i ≤ D.R.rS + 1)
    (hPl : PlacesTau D)
    (h2 : ∀ t ∈ gdd (D := D) 2 (nu D.R.rS i i), t ∈ La M δ (nu D.R.rS i i) 1)
    (hidx : (AddSubgroup.closure (dualPsiG (D := D) (La M δ (nu D.R.rS i i) 1))).relIndex
      (gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ)) :
        Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup = (Lat.gS D) ^ D.R.f) :
    G4 δ M i := by
  have := cmE D
  have hg : (0 : ℝ) < (Lat.gS D : ℝ) := by exact_mod_cast gS_pos D
  have hrd := rdE_pos D
  have hν : ((nu D.R.rS i i : ℕ) : ℤ) + 1 = ((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ) := by
    have : nu D.R.rS i i + 1 = 2 * D.R.rS + 3 - 2 * i := by unfold nu; omega
    exact_mod_cast this
  have c1 : ∀ l ∈ dualPsiG (D := D) (La M δ (nu D.R.rS i i) 1),
      l ∈ gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ)) := by
    intro l hl
    rw [← hν]
    exact dualPsiG_le_of_core _ _ h2 l hl
  have c3 : ∀ l ∈ gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ)), l ≠ 0 →
      Real.sqrt (FractionalIdeal.absNorm (gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ))) : ℝ) ≤
        ∏ τ : D.what₂.Tau, ‖D.host.emb (D.eTau τ) l‖ := by
    intro l hl h0
    rw [hPl l]
    exact Formalism.FourierDecayAlt.P.norm_lower_bound D.host.E _ l hl h0
  have c4 := sqrt_absNorm_gdd D (2 * D.R.rS + 3 - 2 * i)
  have c5 : ∀ c : D.what₂.Tau → ℝ,
      (∏ τ, c τ * (2 * Real.pi / (Lat.gS D : ℝ)) ^ (2 * (i : ℤ) - 3 - 2 * (D.R.rS : ℤ))) /
        Real.sqrt (FractionalIdeal.absNorm (gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ))) : ℝ) =
      (∏ τ, c τ) * (2 * Real.pi / D.host.rdE) ^ ((2 * (i : ℤ) - 3 - 2 * (D.R.rS : ℤ)) * D.R.f) *
        (Lat.gS D : ℝ) ^ (((D.R.m : ℤ) - 2 * ((i : ℤ) - 1)) * D.R.f) := by
    intro c
    have h := Formalism.FourierDecayAlt.P.dual_size_identity D.what₂.Tau c (Lat.gS D : ℝ) D.host.rdE D.R.rS i hg hrd
    rw [D.what₂.card_Tau] at h
    have hm : (D.R.m : ℤ) = 2 * (D.R.rS : ℤ) + 2 := by
      have h1 := D.R.m_even
      have h2 := D.R.two_le_m
      have h3 : D.R.rS = D.R.m / 2 - 1 := rfl
      obtain ⟨q, hq⟩ := h1
      omega
    have ha : (2 * (D.R.rS : ℤ) + 3 - 2 * (i : ℤ)) = ((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ) := by omega
    rw [ha, zpow_natCast] at h
    rw [c4, hm]
    exact h
  refine ⟨c1, hidx, c3, c4, c5, ?_⟩
  intro c hc l hl h0
  show _ / (∏ τ : D.what₂.Tau, ‖D.host.emb (D.eTau τ) l‖) ≤ (∏ τ, c τ) * (2 * Real.pi / D.host.rdE) ^ ((2 * (i : ℤ) - 3 - 2 * (D.R.rS : ℤ)) * D.R.f) *
        (Lat.gS D : ℝ) ^ (((D.R.m : ℤ) - 2 * ((i : ℤ) - 1)) * D.R.f)
  rw [← c5 c]
  have hN : 0 < Real.sqrt (FractionalIdeal.absNorm
      (gdd (D := D) (-1) (-((2 * D.R.rS + 3 - 2 * i : ℕ) : ℤ))) : ℝ) := by
    rw [c4]; positivity
  apply div_le_div_of_nonneg_left _ hN (c3 l (c1 l hl) h0)
  apply Finset.prod_nonneg
  intro τ _
  have := hc τ
  positivity

theorem emb_injective (D : Formalism.BasicNotions.D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem conj_emb (D : Formalism.BasicNotions.D7) (g : D.R.GG) :
    ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (D.R.cc * g) := by
  refine RingHom.ext fun x => ?_
  simp only [ComplexEmbedding.conjugate_coe_eq, Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf,
    RingHom.comp_apply, map_mul]
  rw [← D.host.conjE_apply]
  rfl

theorem cc_notMem (φ : Formalism.HC.Frame) : φ.cc ∉ φ.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff]
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]

theorem placesTau (D : Formalism.BasicNotions.D7) : PlacesTau D := by
  have := cmE D
  intro l
  have hinj : Function.Injective
      (fun τ : D.what₂.Tau => InfinitePlace.mk (D.host.emb (D.eTau τ))) := by
    intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact D.eTau.injective (Subtype.ext (emb_injective D h))
    · exfalso
      rw [conj_emb] at h
      have h1 := emb_injective D h
      apply cc_notMem D.R.toFrame
      have h2 : D.R.cc =
          ((D.eTau τ' : D.R.Psi) : D.R.GG) *
            ((D.eTau τ : D.R.Psi) : D.R.GG)⁻¹ := by
        rw [← h1]; group
      rw [h2]
      exact (D.R.Psi).mul_mem (D.eTau τ').2 ((D.R.Psi).inv_mem (D.eTau τ).2)
  have hcard : Fintype.card D.what₂.Tau = Fintype.card (InfinitePlace D.host.E) := by
    rw [D.what₂.card_Tau, (Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).2.1, deg_eq]
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩
  exact Fintype.prod_bijective _ hbij _ _ (fun τ => (InfinitePlace.apply _ _).symm)

theorem conjF_eq_complexConj (D : Formalism.BasicNotions.D7) (x : D.host.E) :
    letI := cmE D; D.conjF x = IsCMField.complexConj D.host.E x := by
  have := cmE D
  apply D.host.φ₀.injective
  rw [D.conjF_eq, IsCMField.complexEmbedding_complexConj]
  exact D.host.conjE_apply _ _

def LaIsPeriod (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (ν s : ℕ) : Prop :=
  ∀ t, t ∈ La M δ ν s ↔ t ∈ gdd (D := D) 1 ν ∧ t - (-1) ^ s * D.conjF t ∈ gdd (D := D) 2 ν

theorem mem_perLat_iff (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (ν s : ℕ) (h1 : LaIsPeriod δ M ν s)
    (t : D.host.E) :
    letI := cmE D; t ∈ Formalism.FourierDecayAlt.S6.perLat D.host.E (Lat.gS D) ν s ↔ t ∈ La M δ ν s := by
  have := cmE D
  rw [h1 t, Formalism.FourierDecayAlt.S6.perLat, Formalism.FourierDecayAlt.P.S6x1.mem_twLat, gdd_eq_idl, gdd_eq_idl,
    conjF_eq_complexConj]

theorem period_lattice_bounds_of_known (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (ν s : ℕ) (h1 : LaIsPeriod δ M ν s) :
    (∀ t ∈ gdd (D := D) 2 ν, t ∈ La M δ ν s) ∧
    (∀ l ∈ dualPsiG (D := D) (La M δ ν s), l ∈ gdd (D := D) (-1) (-((ν : ℤ) + 1))) := by
  have := cmE D
  have h2 : ∀ t ∈ gdd (D := D) 2 ν, t ∈ La M δ ν s := by
    intro t ht
    rw [← mem_perLat_iff δ M ν s h1]
    rw [gdd_eq_idl] at ht
    exact (Formalism.FourierDecayAlt.P.twistedLatticeBetween D.host.E _ _ s (Formalism.FourierDecayAlt.P.S6x2.idl_le D.host.E _ ν)
      (Formalism.FourierDecayAlt.P.different_power_conj_stable D.host.E _ 2 ν)).1 ht
  exact ⟨h2, dualPsiG_le_of_core _ _ h2⟩

theorem dual_index_of_core (hU : letI := cmE D; Formalism.FourierDecayAlt.S6.Unram D.host.E) (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (ν s : ℕ) (h1 : LaIsPeriod δ M ν s) :
    (AddSubgroup.closure (dualPsiG (D := D) (La M δ ν s))).relIndex
      (gdd (D := D) (-1) (-((ν : ℤ) + 1)) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
        (Lat.gS D) ^ D.R.f := by
  have := cmE D
  have h := (Formalism.FourierDecayAlt.P.lattice_facts_general D.host.E hU (Lat.gS D) ν s (gS_pos D)).2.2.2.2.2.1
  rw [deg_eq] at h
  rw [← h]
  unfold Formalism.FourierDecayAlt.S6.idx
  congr 1
  · rw [← AddSubgroup.closure_eq
      (Formalism.FourierDecayAlt.S6.dualLat D.host.E (Lat.gS D) (Formalism.FourierDecayAlt.S6.perLat D.host.E (Lat.gS D) ν s)).toAddSubgroup]
    congr 1
    ext l
    constructor
    · intro hl y hy
      obtain ⟨z, hz⟩ := hl y ((mem_perLat_iff δ M ν s h1 y).1 hy)
      exact ⟨z, by simpa using hz.symm⟩
    · intro hl y hy
      obtain ⟨z, hz⟩ := hl y ((mem_perLat_iff δ M ν s h1 y).2 hy)
      exact ⟨z, by simpa using hz.symm⟩
  · rw [gdd_eq_idl]
    rfl

theorem period_lattice_unramified_of_known (hU : letI := cmE D; Formalism.FourierDecayAlt.S6.Unram D.host.E) (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (i : ℕ) (hi : i ≤ D.R.rS + 1)
    (h1 : LaIsPeriod δ M (nu D.R.rS i i) 1) : G4 δ M i := by
  have hcast : (2 * D.R.rS + 3 - 2 * i : ℕ) = nu D.R.rS i i + 1 := by
    simp only [nu]
    omega
  refine period_lattice_index_of_known δ M i hi (placesTau D) (period_lattice_bounds_of_known δ M _ 1 h1).1 ?_
  rw [hcast]
  push_cast
  exact dual_index_of_core hU δ M _ 1 h1

theorem unram_of (E : Type) [Field E] [NumberField E] [IsCMField E]
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E,
      algebraMap (𝓞 E) E t = complexConj E (algebraMap (𝓞 E) E θ) ∧ θ - t ∉ P) :
    Formalism.FourierDecayAlt.S6.Unram E := by
  have key : ∀ θ t : 𝓞 E, algebraMap (𝓞 E) E t = complexConj E (algebraMap (𝓞 E) E θ) →
      θ - t ∈ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    intro θ t ht
    have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
    have h1 : algebraMap (𝓞 E) E (θ - t) ∈
        ((differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) : Ideal (𝓞 E)) :
          FractionalIdeal (𝓞 E)⁰ E) := by
      rw [coeIdeal_differentIdeal (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E),
        FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero _ _ h10)]
      intro y hy
      rw [FractionalIdeal.mem_dual h10] at hy
      obtain ⟨a₁, ha₁⟩ := hy 1 (FractionalIdeal.one_mem_one _)
      obtain ⟨a₂, ha₂⟩ := hy (algebraMap (𝓞 E) E θ)
        ((FractionalIdeal.mem_one_iff _).2 ⟨θ, rfl⟩)
      rw [Algebra.traceForm_apply] at ha₁ ha₂
      have e₁ := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (y * 1)
      have e₂ := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (y * algebraMap (𝓞 E) E θ)
      rw [← ha₁] at e₁
      rw [← ha₂] at e₂
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a₂ -
        t * algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a₁, ?_⟩
      rw [map_sub, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E a₂,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E a₁,
        e₁, e₂, map_sub, ht, map_mul, mul_one]
      ring
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : x = θ - t := (FaithfulSMul.algebraMap_injective (𝓞 E) E) hxe
    rwa [← this]
  have top : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h P hP
    exact hn (hle (key θ t ht))
  unfold Formalism.FourierDecayAlt.S6.Unram
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (maximalRealSubfield E)) (𝓞 E), top,
    Ideal.top_mul]

theorem unramE (D : Formalism.BasicNotions.D7) : letI := cmE D; Formalism.FourierDecayAlt.S6.Unram D.host.E := by
  have := cmE D
  exact unram_of D.host.E D.sp.cm.cmUnram.2.2

theorem period_lattice_of_unit_block (δ : ∀ p, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (m : ℕ) (hm : m + 1 ≤ D.R.rS + 1)
    (h : G3blk δ M m 1) : G4 δ M (m + 1) := by
  exact period_lattice_unramified_of_known (unramE D) δ M (m + 1) hm h.1

theorem lattice_statement_of_root_gram_blocks {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ)
    (h : 4 * D.R.rS + 8 ≤ D.R.k →
      ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
        (hA : ∀ p, Agree δ M p), G1root δ M ∧ G2 δ M (X δ M hA) cN ∧
        (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → G3blk δ M m s)) : aux₃ D X cN := by
  intro hk
  obtain ⟨δ, M, hA, h1, h2, h3⟩ := h hk
  refine ⟨δ, M, hA, h1, h2, h3, fun i hi1 hi2 => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  exact period_lattice_of_unit_block δ M m hi2 (h3 m 1 le_rfl hi2)

end Global

section Local

open Formalism.MainNotions.S.Loc Formalism.FourierDecayAlt Formalism.DoubleCosetMeasures ValuativeRel
open scoped ComplexConjugate ComplexOrder

section Points

variable {E : Type} [CommRing E]

def tr {n : ℕ} (w : Pt E n) : A5.Point E :=
  (w.blocks.map (fun b => (b.2 : ℕ)), fun i => (w.blocks.map Prod.fst).getD i 1)

theorem tr_sum {n : ℕ} (w : Pt E n) : (tr w).1.sum = n := by
  exact w.size

theorem tr_snoc {n : ℕ} (h : Pt E n) (t : Eˣ) (s : ℕ+) :
    tr (h.snoc t s) = A5.addBlock (tr h) s t := by
  simp only [tr, Pt.snoc, A5.addBlock, List.map_append, List.map_cons, List.map_nil]
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [Function.update_apply, List.length_map]
  split_ifs with hi
  · subst hi
    simp
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    split_ifs with hlt
    · rfl
    · have h1 : h.blocks.length < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hi)
      have h2 : h.blocks[i]? = none := List.getElem?_eq_none (by omega)
      have h3 : [t][i - h.blocks.length]? = none := List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
      simp [h2, h3]

theorem ptEntryL_eq : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    ptEntryL bs a b = if b = revIn (bs.map (fun b => (b.2 : ℕ))) a then
      (((bs.map Prod.fst).getD (blk (bs.map (fun b => (b.2 : ℕ))) a) 1 : Eˣ) : E) else 0
  | [], a, b, h => by simp at h
  | (t, s) :: bs, a, b, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [ptEntryL, List.map_cons, revIn, blk]
    by_cases ha : a < (s : ℕ)
    · simp only [ha, true_and, if_true]
      by_cases hb : b < (s : ℕ)
      · simp only [hb, if_true, List.getD_cons_zero]
        congr 1
        exact propext ⟨fun _ => by omega, fun _ => by omega⟩
      · have h1 : ¬ ((s : ℕ) ≤ a ∧ (s : ℕ) ≤ b) := by omega
        have h2 : ¬ (b = (s : ℕ) - 1 - a) := by omega
        simp [hb, h1, h2]
    · have h1 : ¬ (a < (s : ℕ) ∧ b < (s : ℕ)) := by omega
      simp only [ha, false_and, if_false]
      by_cases hb : (s : ℕ) ≤ b
      · have h2 : (s : ℕ) ≤ a ∧ (s : ℕ) ≤ b := ⟨by omega, hb⟩
        simp only [h2, and_self, if_true]
        rw [ptEntryL_eq bs (a - s) (b - s) (by omega)]
        have h3 : (b - (s : ℕ) = revIn (bs.map (fun b => (b.2 : ℕ))) (a - s)) ↔
            (b = (s : ℕ) + revIn (bs.map (fun b => (b.2 : ℕ))) (a - s)) := by omega
        simp only [h3, Nat.add_comm 1, List.getD_cons_succ]
      · have h2 : ¬ ((s : ℕ) ≤ a ∧ (s : ℕ) ≤ b) := by omega
        have h3 : ¬ (b = (s : ℕ) + revIn (bs.map (fun b => (b.2 : ℕ))) (a - s)) := by omega
        simp [h2, h3]

theorem mat_eq {n : ℕ} (w : Pt E n) :
    w.mat = (pt (tr w).1 (tr w).2).submatrix (finCongr (tr_sum w).symm) (finCongr (tr_sum w).symm) := by
  ext a b
  simp only [Pt.mat, Matrix.submatrix_apply, pt, tr, finCongr_apply, Fin.val_cast]
  exact ptEntryL_eq w.blocks a b (by rw [w.size]; exact a.2)

theorem det_eq {n : ℕ} (w : Pt E n) : w.mat.det = (pt (tr w).1 (tr w).2).det := by
  rw [mat_eq w, Matrix.det_submatrix_equiv_self]

theorem isInt_inv_of {n : ℕ} (R : Subring E) (A : Matrix (Fin n) (Fin n) E) (hA : IsInt R A)
    (u : E) (hu : u ∈ R) (h : A.det * u = 1) : IsInt R A⁻¹ := by
  have hAinv : A⁻¹ = u • A.adjugate := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, h, one_smul]
  let A' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hmap : A'.map R.subtype = A := by
    ext i j
    rfl
  intro a b
  have hadj : A.adjugate a b = ((A'.adjugate a b : R) : E) := by
    rw [← hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    rfl
  rw [hAinv, Matrix.smul_apply, smul_eq_mul, hadj]
  exact R.mul_mem hu (A'.adjugate a b).2

end Points

section PartA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

structure Ident (M : Model F E) : Prop where
  top : IsTopologicalRing E
  datum : A5.LocalDatum E M.R M.psiR
  kk : ∀ (n : ℕ) (w w' : Pt E n), M.Kk n w w' = A5.Kp M.R M.psiR (tr w) (tr w')
  modK : ∀ x : Eˣ, M.modK (x : E) = A5.modK M.R (x : E)

variable {M : Model F E}

theorem mem_Rsub (M : Model F E) (x : E) : x ∈ M.Rsub ↔ x ∈ M.R := by
  show x ∈ LinearMap.range (Algebra.linearMap M.R E) ↔ x ∈ M.R
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem inGLR_tr {m : ℕ} (h : Pt E m) (hh : M.InGLR h) : A5.InGLR M.R (tr h) := by
  obtain ⟨hent, u, hu, hdet⟩ := hh
  have hP : ∀ a b, pt (tr h).1 (tr h).2 a b ∈ M.R := by
    intro a b
    have := hent ((finCongr (tr_sum h).symm).symm a) ((finCongr (tr_sum h).symm).symm b)
    rw [mat_eq h] at this
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using this
  exact ⟨hP, isInt_inv_of M.R _ hP u hu (by rw [← det_eq h]; exact hdet)⟩

theorem toAddSubgroup_Rsub (M : Model F E) : M.Rsub.toAddSubgroup = M.R.toAddSubgroup := by
  ext x
  exact mem_Rsub M x

def quotE (M : Model F E) : (E ⧸ M.Rsub) ≃ (E ⧸ M.R.toAddSubgroup) :=
  (QuotientAddGroup.quotientAddEquivOfEq (toAddSubgroup_Rsub M)).toEquiv

end PartA

section SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem mem_R_split (L : LocE F E) (g : SplitG L) (mu : MeasureTheory.Measure E) (x : E) :
    x ∈ (⟨L, some g, mu⟩ : Model F E).R ↔ g.e x ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[F]) (g.q : F) := by
  simp only [Model.R, Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus, Formalism.FourierDecayAlt.I.orderR,
    Set.mem_setOf_eq, RingHom.comp_apply]
  constructor
  · rintro ⟨⟨u, v⟩, huv, hx⟩
    have hx' : g.e x = ((u : F), (v : F)) := hx.symm
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at huv
    obtain ⟨c, hc⟩ := huv
    have hc' : (c : F) * g.q = u - v := congrArg Subtype.val hc
    rw [hx']
    exact ⟨u.2, v.2, c, c.2, by show (u : F) - v = g.q * c; rw [← hc']; ring⟩
  · rintro ⟨h1, h2, t, ht, he⟩
    refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
      show t * (g.q : F) = (g.e x).1 - (g.e x).2
      rw [he]
      ring
    · rfl

theorem psiF_cond (hF : IsNonarchimedeanLocalField F) (L : LocE F E) (g : SplitG L) (x : F)
    (h : ∀ u ∈ 𝒪[F], g.psiF (u * x) = 1) : x ∈ 𝒪[F] := by
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (𝒪[F]).zero_mem
  have hxi : x⁻¹ ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
  have hnu : (⟨x⁻¹, hxi⟩ : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    apply hx
    have h1 : ((w⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (⟨x⁻¹, hxi⟩ : 𝒪[F]) = 1 := by rw [← hw]; simp
    have h2 := congrArg Subtype.val h1
    push_cast at h2
    have h3 : (((w⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = x := by
      field_simp at h2
      exact h2
    rw [← h3]
    exact (((w⁻¹ : (𝒪[F])ˣ) : 𝒪[F])).2
  rw [g.q_irr.maximalIdeal_eq, Ideal.mem_span_singleton'] at hnu
  obtain ⟨v, hv⟩ := hnu
  have hv' : (v : F) * (g.q : F) = x⁻¹ := by
    have := congrArg Subtype.val hv
    simpa using this
  obtain ⟨y, hy⟩ := g.psiF_cond
  apply hy
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)
  have e : (y : F) / (g.q : F) = ((y : F) * (v : F)) * x := by
    field_simp
    have : (v : F) * (g.q : F) * x = 1 := by rw [hv']; exact inv_mul_cancel₀ hx0
    linear_combination (-(y : F)) * this
  rw [e]
  exact h _ ((𝒪[F]).mul_mem y.2 v.2)

theorem selfDual_of_core (M : Model F E) (hOK : M.OK) (a : E) :
    (∀ r ∈ M.R, M.psiR (a * r) = 1) ↔ a ∈ M.R := by
  have hF := hOK.loc
  obtain ⟨L, _ | g, mu⟩ := M
  · exact L.additive_character_dual_ring a
  · have hq : (g.q : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    have hpsi : ∀ x : E, (⟨L, some g, mu⟩ : Model F E).psiR x =
        g.psiF (((g.e x).1 - (g.e x).2) / (g.q : F)) := fun x => rfl
    constructor
    · intro h
      rw [mem_R_split]
      refine (Formalism.FourierDecayAlt.P.self_dual_gamma F (𝒪[F]) (g.q : F) g.q.2 hq (g.e a)).1 ?_
      intro b hb
      apply psiF_cond hF L g
      intro u hu
      have hr : g.e.symm (u * b.1, u * b.2) ∈ (⟨L, some g, mu⟩ : Model F E).R := by
        rw [mem_R_split, AlgEquiv.apply_symm_apply]
        obtain ⟨h1, h2, t, ht, h3⟩ := hb
        exact ⟨(𝒪[F]).mul_mem hu h1, (𝒪[F]).mul_mem hu h2, u * t, (𝒪[F]).mul_mem hu ht, by
          simp only; rw [← mul_sub, h3]; ring⟩
      have := h _ hr
      rw [hpsi, map_mul, AlgEquiv.apply_symm_apply] at this
      rw [← this]
      congr 1
      simp only [Prod.fst_mul, Prod.snd_mul]
      ring
    · intro ha r hr
      have har := (⟨L, some g, mu⟩ : Model F E).R.mul_mem ha hr
      rw [mem_R_split] at har
      obtain ⟨-, -, t, ht, h3⟩ := har
      rw [hpsi, h3, mul_div_cancel_left₀ _ hq]
      exact g.psiF_o t ht

end SelfDual

section Min

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem finite_E (M : Model F E) : Module.Finite F E := by
  haveI := M.L.free
  exact Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)

theorem top_of_OK (M : Model F E) (hOK : M.OK) : IsTopologicalRing E := by
  have := hOK.loc
  have := M.L.top
  have := finite_E M
  exact IsModuleTopology.isTopologicalRing F E

theorem nonarchimedean_local_field_t2 (hF : IsNonarchimedeanLocalField F) : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : T0Space F := inferInstance
  infer_instance

theorem t2Space_of_model_ok (M : Model F E) (hOK : M.OK) : T2Space E := by
  have := hOK.loc
  have := nonarchimedean_local_field_t2 hOK.loc
  have := M.L.top
  have := M.L.free
  have := finite_E M
  let e := (Module.Free.chooseBasis F E).equivFun
  exact T2Space.of_injective_continuous e.injective
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap)

end Min

section Min2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_mul_eq_zero_of_not_isUnit [Module.Finite F E] (y : E) (hy : ¬ IsUnit y) :
    ∃ a : E, a ≠ 0 ∧ y * a = 0 := by
  by_contra hne
  push_neg at hne
  apply hy
  have hinj : Function.Injective (LinearMap.mulLeft F y) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra h0
    exact hne a h0 ha
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact isUnit_iff_exists_inv.mpr ⟨a, ha⟩

theorem unitRep_of_OK (M : Model F E) (hOK : M.OK) (x : E) : ∃ r ∈ M.R, IsUnit (x + r) := by
  have := finite_E M
  have := hOK.char0
  by_contra hcon
  push Not at hcon
  have h1 : ∀ i : Fin 3, ∃ a : E, a ≠ 0 ∧ (x + ((i : ℕ) : E)) * a = 0 := fun i =>
    exists_mul_eq_zero_of_not_isUnit (F := F) _ (hcon _ (natCast_mem M.R _))
  choose a ha0 ha using h1
  have hli := Module.End.eigenvectors_linearIndependent' (LinearMap.mulLeft F x)
    (fun i : Fin 3 => -(((i : ℕ) : F))) (by
      intro i j hij
      have : ((i : ℕ) : F) = ((j : ℕ) : F) := neg_injective hij
      exact Fin.ext (Nat.cast_injective this)) a (by
      intro i
      refine ⟨?_, ha0 i⟩
      rw [Module.End.mem_eigenspace_iff, LinearMap.mulLeft_apply, neg_smul, Algebra.smul_def, map_natCast]
      linear_combination ha i)
  have := hli.fintype_card_le_finrank
  rw [M.L.rank] at this
  simp at this

theorem unitary_of (M : Model F E) (hOK : M.OK) (hO : IsOpen (M.R : Set E)) (hC : IsCompact (M.R : Set E))
    (hU : ∃ ϖ : Eˣ, (ϖ : E) ∈ M.R ∧ ∀ x : E, ∃ m : ℕ, (ϖ : E) ^ m * x ∈ M.R) (x : E) :
    conj (M.psiR x) = M.psiR (-x) := by
  have := top_of_OK M hOK
  have hψ : ∀ r ∈ M.R, M.psiR r = 1 := by
    intro r hr
    simpa using (selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  obtain ⟨ϖ, hϖ, hx⟩ := hU
  obtain ⟨m, hm⟩ := hx x
  let u : Eˣ := ϖ ^ m
  have huR : (u : E) ∈ M.R := by
    simp only [u, Units.val_pow_eq_pow_val]
    exact M.R.pow_mem hϖ m
  let d : M.R := ⟨u, huR⟩
  have hfin : Finite (M.R ⧸ Ideal.span {d}) := by
    have : CompactSpace M.R := isCompact_iff_compactSpace.1 hC
    have hopen : IsOpen ((Ideal.span {d}).toAddSubgroup : Set M.R) := by
      have h1 : ((Ideal.span {d}).toAddSubgroup : Set M.R) =
          (fun y : M.R => ((u⁻¹ : Eˣ) : E) * (y : E)) ⁻¹' (M.R : Set E) := by
        ext y
        simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
        rw [Ideal.mem_span_singleton']
        constructor
        · rintro ⟨c, rfl⟩
          rw [Subring.coe_mul, mul_comm (c : E), ← mul_assoc]
          show ((u⁻¹ : Eˣ) : E) * (u : E) * (c : E) ∈ M.R
          rw [Units.inv_mul, one_mul]
          exact c.2
        · intro hy
          refine ⟨⟨_, hy⟩, ?_⟩
          apply Subtype.ext
          rw [Subring.coe_mul]
          show ((u⁻¹ : Eˣ) : E) * (y : E) * (u : E) = y
          rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h1]
      exact hO.preimage (by fun_prop)
    exact AddSubgroup.quotient_finite_of_isOpen (Ideal.span {d}).toAddSubgroup hopen
  have hN : 0 < Nat.card (M.R ⧸ Ideal.span {d}) := Nat.card_pos
  set N := Nat.card (M.R ⧸ Ideal.span {d}) with hNdef
  have hux : (u : E) * x ∈ M.R := by
    simpa only [u, Units.val_pow_eq_pow_val] using hm
  have h0 : N • (Ideal.Quotient.mk (Ideal.span {d}) ⟨_, hux⟩) = 0 := card_nsmul_eq_zero'
  rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨c, hc⟩ := h0
  have hc' : (c : E) * (u : E) = N • ((u : E) * x) := by
    have := congrArg Subtype.val hc
    simpa using this
  have hNx : N • x ∈ M.R := by
    have : N • x = c := by
      apply u.isUnit.mul_left_cancel
      rw [mul_comm (u : E) (c : E), hc', mul_smul_comm]
    rw [this]; exact c.2
  have hpow : M.psiR x ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    exact hψ _ hNx
  have hnorm : ‖M.psiR x‖ = 1 := by
    have h1 : ‖M.psiR x‖ ^ N = 1 := by rw [← norm_pow, hpow, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
  simp

end Min2

section Topo

open Polynomial Topology

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem isOpen_OF [IsNonarchimedeanLocalField F] : IsOpen (𝒪[F] : Set F) :=
  Valuation.isOpen_integer (v := valuation F)

theorem isCompact_OF [IsNonarchimedeanLocalField F] : IsCompact (𝒪[F] : Set F) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F 1

theorem mem_O_of_quad (L : LocE F E) (z : E) (t n : 𝒪[F])
    (h : z * z - algebraMap F E t * z + algebraMap F E n = 0) : z ∈ L.O := by
  rw [L.O_def]
  have ht : algebraMap F E (t : F) = algebraMap 𝒪[F] E t := (IsScalarTower.algebraMap_apply 𝒪[F] F E t).symm
  have hn : algebraMap F E (n : F) = algebraMap 𝒪[F] E n := (IsScalarTower.algebraMap_apply 𝒪[F] F E n).symm
  rw [ht, hn] at h
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · first
      | monicity!
      | monicity
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    linear_combination h

theorem algebraMap_mem_O (L : LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.O_def]
  have h : algebraMap F E (a : F) = algebraMap 𝒪[F] E a := (IsScalarTower.algebraMap_apply 𝒪[F] F E a).symm
  rw [h]
  exact isIntegral_algebraMap

theorem mem_OF_of_mem_O [Nontrivial E] (L : LocE F E) (a : F) (h : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  rw [L.O_def] at h
  have hinj : Function.Injective ((Algebra.ofId F E).restrictScalars 𝒪[F]) := (algebraMap F E).injective
  have h' : IsIntegral 𝒪[F] a := (isIntegral_algHom_iff _ hinj).mp h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  rw [← hy]
  exact y.2

theorem cj_mem_O (L : LocE F E) (x : E) (h : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at h ⊢
  exact h.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

end Top

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem inv_mem_OF (a : F) (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  first
    | exact (ValuationSubring.mem_or_inv_mem _ a).resolve_left h
    | (rw [Valuation.mem_integer_iff] at h ⊢
       rw [map_inv₀]
       exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h)))

theorem exists_scale (a : F) : ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ (r : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, by simp, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0]; exact zero_mem _)
    refine ⟨⟨a⁻¹, inv_mem_OF a ha⟩, inv_ne_zero ha0, ?_⟩
    show a⁻¹ * a ∈ 𝒪[F]
    rw [inv_mul_cancel₀ ha0]
    exact one_mem _

theorem exists_pow_mul_mem [IsNonarchimedeanLocalField F] (π : 𝒪[F]) (hπ : Irreducible π) (a : F) :
    ∃ m : ℕ, ∀ k, m ≤ k → (π : F) ^ k * a ∈ 𝒪[F] := by
  by_cases h : a ∈ 𝒪[F]
  · exact ⟨0, fun k _ => (𝒪[F]).mul_mem ((𝒪[F]).pow_mem π.2 k) h⟩
  · have h0 : a ≠ 0 := by
      rintro rfl
      exact h (𝒪[F]).zero_mem
    have hne : (⟨a⁻¹, inv_mem_OF a h⟩ : 𝒪[F]) ≠ 0 := by
      intro hz
      exact inv_ne_zero h0 (congrArg Subtype.val hz)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπ
    have hu' : a⁻¹ = ((u : 𝒪[F]) : F) * (π : F) ^ n := by
      have := congrArg Subtype.val hu
      simpa using this
    have hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
      have h9 : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) = 1 := Units.inv_mul u
      have h8 := congrArg Subtype.val h9
      rwa [Subring.coe_mul, Subring.coe_one] at h8
    refine ⟨n, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have e : (π : F) ^ (n + j) * a = (π : F) ^ j * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      have h1 : (π : F) ^ n * a = (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
        have h2 : a⁻¹ * a = 1 := inv_mul_cancel₀ h0
        rw [hu'] at h2
        linear_combination (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * h2 - ((π : F) ^ n * a) * hinv
      rw [pow_add, mul_assoc, mul_comm ((π : F) ^ j), ← mul_assoc, h1, mul_comm]
    rw [e]
    exact (𝒪[F]).mul_mem ((𝒪[F]).pow_mem π.2 j) (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])).2

variable (L : LocE F E)

theorem tr_ex (x : E) : ∃ a : F, algebraMap F E a = x + L.cj x := by
  exact (L.cj_fix _).mp (by rw [map_add, L.cj_cj, add_comm])

theorem nm_ex (x : E) : ∃ a : F, algebraMap F E a = x * L.cj x := by
  exact (L.cj_fix _).mp (by rw [map_mul, L.cj_cj, mul_comm])

theorem nontrivial_E (L : LocE F E) : Nontrivial E := by
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

theorem exists_theta : ∃ θ ∈ L.O, L.cj θ = -θ ∧ ∃ D : 𝒪[F], (D : F) ≠ 0 ∧ θ * θ = algebraMap F E D := by
  have := nontrivial_E L
  have hy : ∃ y, L.cj y ≠ y := by
    by_contra hcon
    push Not at hcon
    have h1 : Module.finrank F E ≤ 1 := finrank_le_one (1 : E) (fun w => by
      obtain ⟨a, ha⟩ := (L.cj_fix w).1 (hcon w)
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩)
    rw [L.rank] at h1
    omega
  obtain ⟨y, hy⟩ := hy
  obtain ⟨T, hT⟩ := tr_ex L y
  obtain ⟨N, hN⟩ := nm_ex L y
  obtain ⟨r₁, h10, h1⟩ := exists_scale T
  obtain ⟨r₂, h20, h2⟩ := exists_scale N
  obtain ⟨r, hr⟩ : ∃ r : F, r = (r₁ : F) * (r₂ : F) := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by rw [hr]; exact mul_ne_zero h10 h20
  have hz : algebraMap F E r * y ∈ L.O := by
    refine mem_O_of_quad L _ ⟨r * T, ?_⟩ ⟨r * r * N, ?_⟩ ?_
    · have : r * T = (r₂ : F) * ((r₁ : F) * T) := by rw [hr]; ring
      rw [this]; exact (𝒪[F]).mul_mem r₂.2 h1
    · have : r * r * N = ((r₁ : F) * (r₁ : F) * (r₂ : F)) * ((r₂ : F) * N) := by rw [hr]; ring
      rw [this]; exact (𝒪[F]).mul_mem ((𝒪[F]).mul_mem ((𝒪[F]).mul_mem r₁.2 r₁.2) r₂.2) h2
    · simp only [map_mul, hT, hN]
      ring
  have hθO : algebraMap F E r * y - L.cj (algebraMap F E r * y) ∈ L.O :=
    L.O.sub_mem hz (cj_mem_O L _ hz)
  have hθc : L.cj (algebraMap F E r * y - L.cj (algebraMap F E r * y)) =
      -(algebraMap F E r * y - L.cj (algebraMap F E r * y)) := by
    rw [map_sub, L.cj_cj]; ring
  have hθ0 : algebraMap F E r * y - L.cj (algebraMap F E r * y) ≠ 0 := by
    intro h0
    apply hy
    rw [map_mul L.cj, AlgEquiv.commutes, ← mul_sub] at h0
    have hu : IsUnit (algebraMap F E r) := (hr0.isUnit).map _
    have := (hu.mul_right_eq_zero).1 h0
    exact (sub_eq_zero.1 this).symm
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ = algebraMap F E r * y - L.cj (algebraMap F E r * y) := ⟨_, rfl⟩
  rw [← hθ] at hθO hθc hθ0
  obtain ⟨D, hD⟩ := (L.cj_fix (θ * θ)).1 (by rw [map_mul, hθc]; ring)
  have hDO : D ∈ 𝒪[F] := mem_OF_of_mem_O L D (by rw [hD]; exact L.O.mul_mem hθO hθO)
  refine ⟨θ, hθO, hθc, ⟨D, hDO⟩, ?_, hD.symm⟩
  rintro (rfl : D = 0)
  rw [map_zero] at hD
  have := L.reduced
  exact hθ0 (IsReduced.eq_zero θ ⟨2, by rw [sq]; exact hD.symm⟩)

end Top2

section Top3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem decomp (L : LocE F E) (θ : E) (hθc : L.cj θ = -θ) (D : F) (hD : θ * θ = algebraMap F E D) (x : E) :
    ∃ t c : F, algebraMap F E t = x + L.cj x ∧ algebraMap F E c = (x - L.cj x) * θ ∧
      algebraMap F E (2 * D) * x = algebraMap F E (D * t) + algebraMap F E c * θ := by
  obtain ⟨t, ht⟩ := tr_ex L x
  obtain ⟨c, hc⟩ := (L.cj_fix ((x - L.cj x) * θ)).mp (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)
  refine ⟨t, c, ht, hc, ?_⟩
  rw [map_mul, map_mul, ht, hc, map_ofNat]
  linear_combination (L.cj x - x) * hD

theorem O_top (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] [IsTopologicalRing E] :
    IsOpen (L.O : Set E) ∧ IsCompact (L.O : Set E) ∧
      ∀ π : 𝒪[F], Irreducible π → ∀ x : E, ∃ m : ℕ, ∀ k, m ≤ k → algebraMap F E π ^ k * x ∈ L.O := by
  have := L.top
  have := nontrivial_E L
  obtain ⟨θ, hθO, hθc, D, hD0, hD⟩ := exists_theta L
  let φ : F × F →ₗ[F] E :=
    (LinearMap.toSpanSingleton F E 1).coprod (LinearMap.toSpanSingleton F E θ)
  have hφ : ∀ a b : F, φ (a, b) = algebraMap F E a + algebraMap F E b * θ := by
    intro a b
    simp [φ, Algebra.smul_def]
  have h2D : (2 * (D : F)) ≠ 0 := mul_ne_zero two_ne_zero hD0
  have hinv : ∀ x y : E, algebraMap F E (2 * D) * x = y → x = algebraMap F E (2 * D)⁻¹ * y := by
    intro x y h
    rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2D, map_one, one_mul]
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨t, c, -, -, h⟩ := decomp L θ hθc D hD x
    refine ⟨((2 * (D : F))⁻¹ * (D * t), (2 * (D : F))⁻¹ * c), ?_⟩
    rw [hφ, hinv x _ h, map_mul, map_mul _ _ c]
    ring
  have hcont : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hopenmap : IsOpenMap φ := IsModuleTopology.isOpenMap_of_surjective hsurj
  let S : Set (F × F) := (𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F)
  have hS_open : IsOpen S := isOpen_OF.prod isOpen_OF
  have hS_comp : IsCompact S := isCompact_OF.prod isCompact_OF
  have hsub : φ '' S ⊆ (L.O : Set E) := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [hφ]
    exact L.O.add_mem (algebraMap_mem_O L ⟨a, ha⟩) (L.O.mul_mem (algebraMap_mem_O L ⟨b, hb⟩) hθO)
  have hO_open : IsOpen (L.O : Set E) := by
    have h0 : (L.O.toAddSubgroup : Set E) ∈ 𝓝 (0 : E) :=
      Filter.mem_of_superset ((hopenmap S hS_open).mem_nhds
        ⟨(0, 0), ⟨(𝒪[F]).zero_mem, (𝒪[F]).zero_mem⟩, map_zero φ⟩) hsub
    exact L.O.toAddSubgroup.isOpen_of_mem_nhds h0
  have hO_closed : IsClosed (L.O : Set E) := L.O.toAddSubgroup.isClosed_of_isOpen hO_open
  refine ⟨hO_open, ?_, ?_⟩
  · refine IsCompact.of_isClosed_subset
      ((hS_comp.image hcont).image (continuous_const.mul continuous_id :
        Continuous fun y : E => algebraMap F E (2 * D)⁻¹ * y)) hO_closed ?_
    intro x hx
    obtain ⟨t, c, ht, hc, h⟩ := decomp L θ hθc D hD x
    have htO : t ∈ 𝒪[F] := mem_OF_of_mem_O L t (by rw [ht]; exact L.O.add_mem hx (cj_mem_O L x hx))
    have hcO : c ∈ 𝒪[F] := mem_OF_of_mem_O L c (by
      rw [hc]; exact L.O.mul_mem (L.O.sub_mem hx (cj_mem_O L x hx)) hθO)
    refine ⟨_, ⟨((D : F) * t, c), ⟨(𝒪[F]).mul_mem D.2 htO, hcO⟩, rfl⟩, ?_⟩
    rw [hφ]
    exact (hinv x _ h).symm
  · intro π hπ x
    obtain ⟨⟨a, b⟩, rfl⟩ := hsurj x
    obtain ⟨m₁, h₁⟩ := exists_pow_mul_mem π hπ a
    obtain ⟨m₂, h₂⟩ := exists_pow_mul_mem π hπ b
    refine ⟨max m₁ m₂, fun k hk => ?_⟩
    have e : algebraMap F E π ^ k * φ (a, b) =
        algebraMap F E ((π : F) ^ k * a) + algebraMap F E ((π : F) ^ k * b) * θ := by
      rw [hφ, map_mul, map_mul, map_pow]; ring
    rw [e]
    exact L.O.add_mem (algebraMap_mem_O L ⟨_, h₁ k (le_trans (le_max_left _ _) hk)⟩)
      (L.O.mul_mem (algebraMap_mem_O L ⟨_, h₂ k (le_trans (le_max_right _ _) hk)⟩) hθO)

variable [MeasurableSpace E]

theorem e_algebraMap (L : LocE F E) (g : SplitG L) (c : F) : g.e (algebraMap F E c) = (c, c) := by
  rw [AlgEquiv.commutes]
  rfl

theorem R_top (M : Model F E) (hOK : M.OK) :
    IsOpen (M.R : Set E) ∧ IsCompact (M.R : Set E) ∧
      ∃ ϖ : Eˣ, (ϖ : E) ∈ M.R ∧ ∀ x : E, ∃ m : ℕ, (ϖ : E) ^ m * x ∈ M.R := by
  have := hOK.loc
  have := hOK.char0
  have := top_of_OK M hOK
  obtain ⟨L, _ | g, mu⟩ := M
  · obtain ⟨h1, h2, h3⟩ := O_top L
    refine ⟨h1, h2, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have hπ0 : (π : F) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
    refine ⟨(hπ0.isUnit.map (algebraMap F E)).unit, algebraMap_mem_O L π, fun x => ?_⟩
    obtain ⟨m, hm⟩ := h3 π hπ x
    exact ⟨m, hm m le_rfl⟩
  · obtain ⟨h1, h2, h3⟩ := O_top L
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hRO : ((⟨L, some g, mu⟩ : Model F E).R : Set E) ⊆ (L.O : Set E) := by
      intro x hx
      obtain ⟨ha, hb, -⟩ := (mem_R_split L g mu x).1 hx
      refine mem_O_of_quad L x ⟨(g.e x).1 + (g.e x).2, (𝒪[F]).add_mem ha hb⟩
        ⟨(g.e x).1 * (g.e x).2, (𝒪[F]).mul_mem ha hb⟩ ?_
      apply g.e.injective
      rw [map_add, map_sub, map_mul, map_mul, e_algebraMap, e_algebraMap, map_zero]
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have hqO : ∀ y ∈ L.O, algebraMap F E g.q * y ∈ (⟨L, some g, mu⟩ : Model F E).R := by
      intro y hy
      rw [L.O_def] at hy
      have i1 : (g.e y).1 ∈ 𝒪[F] := (Valuation.integer.integers (valuation F)).mem_of_integral
        (hy.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F]))
      have i2 : (g.e y).2 ∈ 𝒪[F] := (Valuation.integer.integers (valuation F)).mem_of_integral
        (hy.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F]))
      rw [mem_R_split, map_mul, e_algebraMap]
      exact ⟨(𝒪[F]).mul_mem g.q.2 i1, (𝒪[F]).mul_mem g.q.2 i2, (g.e y).1 - (g.e y).2,
        (𝒪[F]).sub_mem i1 i2, by simp only [Prod.fst_mul, Prod.snd_mul]; ring⟩
    have hopen : IsOpen ((⟨L, some g, mu⟩ : Model F E).R : Set E) := by
      have hU : IsOpen ((fun x : E => algebraMap F E (g.q : F)⁻¹ * x) ⁻¹' (L.O : Set E)) :=
        h1.preimage (continuous_const.mul continuous_id)
      have h0 : ((⟨L, some g, mu⟩ : Model F E).R.toAddSubgroup : Set E) ∈ 𝓝 (0 : E) := by
        refine Filter.mem_of_superset (hU.mem_nhds (by simp [L.O.zero_mem])) ?_
        intro x hx
        have := hqO _ hx
        rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul] at this
      exact (⟨L, some g, mu⟩ : Model F E).R.toAddSubgroup.isOpen_of_mem_nhds h0
    refine ⟨hopen, IsCompact.of_isClosed_subset h2
      ((⟨L, some g, mu⟩ : Model F E).R.toAddSubgroup.isClosed_of_isOpen hopen) hRO, ?_⟩
    refine ⟨(hq0.isUnit.map (algebraMap F E)).unit, ?_, fun x => ?_⟩
    · have := hqO 1 L.O.one_mem
      rwa [mul_one] at this
    · obtain ⟨m, hm⟩ := h3 g.q g.q_irr x
      refine ⟨m + 1, ?_⟩
      have := hqO _ (hm m le_rfl)
      rw [← mul_assoc, ← pow_succ'] at this
      exact this

end Top3

end Topo

section Meas

open Topology MeasureTheory

section Mod

variable {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [MeasurableSpace E] [BorelSpace E]

theorem measure_eq_relIndex_mul (mu : Measure E) [mu.IsAddLeftInvariant] (H A : AddSubgroup E) (hHA : H ≤ A)
    (hH : IsOpen (H : Set E)) (hA : IsCompact (A : Set E)) :
    H.relIndex A ≠ 0 ∧ mu (A : Set E) = (H.relIndex A : ENNReal) * mu (H : Set E) := by
  classical
  have : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have hfin : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  have := Fintype.ofFinite (A ⧸ H.addSubgroupOf A)
  have hidx : H.relIndex A = Fintype.card (A ⧸ H.addSubgroupOf A) := by
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  have hU : (A : Set E) = ⋃ q : A ⧸ H.addSubgroupOf A,
      (fun h : E => ((Quotient.out q : A) : E) + h) '' (H : Set E) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk (⟨x, hx⟩ : A), -((Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : A) :
        A ⧸ H.addSubgroupOf A) : A) : E) + x, ?_, by abel⟩
      have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : A) :
          A ⧸ H.addSubgroupOf A)) : A ⧸ H.addSubgroupOf A) = QuotientAddGroup.mk (⟨x, hx⟩ : A) :=
        Quotient.out_eq' _
      have h2 := QuotientAddGroup.eq.1 h1
      simpa [AddSubgroup.mem_addSubgroupOf] using h2
    · rintro ⟨q, h, hh, rfl⟩
      exact A.add_mem (Quotient.out q : A).2 (hHA hh)
  have hdisj : Pairwise (Function.onFun Disjoint fun q : A ⧸ H.addSubgroupOf A =>
      (fun h : E => ((Quotient.out q : A) : E) + h) '' (H : Set E)) := by
    intro q q' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨h, hh, rfl⟩ ⟨h', hh', he⟩
    apply hne
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' q']
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    have : ((-(Quotient.out q : A) + (Quotient.out q' : A) : A) : E) = h - h' := by
      simp only at he
      push_cast
      linear_combination he
    rw [this]
    exact H.sub_mem hh hh'
  have hmeas : ∀ q : A ⧸ H.addSubgroupOf A,
      mu ((fun h : E => ((Quotient.out q : A) : E) + h) '' (H : Set E)) = mu (H : Set E) := by
    intro q
    rw [Set.image_add_left, measure_preimage_add]
  have hms : ∀ q : A ⧸ H.addSubgroupOf A,
      MeasurableSet ((fun h : E => ((Quotient.out q : A) : E) + h) '' (H : Set E)) := by
    intro q
    rw [Set.image_add_left]
    exact (hH.preimage (continuous_const.add continuous_id)).measurableSet
  refine ⟨by rw [hidx]; exact Fintype.card_ne_zero, ?_⟩
  rw [hU, measure_iUnion hdisj hms, tsum_fintype, Finset.sum_congr rfl (fun q _ => hmeas q), hidx]
  simp

end Mod

section Mod2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem modK_of_OK (M : Model F E) (hOK : M.OK) (x : Eˣ) : M.modK (x : E) = A5.modK M.R (x : E) := by
  have := top_of_OK M hOK
  have := hOK.borel
  have := hOK.haar.haar
  obtain ⟨hRo, hRc, -⟩ := R_top M hOK
  have hset : ((A5.mulR M.R (x : E) : AddSubgroup E) : Set E) = (fun y => (x : E) * y) '' (M.R : Set E) := by
    ext y
    simp [A5.mulR]
  have hxo : IsOpen ((A5.mulR M.R (x : E) : AddSubgroup E) : Set E) := by
    have : ((A5.mulR M.R (x : E) : AddSubgroup E) : Set E) =
        (fun y : E => ((x⁻¹ : Eˣ) : E) * y) ⁻¹' (M.R : Set E) := by
      rw [hset]
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
      constructor
      · rintro ⟨r, hr, rfl⟩
        rwa [← mul_assoc, Units.inv_mul, one_mul]
      · intro hy
        exact ⟨_, hy, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [this]
    exact hRo.preimage (continuous_const.mul continuous_id)
  have hxc : IsCompact ((A5.mulR M.R (x : E) : AddSubgroup E) : Set E) := by
    rw [hset]
    exact hRc.image (continuous_const.mul continuous_id)
  have hHo : IsOpen ((M.R.toAddSubgroup ⊓ A5.mulR M.R (x : E) : AddSubgroup E) : Set E) := by
    rw [AddSubgroup.coe_inf]
    exact IsOpen.inter hRo hxo
  obtain ⟨n1, e1⟩ := measure_eq_relIndex_mul M.mu _ (A5.mulR M.R (x : E)) inf_le_right hHo hxc
  obtain ⟨n2, e2⟩ := measure_eq_relIndex_mul M.mu _ M.R.toAddSubgroup inf_le_left hHo hRc
  rw [AddSubgroup.inf_relIndex_right] at n1 e1
  rw [AddSubgroup.inf_relIndex_left] at n2 e2
  have hR1 : M.mu (M.R.toAddSubgroup : Set E) = 1 := hOK.haar.volR
  rw [hR1] at e2
  unfold Model.modK A5.modK
  rw [← hset, e1, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have e3 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at e3
  have hn2 : (((A5.mulR M.R (x : E)).relIndex M.R.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by exact_mod_cast n2
  rw [eq_div_iff hn2]
  linear_combination (-(((M.R.toAddSubgroup).relIndex (A5.mulR M.R (x : E)) : ℕ) : ℝ)) * e3

end Mod2

end Meas

section KKdef

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem datum_of_OK (M : Model F E) (hOK : M.OK) :
    haveI := top_of_OK M hOK; A5.LocalDatum E M.R M.psiR := by
  obtain ⟨hO, hC, hU⟩ := R_top M hOK
  haveI := top_of_OK M hOK
  haveI := finite_E M
  have hart : IsArtinianRing E := by
    first
      | exact IsArtinianRing.of_finite F E
      | infer_instance
  exact {
    t2 := t2Space_of_model_ok M hOK
    isOpen := hO
    isCompact := hC
    unif := hU
    artin := hart
    red := M.L.reduced
    unitRep := unitRep_of_OK M hOK
    unitary := unitary_of M hOK hO hC hU
    selfDual := selfDual_of_core M hOK }

def KK (M : Model F E) : Prop :=
  ∀ (n : ℕ) (w w' : Pt E n), M.Kk n w w' = A5.Kp M.R M.psiR (tr w) (tr w')

end KKdef

section PartA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}

def KKAll : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → KK M

def BBFin (M : Model F E) (r : ℕ) : Prop := ∀ w : Pt E (r + 1), {c : M.Cls r | M.BB w c ≠ 0}.Finite

end PartA

section Meas2

open Topology MeasureTheory

section Fin1

variable {A : Type} [CommRing A]

def redV (I : Ideal A) {n : ℕ} (v : Fin n → A) : Fin n → A ⧸ I := fun i => Ideal.Quotient.mk I (v i)

theorem range_le_of_red {n : ℕ} (Z Z' : Matrix (Fin n) (Fin n) A)
    (h : redV (Ideal.span {Z'.det}) '' (LinearMap.range Z.mulVecLin : Set (Fin n → A)) ⊆
      redV (Ideal.span {Z'.det}) '' (LinearMap.range Z'.mulVecLin : Set (Fin n → A))) :
    LinearMap.range Z.mulVecLin ≤ LinearMap.range Z'.mulVecLin := by
  rintro v ⟨x, rfl⟩
  obtain ⟨w, hwm, hw⟩ := h (Set.mem_image_of_mem _ (LinearMap.mem_range_self _ x))
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hwm
  have hc : ∀ i, ∃ c : A, Z.mulVec x i - Z'.mulVec y i = Z'.det * c := by
    intro i
    have hi := congrFun hw i
    simp only [redV, Matrix.mulVecLin_apply] at hi
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hi
    obtain ⟨a, ha⟩ := hi
    exact ⟨-a, by linear_combination ha⟩
  choose c hc using hc
  refine LinearMap.mem_range.mpr ⟨y + Z'.adjugate.mulVec c, ?_⟩
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  first
    | rw [Matrix.smul_mulVec_assoc]
    | rw [Matrix.smul_mulVec]
    | rw [Matrix.smul_mulVec_eq_smul_mulVec]
  simp only [Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(hc i)

theorem finite_image_of_factor {α β γ : Type} [Finite γ] (f : α → β) (J : α → γ) (T : Set α)
    (h : ∀ a ∈ T, ∀ a' ∈ T, J a = J a' → f a = f a') : (f '' T).Finite := by
  have hs : ∀ c : γ, (f '' (T ∩ J ⁻¹' {c})).Subsingleton := by
    rintro c _ ⟨a, ⟨ha, hac⟩, rfl⟩ _ ⟨a', ⟨ha', hac'⟩, rfl⟩
    exact h a ha a' ha' ((hac : J a = c).trans (hac' : J a' = c).symm)
  refine (Set.finite_iUnion (fun c => (hs c).finite)).subset ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Set.mem_iUnion.mpr ⟨J a, a, ⟨ha, rfl⟩, rfl⟩

end Fin1

section Fin2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem lamRaw_eq (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    M.lamRaw ZZ v = Submodule.Quotient.mk
      (Ring.inverse ((ZZ.Z.det : M.R) : E) * ((ZZ.Z.adjugate.mulVec v (Fin.last m) : M.R) : E)) := by
  simp only [Model.lamRaw, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    LinearMap.proj_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  congr 1
  have hdet : (ZZ.Z.map M.R.subtype).det = ((ZZ.Z.det : M.R) : E) :=
    (RingHom.map_det M.R.subtype ZZ.Z).symm
  have hadj : (ZZ.Z.map M.R.subtype).adjugate = ZZ.Z.adjugate.map M.R.subtype :=
    (RingHom.map_adjugate M.R.subtype ZZ.Z).symm
  rw [Matrix.inv_def, hdet, hadj, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact (RingHom.map_mulVec M.R.subtype ZZ.Z.adjugate v (Fin.last m)).symm

theorem iso_of_inv (M : Model F E) {m : ℕ} (ZZ ZZ' : M.Mat (m + 1)) (hd : ZZ.Z.det = ZZ'.Z.det)
    (h1 : redV (Ideal.span {ZZ.Z.det}) '' (LinearMap.range ZZ.Z.mulVecLin : Set (Fin (m + 1) → M.R)) =
      redV (Ideal.span {ZZ.Z.det}) '' (LinearMap.range ZZ'.Z.mulVecLin : Set (Fin (m + 1) → M.R)))
    (h2 : redV (Ideal.span {ZZ.Z.det}) (ZZ.Z.adjugate (Fin.last m)) =
      redV (Ideal.span {ZZ.Z.det}) (ZZ'.Z.adjugate (Fin.last m))) : Nonempty (M.Iso ZZ ZZ') := by
  have hr : LinearMap.range ZZ.Z.mulVecLin = LinearMap.range ZZ'.Z.mulVecLin := by
    apply le_antisymm
    · apply range_le_of_red
      rw [← hd]; exact h1.le
    · apply range_le_of_red
      exact h1.ge
  refine ⟨⟨Submodule.quotEquivOfEq _ _ hr, rfl, ?_⟩⟩
  intro c
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [Submodule.quotEquivOfEq_mk]
  show M.lamRaw ZZ' v = M.lamRaw ZZ v
  rw [lamRaw_eq, lamRaw_eq, ← hd, Submodule.Quotient.eq, ← mul_sub, mem_Rsub]
  have h3 : ∀ j, ∃ r, r * ZZ.Z.det = ZZ'.Z.adjugate (Fin.last m) j - ZZ.Z.adjugate (Fin.last m) j := by
    intro j
    have := congrFun h2 j
    simp only [redV] at this
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    exact this.symm
  choose r hr' using h3
  have h4 : ZZ'.Z.adjugate.mulVec v (Fin.last m) - ZZ.Z.adjugate.mulVec v (Fin.last m) =
      ZZ.Z.det * ∑ j, r j * v j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(v j)) * hr' j
  have hU : IsUnit ((ZZ.Z.det : M.R) : E) := by
    have h9 := ZZ.unit
    have hdet : (ZZ.Z.map M.R.subtype).det = ((ZZ.Z.det : M.R) : E) :=
      (RingHom.map_det M.R.subtype ZZ.Z).symm
    rwa [hdet] at h9
  have h5 : ((ZZ'.Z.adjugate.mulVec v (Fin.last m) : M.R) : E) - ((ZZ.Z.adjugate.mulVec v (Fin.last m) : M.R) : E) =
      ((ZZ.Z.det : M.R) : E) * ((∑ j, r j * v j : M.R) : E) := by
    have h8 := congrArg M.R.subtype h4
    rwa [map_sub, map_mul] at h8
  rw [h5, ← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]
  exact (∑ j, r j * v j : M.R).2

theorem finite_classes (M : Model F E) (hOK : M.OK) (m : ℕ) (d₀ : M.R) (hd₀ : IsUnit (d₀ : E)) :
    {c : M.Cls m | ∃ ZZ : M.Mat (m + 1), ZZ.Z.det = d₀ ∧ Quotient.mk (M.isoSetoid m) ZZ = c}.Finite := by
  have := top_of_OK M hOK
  obtain ⟨hRo, hRc, -⟩ := R_top M hOK
  have hfin : Finite (M.R ⧸ Ideal.span {d₀}) := by
    have : CompactSpace M.R := isCompact_iff_compactSpace.1 hRc
    obtain ⟨u, hu⟩ := hd₀
    have hopen : IsOpen ((Ideal.span {d₀}).toAddSubgroup : Set M.R) := by
      have h1 : ((Ideal.span {d₀}).toAddSubgroup : Set M.R) =
          (fun y : M.R => ((u⁻¹ : Eˣ) : E) * (y : E)) ⁻¹' (M.R : Set E) := by
        ext y
        simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
        rw [Ideal.mem_span_singleton']
        constructor
        · rintro ⟨c, rfl⟩
          rw [Subring.coe_mul, ← hu, mul_comm (c : E), ← mul_assoc, Units.inv_mul, one_mul]
          exact c.2
        · intro hy
          refine ⟨⟨_, hy⟩, ?_⟩
          apply Subtype.ext
          rw [Subring.coe_mul, ← hu]
          simp only
          rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h1]
      exact hRo.preimage (by fun_prop)
    exact AddSubgroup.quotient_finite_of_isOpen (Ideal.span {d₀}).toAddSubgroup hopen
  have key := finite_image_of_factor (Quotient.mk (M.isoSetoid m))
    (fun ZZ : M.Mat (m + 1) =>
      (redV (Ideal.span {d₀}) '' (LinearMap.range ZZ.Z.mulVecLin : Set (Fin (m + 1) → M.R)),
        redV (Ideal.span {d₀}) (ZZ.Z.adjugate (Fin.last m))))
    {ZZ | ZZ.Z.det = d₀} (by
      intro ZZ hZ ZZ' hZ' hJ
      change ZZ.Z.det = d₀ at hZ
      change ZZ'.Z.det = d₀ at hZ'
      apply Quotient.sound
      simp only [Prod.mk.injEq] at hJ
      exact iso_of_inv M ZZ ZZ' (hZ.trans hZ'.symm) (by rw [hZ]; exact hJ.1) (by rw [hZ]; exact hJ.2))
  refine key.subset ?_
  rintro c ⟨ZZ, hZ, rfl⟩
  exact ⟨ZZ, hZ, rfl⟩

end Fin2

section Fin3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem isLowUni_uLow {n : ℕ} (x : IL n → E) : IsLowUni (uLow x) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp [uLow, hab'.ne, not_lt.mpr hab'.le]
  · intro a
    simp [uLow]

theorem isUpUni_uUp {n : ℕ} (w : Pt E n) (y : IN w → E) : IsUpUni (uUp w y) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    simp [uUp, hab'.ne', not_lt.mpr hab'.le]
  · intro a
    simp [uUp]

theorem nonempty_of_nIso_ne (M : Model F E) {m : ℕ} (ZZ ZZ' : M.Mat (m + 1)) (h : M.nIso ZZ ZZ' ≠ 0) :
    Nonempty (M.Iso ZZ ZZ') := by
  exact (Nat.card_ne_zero.mp h).1

theorem exists_mat_of_BB_ne (M : Model F E) {m : ℕ} (w : Pt E (m + 1)) (c : M.Cls m) (hc : M.BB w c ≠ 0) :
    ∃ ZZ : M.Mat (m + 1), ((ZZ.Z.det : M.R) : E) = w.mat.det ∧ Quotient.mk (M.isoSetoid m) ZZ = c := by
  obtain ⟨xy, hxy⟩ : ∃ xy, M.bbIntegrand w c xy ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hc
    unfold Model.BB
    simp [hcon]
  unfold Model.bbIntegrand at hxy
  simp only at hxy
  split_ifs at hxy with h
  · rw [mul_ne_zero_iff] at hxy
    have h1 := hxy.1
    rw [Nat.cast_ne_zero] at h1
    have hne := nonempty_of_nIso_ne M _ _ h1
    refine ⟨_, ?_, (Quotient.sound hne).trans (Quotient.out_eq c)⟩
    have hdet := RingHom.map_det M.R.subtype
      (Matrix.of fun a b => (⟨(uLow xy.1 * w.mat * uUp w xy.2) a b, h.1 a b⟩ : M.R))
    have hmap : M.R.subtype.mapMatrix
        (Matrix.of fun a b => (⟨(uLow xy.1 * w.mat * uUp w xy.2) a b, h.1 a b⟩ : M.R)) =
        uLow xy.1 * w.mat * uUp w xy.2 := rfl
    have hd2 : (uLow xy.1 * w.mat * uUp w xy.2).det = w.mat.det := by
      rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det E (isLowUni_uLow xy.1),
        isUpUni_det E (isUpUni_uUp w xy.2), one_mul, mul_one]
    exact (hdet.trans (congrArg Matrix.det hmap)).trans hd2
  · exact absurd rfl hxy

end Fin3

end Meas2

section Final

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem latZ_eq (M : Model F E) {n : ℕ} (ZZ : M.Mat n) :
    latZ M.R (ZZ.Z.map M.R.subtype) = LinearMap.range ZZ.Z.mulVecLin := by
  ext v
  have hc : ∀ r : M.R, algebraMap M.R E r = (r : E) := fun _ => rfl
  simp only [Formalism.DoubleCosetMeasures.latZ, Formalism.DoubleCosetMeasures.coeLin, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, funext fun i => Subtype.ext ?_⟩
    have := congrFun hw i
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, hc] using this
  · rintro ⟨w, rfl⟩
    refine ⟨w, funext fun i => ?_⟩
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, hc]

end Final

end Local

end Formalism.MainNotions.LocalModelPeriodLattices

end
