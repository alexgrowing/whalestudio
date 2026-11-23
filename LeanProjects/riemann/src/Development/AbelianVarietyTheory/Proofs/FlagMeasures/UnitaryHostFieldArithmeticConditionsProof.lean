import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem places : GlobalTheory.DegVol.IsPlaces (embS D) := by
  have := D.host.toHostAx.isCMField_hostE
  have : IsGalois ℚ D.host.E := D.host.toHostAx.hostE_isGalois
  have hcc : ∀ g : D.R.GG, (D.R.toFrame.cc * g).1.2 = - g.1.2 := by
    intro g
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  have hemb : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embS D τ x = D.host.φ₀ (D.host.gal.symm (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have hconj : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    fun y => D.host.toHostAx.conjE_apply _ y
  refine ⟨fun τ a => D.sp.cm.cmUnram.2.1 _ a, fun w => ?_⟩

  have key : ∀ τ₁ τ₂ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ₁) =
      NumberField.InfinitePlace.mk (embS D τ₂) → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have h1 := (D.eTau τ₁).2
    have h2 := (D.eTau τ₂).2
    rw [Formalism.HC.Frame.mem_Psi_iff] at h1 h2
    apply D.eTau.injective
    apply Subtype.ext
    apply D.host.gal.symm.injective
    rcases h with h | h
    · ext x
      apply D.host.φ₀.injective
      have := DFunLike.congr_fun h x
      rwa [hemb, hemb] at this
    · exfalso
      have heq : D.host.conj * D.host.gal.symm (D.eTau τ₁ : D.R.GG) =
          D.host.gal.symm (D.eTau τ₂ : D.R.GG) := by
        ext x
        apply D.host.φ₀.injective
        have := DFunLike.congr_fun h x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hemb, hemb] at this
        rw [AlgEquiv.mul_apply, hconj]
        exact this
      have h3 := congrArg (fun g : D.R.GG => g.1.2) (congrArg D.host.gal heq)
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      rw [show D.host.gal D.host.conj = D.R.toFrame.cc from D.host.gal.apply_symm_apply _,
        hcc, h1, h2] at h3
      exact absurd h3 (by decide)

  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
    D.host.φ₀ w.embedding (Subsingleton.elim _ _)
  have hwρ : ∀ x, D.host.φ₀ (σ.symm x) = w.embedding x := fun x => by rw [← hσ]; rfl
  have hex : ∃ τ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ) = w := by
    by_cases hgP : D.host.gal σ.symm ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hgP⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hgP⟩) = w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply]
        simp only [MulEquiv.symm_apply_apply]
        exact hwρ x
      rw [this, NumberField.InfinitePlace.mk_embedding]
    · have hg' : D.R.toFrame.cc * D.host.gal σ.symm ∈ D.R.Psi := by
        rw [Formalism.HC.Frame.mem_Psi_iff] at hgP ⊢
        rw [hcc]
        rcases Int.units_eq_one_or (D.host.gal σ.symm).1.2 with h | h
        · exact absurd h hgP
        · rw [h, neg_neg]
      refine ⟨D.eTau.symm ⟨_, hg'⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hg'⟩) = NumberField.ComplexEmbedding.conjugate w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        simp only [map_mul, MulEquiv.symm_apply_apply, AlgEquiv.mul_apply]
        rw [show D.host.gal.symm D.R.toFrame.cc = D.host.conj from rfl, hconj, hwρ]
      rw [this, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  exact ⟨τ, hτ, fun τ' hτ' => key τ' τ (hτ'.trans hτ.symm)⟩

theorem finrank_eq : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.toHostAx.finrank_cmField]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem fDeg_eq : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  have := D.host.toHostAx.isCMField_hostE
  have h1 := NumberField.IsTotallyComplex.finrank (K := D.host.E)
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem vInv_eq : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  have h1 := GlobalTheory.TypeAsm.HostArith.fDeg_eq D
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  rw [h1, h2]
  push_cast
  rfl

theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  have := D.host.toHostAx.isCMField_hostE
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

private theorem absNorm_dI_eq_abs_discr_of_discr_eq_sq (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = |(NumberField.discr D.host.E : ℝ)| := by
  have := D.host.toHostAx.isCMField_hostE
  unfold dI
  rw [Ideal.absNorm_algebraMap, GlobalTheory.TypeAsm.HostArith.finrank_O,
    NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), hd]
  push_cast
  rw [abs_pow, Nat.cast_natAbs, Int.cast_abs]

private theorem one_le_host_v : 1 ≤ D.host.v := by
  have h := D.host.toHostAx.der.rd_sq_ge
  have ho : (1 : ℝ) ≤ D.R.toFrame.ord := by exact_mod_cast D.R.toFrame.ord_pos
  have hrd : D.host.rdE = D.host.toHostRaw.rd := rfl
  have hnn : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [← hrd] at h
  unfold Formalism.BasicNotions.Host.v
  nlinarith

theorem absNorm_dI (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = (2 * D.host.v) ^ (2 * D.R.f) := by
  rw [absNorm_dI_eq_abs_discr_of_discr_eq_sq D hd]
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  have hf : (0 : ℝ) < ((2 * D.R.f : ℕ) : ℝ) := by
    rw [← h2]; exact_mod_cast Module.finrank_pos
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [hv]
  unfold Formalism.BasicNotions.Host.rdE
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
    inv_mul_cancel₀ hf.ne', Real.rpow_one]

theorem dI_star : ∀ x ∈ dI D, ∃ y ∈ dI D, (y : D.host.E) = star (x : D.host.E) := by
  have := D.host.toHostAx.isCMField_hostE
  intro x hx

  have key : dI D ≤ Ideal.comap (NumberField.IsCMField.ringOfIntegersComplexConj D.host.E) (dI D) := by
    show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap]
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hi
  exact ⟨NumberField.IsCMField.ringOfIntegersComplexConj D.host.E x, key hx, rfl⟩

theorem dI_ne_bot (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : dI D ≠ ⊥ := by
  intro h
  have h1 := absNorm_dI D hd
  rw [h, Ideal.absNorm_bot, Nat.cast_zero] at h1
  have hv := one_le_host_v D
  have : (0 : ℝ) < (2 * D.host.v) ^ (2 * D.R.f) := pow_pos (by linarith) _
  linarith

theorem rank_VS : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [(VS D).rank_eq]
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS] at h ⊢
  show (D.sp.Y 0).rank = _
  rw [h]
  omega

theorem two_le_gS : 2 ≤ gS D := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  show 2 ≤ D.host.g 0 * D.host.g 1
  nlinarith

private theorem card_Tau_eq_f : Fintype.card D.what₂.Tau = D.R.f := by
  have hP := (HostArith.places D).2
  have hb : Function.Bijective (fun τ => NumberField.InfinitePlace.mk (embS D τ)) :=
    ⟨fun a b h => (hP _).unique h rfl, fun w => (hP w).exists⟩
  rw [Fintype.card_of_bijective hb]
  exact HostArith.fDeg_eq D

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hostC : HostC := by
  intro D large₂ hStd
  obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩ := hStd
  obtain ⟨⟨-, hD0, -⟩, -⟩ := hK
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := hD0
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := D.host.toHostAx.der.discr_sq
  exact ⟨D.sp.cm.cmUnram, HostArith.places D, HostArith.vInv_eq D, HostArith.one_le_host_v D,
    HostArith.fDeg_eq D, HostArith.card_Tau_eq_f D, HostArith.finrank_eq D, HostArith.dI_ne_bot D hd,
    HostArith.dI_star D, HostArith.absNorm_dI D hd, HostArith.rank_VS D, HostArith.two_le_gS D,
    fun u => ⟨(D.mem u).A.T_prime, (hsplit u).1⟩⟩

end GlobalTheory.TypeAsm
