import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualOfDualFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOneStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FunFix

section Abstract

variable {A : Type} [CommRing A] {k : ℕ} (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A)

theorem hform_sub_left (x x' y : Fin k → A) : hform τ J (x - x') y = hform τ J x y - hform τ J x' y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y y' : Fin k → A) : hform τ J x (y - y') = hform τ J x y - hform τ J x y' := by
  simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_swap (c : A) (x y : Fin k → A) : hform τ J x (τ c • y) = hform τ J (c • x) y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_unitary {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform τ J x y := by
  have h : cT τ g.1 * J * g.1 = J := hg
  rw [GlobalTheory.DualFrame.hform_mulVec, mulVec_mulVec, h, GlobalTheory.DualFrame.hform_eq_dot]

theorem hform_move {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J x (g.1 *ᵥ y) = hform τ J ((g⁻¹).1 *ᵥ x) y := by
  rw [← hform_unitary τ J hg ((g⁻¹).1 *ᵥ x) y, mulVec_mulVec, Units.mul_inv, one_mulVec]

variable {τ J} {O : Subring A} {L D : Submodule O (Fin k → A)}

theorem stab_dual (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O) {g : GL (Fin k) A}
    (hg : g ∈ level τ J L) : g ∈ stabGL D := by
  obtain ⟨hu, hs⟩ := hg
  intro y
  rw [hD, hD]
  constructor
  · intro h x hx
    rw [hform_move τ J hu]
    exact h _ (((stabGL L).inv_mem hs x).1 hx)
  · intro h x hx
    rw [← hform_unitary τ J hu]
    exact h _ ((hs x).1 hx)

theorem triv_iff_stabFun (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ D, hform τ J x y ∈ O)
    {M : Type} [AddCommGroup M] [Module O M] (f : D →ₗ[O] M) (hf0 : f ≠ 0)
    (hfL : ∀ x : D, x.1 ∈ L → f x = 0) (e : O) (hτe : τ e = 1 - e) (hact : ∀ m : M, e • m = m)
    (hfield : ∀ a : O, (∃ b : O, b * a * e = e) ∨ ∀ x ∈ D, (e * a) • x ∈ L)
    (d : Fin k → A) (hd : d ∈ D) (hgen : ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ L)
    {g : GL (Fin k) A} (hg : g ∈ level τ J L) :
    (∀ x ∈ D, (g.1 - 1) *ᵥ x ∈ L) ↔ g ∈ stabFun D f := by
  have hgD := stab_dual hD hg
  have hval : ∀ (x : D) (a : O), x.1 - a.1 • d ∈ L → f x = a • f ⟨d, hd⟩ := by
    intro x a h
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact hfL _ h
  have hfd : f ⟨d, hd⟩ ≠ 0 := by
    intro h
    apply hf0
    ext x
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rw [hval x ⟨a, ha⟩ hx, h, smul_zero]
    rfl
  have hker : ∀ x : D, f x = 0 → e • x.1 ∈ L := by
    intro x hx0
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rcases hfield ⟨a, ha⟩ with ⟨b, hb⟩ | h
    · exfalso
      apply hfd
      rw [← hact (f ⟨d, hd⟩), ← hb, mul_smul, hact, mul_smul, ← hval x ⟨a, ha⟩ hx, hx0, smul_zero]
    · have h1 := L.add_mem (L.smul_mem e hx) (h d hd)
      have h2 : e • (x.1 - a • d) + (e * ⟨a, ha⟩) • d = e • x.1 := by
        rw [smul_sub, mul_smul]
        exact sub_add_cancel _ _
      rwa [h2] at h1
  have hhalf : ∀ g' ∈ stabFun D f, ∀ x ∈ D, e • (g'.1 *ᵥ x - x) ∈ L := by
    rintro g' ⟨h1, h2⟩ x hx
    refine hker (⟨g'.1 *ᵥ x, (h1 x).1 hx⟩ - ⟨x, hx⟩) ?_
    rw [map_sub, sub_eq_zero]
    exact h2 ⟨x, hx⟩
  constructor
  · intro h
    refine ⟨hgD, fun x => ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    refine hfL _ ?_
    have := h x.1 x.2
    rwa [sub_mulVec, one_mulVec] at this
  · intro h x hx
    rw [sub_mulVec, one_mulVec]
    have h1 := hhalf g h x hx
    have h2 : τ e • (g.1 *ᵥ x - x) ∈ L := by
      rw [hL]
      intro z hz
      rw [hform_smul_swap, hform_sub_right, hform_move τ J hg.1, ← hform_sub_left, mulVec_smul, ← smul_sub]
      exact (hD x).1 hx _ (hhalf g⁻¹ ((stabFun D f).inv_mem h) z hz)
    have h3 := L.add_mem h1 h2
    have h4 : e • (g.1 *ᵥ x - x) + τ e • (g.1 *ᵥ x - x) = g.1 *ᵥ x - x := by
      rw [hτe, sub_smul, one_smul]
      exact add_sub_cancel _ _
    rwa [h4] at h3

theorem idem_act {R : Type} [Ring R] {G : Type} [AddCommGroup G] [Module R G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : R} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleAddGroup_of_prime_card hG
  rcases IsSimpleAddGroup.eq_bot_or_eq_top_of_normal (DistribSMul.toAddMonoidHom G e).range inferInstance
    with h | h
  · left
    intro y
    exact AddSubgroup.mem_bot.1 (h ▸ ⟨y, rfl⟩)
  · right
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [h]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

theorem unit_or_dvd {K : Type} [Field K] (V : ValuationSubring K) (T : ℕ)
    (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(T : V)}) (sp : A ≃+* K × K)
    (hint : ∀ x, x ∈ O ↔ (sp x).1 ∈ V ∧ (sp x).2 ∈ V) (e : O) (he : sp e = (1, 0)) (a : O) :
    (∃ b : O, b * a * e = e) ∨ ∃ c : O, e * a = c * T := by
  have ha := ((hint a).1 a.2).1
  have hm : ∀ c : V, sp.symm (c, 0) ∈ O := fun c => by
    rw [hint, sp.apply_symm_apply]; exact ⟨c.2, zero_mem _⟩
  by_cases hu : IsUnit (⟨_, ha⟩ : V)
  · obtain ⟨b, hb⟩ := hu.exists_left_inv
    have hb' : (b : K) * (sp a).1 = 1 := congrArg Subtype.val hb
    refine Or.inl ⟨⟨_, hm b⟩, Subtype.ext (sp.injective ?_)⟩
    change sp (sp.symm (b, 0) * a * e) = sp e
    rw [map_mul, map_mul, sp.apply_symm_apply, he]
    ext <;> simp [hb']
  · have h1 : (⟨_, ha⟩ : V) ∈ IsLocalRing.maximalIdeal V := hu
    rw [hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : K) * T = (sp a).1 := by simpa using congrArg Subtype.val hc
    refine Or.inr ⟨⟨_, hm c⟩, Subtype.ext (sp.injective ?_)⟩
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, map_mul, map_mul, sp.apply_symm_apply, he, map_natCast]
    ext <;> simp [hc']

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sigR_mem (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ a ∈ intV E v, sigR σ (v.adicCompletion F) a ∈ intV E v := by
  have : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E), rfl⟩, rfl⟩)
    · show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  exact this

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L L' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ L', (T : E) • x ∈ L) : ∀ x ∈ loc v L', (T : intV E v) • x ∈ loc v L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h y hy, ?_⟩
    funext i
    simp only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

end Local

theorem trivial_iff_mem_Uloc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f bad S hT hsp hdeg v hv y hy
  obtain ⟨-, d, hd, hgen⟩ := GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f S.Lb hT hsp hdeg
    (stepLevel_tLat F E n cm.sig J T f bad S) v hv
  obtain ⟨-, hmax, sp, hsig, hdiag⟩ := (GlobalTheory.T.cmField_splitCompletely_place_structure F E cm T hT hsp).2 v hv
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  obtain ⟨B, C, hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E cm.sig n J (isUnit_iff_ne_zero.2 hdet) S.Lb
    S.Lb_fin S.Lb_span v
  obtain ⟨hD, hL, -⟩ := GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) (sigR cm.sig (v.adicCompletion F))
    (fun a => sp.injective (by rw [hsig, hsig]; rfl)) (sigR_mem _ v) n _
    (by ext i j; exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j))
    B C _ _ hBC hB hC
  have hTD := nsmul_mem_loc v T S.Lb (dualL cm.sig J S.Lb)
    fun x hx => S.Lb_dual x (GlobalTheory.DualFrame.mem_dualSet_of_mem_span _ _ _ hx)
  have key : ∀ (sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
      (∀ x, x ∈ intV E v ↔
        (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F) →
      ∀ e : intV E v, sp' e = (1, 0) → sigR cm.sig (v.adicCompletion F) e = 1 - e →
      (∀ m : S.fM v hv, e • m = m) →
      ((∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ stabFun _ (S.fT v hv)) := by
    intro sp' hint' e he hτe hact
    refine triv_iff_stabFun hD hL (S.fT v hv) (S.fT_ne v hv) (S.fT_L v hv) e hτe hact (fun a => ?_) d hd hgen hy
    refine (unit_or_dvd _ T hmax sp' hint' e he a).imp id ?_
    rintro ⟨c, hc⟩ x hx
    rw [hc, mul_smul]
    exact Submodule.smul_mem _ _ (hTD x hx)
  have he : sp.symm (1, 0) ∈ intV E v := by
    rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
  have hτ : sigR cm.sig (v.adicCompletion F) (sp.symm (1, 0)) = 1 - sp.symm (1, 0) := by
    apply sp.injective
    rw [hsig, map_sub, map_one, sp.apply_symm_apply]
    ext <;> simp [swapR]
  have hee : (⟨_, he⟩ : intV E v) * ⟨_, he⟩ = ⟨_, he⟩ := by
    apply Subtype.ext
    change sp.symm (1, 0) * sp.symm (1, 0) = sp.symm (1, 0)
    rw [← map_mul]
    simp
  rw [S.UlocAlt v hv, Subgroup.mem_inf, and_iff_right hy]
  rcases idem_act hT (S.fM_card v hv) hee with h0 | h1
  · refine key (sp.trans RingEquiv.prodComm) (fun x => (hint x).trans and_comm) (1 - ⟨_, he⟩) ?_ ?_ fun m => ?_
    · change RingEquiv.prodComm (sp (1 - sp.symm (1, 0))) = _
      rw [map_sub sp, map_one, sp.apply_symm_apply]
      ext <;> simp
    · change sigR cm.sig (v.adicCompletion F) (1 - sp.symm (1, 0)) = 1 - (1 - sp.symm (1, 0))
      rw [map_sub, map_one, hτ]
    · rw [sub_smul, one_smul, h0, sub_zero]
  · exact key sp hint ⟨_, he⟩ (sp.apply_symm_apply _) hτ h1

end GlobalTheory.St.G.FunFix
