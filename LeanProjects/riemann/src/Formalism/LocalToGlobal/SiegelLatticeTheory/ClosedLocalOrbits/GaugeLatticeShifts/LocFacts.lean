import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.TrDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGSmall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DApprox
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocLatSat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocLatEq
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.DensInertDisplayHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TrDualLoc

noncomputable section

open scoped Classical BigOperators

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef
  Formalism.L2.SG.Saturated Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DualLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) →
    ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Loc.resChar p] Fp (c * ι t)‖ ≤ 1

namespace LocFacts

variable {D : D7}

theorem lf_span_coe_of_eq {Ep M : Type*} [CommRing Ep] [AddCommGroup M] [Module Ep M] {S T : Subring Ep}
    (h : S = T) (X : Set M) : ((Submodule.span S X : Submodule S M) : Set M) = (Submodule.span T X : Set M) := by
  subst h; rfl

def phiE (D : D7) : (VS D).V ≃ₗ[𝓞 D.host.E] (Fin (nV D) → D.host.E) :=
  ((VS D).frame.equivFun).restrictScalars (𝓞 D.host.E)

def phi (D : D7) : (VS D).V →ₗ[𝓞 D.host.E] (Fin (nV D) → D.host.E) := (phiE D).toLinearMap

theorem localBaseChange_eq (p : PlF D) (x : (VS D).V) : baseChange₂ D p x = PI.LocLatEq.bc (D.s.atP p) (phi D x) := by
  funext i
  simp [baseChange₂, PI.LocLatEq.bc, phi, phiE, Module.Basis.equivFun_apply]

theorem lf_img_eq (p : PlF D) (L : Submodule (𝓞 D.host.E) (VS D).V) :
    baseChange₂ D p '' (L : Set (VS D).V) = PI.LocLatEq.bc (D.s.atP p) '' ((L.map (phi D) : Submodule _ _) : Set _) := by
  rw [Submodule.map_coe, Set.image_image]
  exact Set.image_congr (fun x _ => localBaseChange_eq p x)

theorem localLattice_coe (Z : LocDat D) (p : PlF D) (L : Submodule (𝓞 D.host.E) (VS D).V) :
    (lattice₂ D Z.M p L : Set (Vp D p)) = (PI.LocLatEq.latL (D.s.atP p) (L.map (phi D)) : Set _) := by
  unfold lattice₂ PI.LocLatEq.latL
  rw [lf_img_eq]
  exact lf_span_coe_of_eq (Z.agree p).2.2.2.1 _

theorem lf_mem_map_phi (L : Submodule (𝓞 D.host.E) (VS D).V) (s : 𝓞 D.host.E) (x : (VS D).V) :
    s • phi D x ∈ L.map (phi D) ↔ s • x ∈ L := by
  have h1 : s • phi D x = phiE D (s • x) := by simp [phi]
  rw [h1]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = s • x := (phiE D).injective (by simpa [phi] using hxy)
    exact this ▸ hy
  · intro hx
    exact ⟨s • x, hx, by simp [phi]⟩

theorem locEqC_of_stmt (h : PI.LocLatEq.Stmt) (Z : LocDat D) : LocEqC D Z := by
  intro p A B hA hB
  have key := h _ _ (Formalism.BasicNotions.Examples₂.finrank_FE D.host) _ p (D.s.atP p) (nV D) (A.map (phi D)) (B.map (phi D))
    (hA.map _) (hB.map _)
  rw [← SetLike.coe_set_eq, localLattice_coe, localLattice_coe, SetLike.coe_set_eq, key]
  refine forall_congr' fun P => imp_congr_right fun _ => ?_
  rw [SetLike.ext_iff]
  have hm : ∀ (L : Submodule (𝓞 D.host.E) (VS D).V) (v : (VS D).V),
      (haveI := P.isPrime; v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) ↔
        ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • phi D v ∈ L.map (phi D) := by
    intro L v
    simp only [lf_mem_map_phi]
    exact Iff.rfl
  constructor
  · intro H v
    exact (hm A v).trans ((H (phi D v)).trans (hm B v).symm)
  · intro H y
    obtain ⟨v, rfl⟩ : ∃ v, phi D v = y := ⟨(phiE D).symm y, by simp [phi]⟩
    exact (hm A v).symm.trans ((H v).trans (hm B v))

theorem locSatC_of_stmt (h : PI.LocLatSat.Stmt) (Z : LocDat D) : LocSatC D Z := by
  intro p Λ W hΛ
  have hmap : (Λ ⊓ toO (VS D) W).map (phi D) =
      Λ.map (phi D) ⊓ (W.map (VS D).frame.equivFun.toLinearMap).restrictScalars (𝓞 D.host.E) := by
    rw [Submodule.map_inf (phi D) (fun a c hac => (phiE D).injective (by simpa [phi] using hac))]
    congr 1
  have hW : baseChange₂ D p '' (W : Set (VS D).V) =
      PI.LocLatSat.bc (D.s.atP p) '' ((W.map (VS D).frame.equivFun.toLinearMap : Submodule _ _) : Set _) := by
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun x _ => localBaseChange_eq p x)
  have key := h _ _ _ p (D.s.atP p) (nV D) (Λ.map (phi D)) (W.map (VS D).frame.equivFun.toLinearMap) (hΛ.map _)
  rw [localLattice_coe, localLattice_coe, hmap, hW]
  exact key

end LocFacts

theorem locSatC_holds (D : D7) (Z : LocDat D) : LocSatC D Z :=
  LocFacts.locSatC_of_stmt inf_eq_inter_span Z

theorem locEqC_of (h : PI.LocLatEq.Stmt) (D : D7) (Z : LocDat D) : LocEqC D Z :=
  LocFacts.locEqC_of_stmt h Z

namespace LocFacts

open PI.CntNotIntW

variable {D : D7}

section Diff

attribute [local instance] LocCP.factRes

variable (p : PlF D)

theorem lf_psiE_one (z : (D.s.atP p).Ep) (hz : ‖LocCP.trQ p z‖ ≤ 1) : (D.s.atP p).psiE z = 1 := by
  obtain ⟨a, ⟨n, hden⟩, hle, heq⟩ := (D.s.atP p).psiE_def z
  change ‖LocCP.trQ p z - (a : ℚ_[Loc.resChar p])‖ ≤ 1 at hle
  have ha : ‖((a : ℚ) : ℚ_[Loc.resChar p])‖ ≤ 1 := by
    have e : ((a : ℚ) : ℚ_[Loc.resChar p]) = LocCP.trQ p z + -(LocCP.trQ p z - (a : ℚ_[Loc.resChar p])) := by ring
    rw [e]
    refine (Padic.nonarchimedean _ _).trans (max_le hz ?_)
    rw [norm_neg]; exact hle
  have h1 := LocCP.den_one_of (Loc.resChar p) a n hden ha
  have ha' : ((a.num : ℚ) : ℂ) = (a : ℂ) := by rw [Rat.coe_int_num_of_den_eq_one h1]
  rw [heq, ← ha', Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I a.num

theorem lf_tr_th : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (LocCP.th p) = 0 := by
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have h := Algebra.trace_eq_of_algEquiv (D.s.atP p).cj (LocCP.th p)
  rw [LocCP.cj_th, map_neg] at h
  have h2 : (2 : (D.s.atP p).Fp) * Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (LocCP.th p) = 0 := by
    linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem lf_tr_eq (y : (D.s.atP p).Ep) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep y) =
      y + (D.s.atP p).cj y := by
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  obtain ⟨a, b, rfl⟩ := LocCP.repr_th p y
  have ht : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * LocCP.th p) = 0 := by
    rw [← Algebra.smul_def, map_smul, lf_tr_th, smul_zero]
  rw [map_add, ht, add_zero, Algebra.trace_algebraMap, (D.s.atP p).rank, map_add, map_mul,
    AlgEquiv.commutes, AlgEquiv.commutes, LocCP.cj_th]
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  push_cast
  ring

theorem lf_cj_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) : (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map (((D.s.atP p).cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars
    𝒪[(D.s.atP p).Fp])

theorem lf_int_of_alg (c : (D.s.atP p).Fp) (hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O) :
    c ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hc
  have hinj : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) :=
    RingHom.injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep)
  have hc' : IsIntegral 𝒪[(D.s.atP p).Fp] c := (isIntegral_algebraMap_iff hinj).1 hc
  exact (Valuation.integer.integers (valuation (D.s.atP p).Fp)).mem_of_integral hc'

theorem lf_tr_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) :
    Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep y ∈ 𝒪[(D.s.atP p).Fp] := by
  apply lf_int_of_alg
  rw [lf_tr_eq]
  exact add_mem hy (lf_cj_mem p y hy)

theorem lf_trQ_mul (z : (D.s.atP p).Fp) (y : (D.s.atP p).Ep) :
    LocCP.trQ p (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z * y) =
      Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (z * Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep y) := by
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  haveI : FiniteDimensional ℚ_[Loc.resChar p] (D.s.atP p).Fp := (D.s.atP p).qlFin
  unfold LocCP.trQ
  letI := ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).comp
    (algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[Loc.resChar p] (D.s.atP p).Fp (D.s.atP p).Ep :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [← Algebra.trace_trace (S := (D.s.atP p).Fp), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem lf_dual_le (Z : LocDat D) (z : (D.s.atP p).Fp)
    (hz : ∀ c ∈ 𝒪[(D.s.atP p).Fp], ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * z)‖ ≤ 1) :
    z * Z.δ p ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := Z.agree p
  apply lf_int_of_alg
  rw [← hO]
  apply ((Z.M p).L.additive_character_dual_ring _).1
  intro y hy
  rw [hpsi]
  have e : -(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (z * Z.δ p) * y *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z * (-y) := by
    have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
    rw [map_mul]
    linear_combination (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z * y)) * h1
  rw [e]
  apply lf_psiE_one
  rw [lf_trQ_mul, mul_comm]
  rw [hO] at hy
  exact hz _ (lf_tr_mem p _ (neg_mem hy))

theorem unitPart_mem₂ : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O := by
  have hE : (D.s.atP p).ιE (uP p : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp) := by
    rw [← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]
  rw [hE]
  apply algMap_mem_O D p
  have hℓ : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have key : ∃ n : ℕ, ¬ Loc.resChar p ∣ n ∧ (uP p : ℚ) = 1 / n := by
    unfold uP gpart Lat.gS
    have h0 : (D.host.g 0 : ℚ) ≠ 0 := by exact_mod_cast hg0.ne_zero
    have h1 : (D.host.g 1 : ℚ) ≠ 0 := by exact_mod_cast hg1.ne_zero
    split_ifs with ha hb
    · refine ⟨D.host.g 1, fun hd => D.host.g_ne (ha.symm.trans ((Nat.prime_dvd_prime_iff_eq hℓ hg1).1 hd)), ?_⟩
      push_cast; field_simp
    · refine ⟨D.host.g 0, fun hd => ha ((Nat.prime_dvd_prime_iff_eq hℓ hg0).1 hd), ?_⟩
      push_cast; field_simp
    · refine ⟨D.host.g 0 * D.host.g 1, fun hd => ?_, by push_cast; field_simp⟩
      rcases (Nat.Prime.dvd_mul hℓ).1 hd with hd | hd
      · exact ha ((Nat.prime_dvd_prime_iff_eq hℓ hg0).1 hd)
      · exact hb ((Nat.prime_dvd_prime_iff_eq hℓ hg1).1 hd)
  obtain ⟨n, hn, hu⟩ := key
  obtain ⟨w, hw⟩ := BBTie.bt_natF_unit p n hn
  have hc := (D.s.atP p).char0
  have hn0 : (n : (D.s.atP p).Fp) ≠ 0 := right_ne_zero_of_mul_eq_one hw
  have : ((uP p : ℚ) : (D.s.atP p).Fp) = (w : (D.s.atP p).Fp) := by
    rw [hu]; push_cast
    field_simp
    linear_combination -hw
  rw [this]; exact w.2

end Diff

end LocFacts

namespace LocFacts

open PI.CntNotIntW
open scoped nonZeroDivisors

variable {D : D7}

section Diff2

attribute [local instance] LocCP.factRes

variable (p : PlF D)

abbrev cP (Z : LocDat D) : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)

theorem isUnit_localConstant (Z : LocDat D) : IsUnit (cP p Z) := by
  have hδ : Z.δ p ≠ 0 := (Z.agree p).2.1
  obtain ⟨n, hn⟩ := unitAt_mul_natCast D p
  have hu : (uP p : D.host.E) ≠ 0 := by
    have : (uP p : ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hn
    exact_mod_cast this
  exact ((IsUnit.mk0 _ hδ).map _).mul ((IsUnit.mk0 _ hu).map _)

theorem lf_ddS_inv : (ddS D)⁻¹ = FractionalIdeal.extendedHom D.host.E (𝓞 D.host.E)
    (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F)) := by
  have h1 : ddS D = FractionalIdeal.extendedHom D.host.E (𝓞 D.host.E)
      ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) := by
    rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]; rfl
  rw [h1, coeIdeal_differentIdeal ℤ ℚ D.host.F, map_inv₀, inv_inv]

theorem lf_mem_inv (hDL : DualLoc) (Z : LocDat D) (y : D.host.E) (hy : y ∈ (ddS D)⁻¹) :
    (D.s.atP p).ιE y * cP p Z ∈ (D.s.atP p).O := by
  rw [lf_ddS_inv, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have htr : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n := by
      rw [SetLike.mem_coe, FractionalIdeal.mem_dual
        (one_ne_zero : (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) ≠ 0)] at ht
      intro a
      obtain ⟨n, hn⟩ := ht (algebraMap _ _ a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩
    haveI := (D.s.atP p).lf
    have hz := hDL D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont (D.s.atP p).qlFin (D.s.atP p).ιF
      (D.s.atP p).dense (D.s.atP p).val t htr
    have hm := LocFacts.lf_dual_le p Z _ hz
    have e : (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) * cP p Z =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF t * Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := by
      rw [(D.s.atP p).compat, map_mul, cP, mul_assoc]
    rw [e]
    exact mul_mem (algMap_mem_O D p _ hm) (unitPart_mem₂ p)
  | zero => rw [map_zero, zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact mul_mem (iE_mem_O D p a) hx

theorem lf_mem_pow (hDL : DualLoc) (Z : LocDat D) :
    ∀ (m : ℕ) (x : D.host.E), x ∈ (ddS D)⁻¹ ^ m → (D.s.atP p).ιE x * cP p Z ^ m ∈ (D.s.atP p).O
  | 0, x, hx => by
      rw [pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [pow_zero, mul_one]; exact iE_mem_O D p o
  | m + 1, x, hx => by
      rw [pow_succ] at hx
      refine FractionalIdeal.mul_induction_on hx ?_ ?_
      · intro i hi j hj
        have := mul_mem (lf_mem_pow hDL Z m i hi) (lf_mem_inv p hDL Z j hj)
        rw [map_mul, pow_succ]
        convert this using 1
        ring
      · intro a b ha hb
        rw [map_add, add_mul]
        exact add_mem ha hb

end Diff2

end LocFacts

open PI.CntNotIntW in

theorem locDiffC_of (hDL : DualLoc) (D : D7) (Z : LocDat D) : LocDiffC D Z := by
  intro p a
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -((D.R.rS - a.val : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : a.val ≤ D.R.rS)]
  have hpow : ∀ m : ℕ, (ddS D) ^ (-(m : ℤ)) = (ddS D)⁻¹ ^ m := fun m => by rw [zpow_neg, zpow_natCast, inv_pow]
  have hfr : frFac Z.δ p a = Ring.inverse (LocFacts.cP p Z ^ (D.R.rS - a.val)) := rfl
  rw [hexp, hpow, hfr]
  have hc := LocFacts.isUnit_localConstant p Z
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    have hmem := LocFacts.lf_mem_pow p hDL Z (D.R.rS - a.val) x hx
    refine ⟨⟨(D.s.atP p).ιE x * LocFacts.cP p Z ^ (D.R.rS - a.val), by rw [hO]; exact hmem⟩, ?_⟩
    show ((D.s.atP p).ιE x * LocFacts.cP p Z ^ (D.R.rS - a.val)) *
      Ring.inverse (LocFacts.cP p Z ^ (D.R.rS - a.val)) = _
    rw [mul_assoc, Ring.mul_inverse_cancel _ (hc.pow _), mul_one]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨x, hx, -, w, hw, hxw⟩ := locGen_of (locDiff_of trace_dual_lattice
      (dualApprox_of small_powers_bound tensorLiftSurjective) small_powers_bound) dual_lattice_powers D Z.δ Z.M Z.agree p (D.R.rS - a.val)
    rw [hpow] at hx
    have e : Ring.inverse (LocFacts.cP p Z ^ (D.R.rS - a.val)) = w * (D.s.atP p).ιE x := hxw
    rw [SetLike.mem_coe, e]
    have hw' : w ∈ (Z.M p).L.O := by rw [hO]; exact hw
    exact Submodule.smul_mem _ (⟨w, hw'⟩ : (Z.M p).L.O) (Submodule.subset_span ⟨x, hx, rfl⟩)

namespace LocFacts

variable {D : D7}

section Unimod

variable (Z : LocDat D) (p : PlF D)

theorem localForm_add_left₂ (x x' y : Vp D p) : LocFacts₂ Z.M p (x + x') y = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x' y := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left₂ (a : (D.s.atP p).Ep) (x y : Vp D p) : LocFacts₂ Z.M p (a • x) y = a * LocFacts₂ Z.M p x y := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem localForm_add_right (x y y' : Vp D p) : LocFacts₂ Z.M p x (y + y') = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x y' := by
  simp only [LocFacts₂, Pi.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_right (a : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ Z.M p x (a • y) = (Z.M p).L.cj a * LocFacts₂ Z.M p x y := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem localForm_zero_left₂ (y : Vp D p) : LocFacts₂ Z.M p 0 y = 0 := by
  simp [LocFacts₂]

theorem localForm_zero_right (x : Vp D p) : LocFacts₂ Z.M p x 0 = 0 := by
  simp [LocFacts₂]

theorem lf_hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1

theorem lf_cjM_mem (a : (D.s.atP p).Ep) (ha : a ∈ (Z.M p).L.O) : (Z.M p).L.cj a ∈ (Z.M p).L.O := by
  rw [Z.hcj p, lf_hO Z p] at *
  exact lf_cj_mem p a ha

theorem lf_mem_hdual {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ Formalism.E.hdual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

theorem lf_int_of_unimod {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {a b : (VS D).V} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p b) ∈ (Z.M p).L.O := by
  rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
  have ha' : a ∈ Formalism.E.hdual (VS D).hT Λ := by
    have : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [← this] at ha
    exact ha
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((lf_mem_hdual).1 ha' b hb)
  rw [← ho, lf_hO Z p]
  exact PI.CntNotIntW.iE_mem_O D p o

theorem lf_form_int {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {x y : Vp D p} (hx : x ∈ lattice₂ D Z.M p Λ) (hy : y ∈ lattice₂ D Z.M p Λ) :
    LocFacts₂ Z.M p x y ∈ (Z.M p).L.O := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact lf_int_of_unimod Z p hU ha hb
    | zero => rw [localForm_zero_right]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [localForm_add_right]; exact add_mem h1 h2
    | smul o y _ h =>
      rw [Subring.smul_def, localForm_smul_right]
      exact mul_mem (lf_cjM_mem Z p _ o.2) h
  | zero => rw [localForm_zero_left₂]; exact zero_mem _
  | add x x' _ _ h1 h2 => rw [localForm_add_left₂]; exact add_mem h1 h2
  | smul o x _ h =>
    rw [Subring.smul_def, localForm_smul_left₂]
    exact mul_mem o.2 h

theorem lf_riesz (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

theorem lf_riesz_lat {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (f : Λ →ₗ[𝓞 D.host.E] 𝓞 D.host.E) :
    ∃ μ ∈ Λ, ∀ y : Λ, (VS D).hT μ (y : (VS D).V) = ((f y : 𝓞 D.host.E) : D.host.E) := by
  classical
  obtain ⟨s, _, b, hb, hsΛ⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 D.host.E) Λ hL.span_eq_top
  let φ : (VS D).V →ₗ[D.host.E] D.host.E := b.constr D.host.E
    (fun j => ((f ⟨(j : (VS D).V), hsΛ j.2⟩ : 𝓞 D.host.E) : D.host.E))
  have hφ : ∀ y : Λ, φ (y : (VS D).V) = ((f y : 𝓞 D.host.E) : D.host.E) := by
    intro y
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) Finset.univ
      (fun j => b.equivFun (y : (VS D).V) j)
    choose c hc using fun j => hd j (Finset.mem_univ j)
    have hy : ((d : 𝓞 D.host.E) • y : Λ) = ∑ j, c j • (⟨(j : (VS D).V), hsΛ j.2⟩ : Λ) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sum]
      conv_lhs => rw [← b.sum_equivFun (y : (VS D).V)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hb j, ← algebraMap_smul D.host.E (c j), hc j, Algebra.smul_def, ← smul_smul,
        algebraMap_smul]
    have h1 := congrArg (fun z => ((f z : 𝓞 D.host.E) : D.host.E)) hy
    simp only [map_smul, map_sum, smul_eq_mul] at h1
    push_cast at h1
    have hd0 : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      have := nonZeroDivisors.ne_zero d.2
      exact_mod_cast this
    have h2 : ((d : 𝓞 D.host.E) : D.host.E) * φ (y : (VS D).V) =
        ∑ j, ((c j : 𝓞 D.host.E) : D.host.E) * ((f ⟨(j : (VS D).V), hsΛ j.2⟩ : 𝓞 D.host.E) : D.host.E) := by
      rw [show φ (y : (VS D).V) = _ from Module.Basis.constr_apply_fintype (S := D.host.E) b _ _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, ← mul_assoc]
      congr 1
      have := hc j
      rw [Algebra.smul_def] at this
      exact this.symm
    exact mul_left_cancel₀ hd0 (h2.trans h1.symm)
  obtain ⟨μ, hμ⟩ := lf_riesz φ
  refine ⟨μ, ?_, fun y => (hμ y).trans (hφ y)⟩
  have : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  rw [← this]
  show μ ∈ Formalism.E.hdual (VS D).hT Λ
  rw [lf_mem_hdual]
  intro y hy
  rw [← (VS D).herm.eq μ y, hμ, hφ ⟨y, hy⟩]
  refine Submodule.mem_one.2 ⟨⟨starRingEnd D.host.E ((f ⟨y, hy⟩ : 𝓞 D.host.E) : D.host.E),
    map_isIntegral_int (starRingEnd D.host.E) (RingOfIntegers.isIntegral_coe _)⟩, rfl⟩

end Unimod

end LocFacts

theorem locUnimodC_holds (D : D7) (Z : LocDat D) : LocUnimodC D Z := by
  intro p Λ hL hU x
  constructor
  · intro hx y hy
    exact LocFacts.lf_form_int Z p hU hx hy
  · intro h
    classical
    obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := D.host.E) Λ hL.fg
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    choose μ hμΛ hμ using fun i => LocFacts.lf_riesz_lat hL hU (f i)

    have hV : ∀ v : (VS D).V, v = ∑ i, (VS D).hT (μ i) v • ((g i : Λ) : (VS D).V) := by
      let L2 : (VS D).V →ₗ[D.host.E] (VS D).V := ∑ i, ((VS D).hT (μ i)).smulRight ((g i : Λ) : (VS D).V)
      have hL2 : ∀ v, L2 v = ∑ i, (VS D).hT (μ i) v • ((g i : Λ) : (VS D).V) := by
        intro v; simp [L2]
      have heq : LinearMap.id = L2 := by
        apply LinearMap.ext_on hL.span_eq_top
        intro y hy
        have e1 := congrArg (fun z : Λ => (z : (VS D).V)) (hgf ⟨y, hy⟩)
        rw [LinearMap.id_apply, hL2]
        refine e1.trans ?_
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, ← algebraMap_smul D.host.E, hμ i ⟨y, hy⟩]
      intro v
      rw [← hL2, ← heq, LinearMap.id_apply]

    have hVp : ∀ w : Vp D p, w = ∑ i, LocFacts₂ Z.M p w (baseChange₂ D p (μ i)) • baseChange₂ D p ((g i : Λ) : (VS D).V) := by
      intro w
      have hw : w ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        have e : ∀ i, LocFacts₂ Z.M p (baseChange₂ D p v) (baseChange₂ D p (μ i)) = (D.s.atP p).ιE ((VS D).hT (μ i) v) := by
          intro i; rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
        simp only [e, ← baseChange_smul₂]
        rw [← map_sum, ← hV v]
      | zero => simp [LocFacts.localForm_zero_left₂]
      | add w w' _ _ h1 h2 =>
        simp only [LocFacts.localForm_add_left₂, add_smul, Finset.sum_add_distrib]
        rw [← h1, ← h2]
      | smul a w _ h =>
        simp only [LocFacts.localForm_smul_left₂, mul_smul]
        rw [← Finset.smul_sum, ← h]
    rw [hVp x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : LocFacts₂ Z.M p x (baseChange₂ D p (μ i)) ∈ (Z.M p).L.O :=
      h _ (Submodule.subset_span ⟨μ i, hμΛ i, rfl⟩)
    have hg : baseChange₂ D p ((g i : Λ) : (VS D).V) ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨_, (g i).2, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hc⟩ : (Z.M p).L.O) hg

theorem dualLoc_holds : DualLoc := trace_dual_local

theorem locDiffC_holds (D : D7) (Z : LocDat D) : LocDiffC D Z := locDiffC_of dualLoc_holds D Z

theorem locEqC_holds (D : D7) (Z : LocDat D) : LocEqC D Z := locEqC_of eq_iff_locallyEq D Z

theorem bbTie_holds (D : D7) (Z : LocDat D) : BBTie D Z :=
  bbTie_of Z (locEqC_holds D Z) (locSatC_holds D Z) (locDiffC_holds D Z)

theorem frameGenLoc_holds (D : D7) (Z : LocDat D) {u u' : D.what₂.Word}
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F') (hMI : MplusIndep Λ (lf D F0) (gS D) F')
    (hG : Gval (lf D F0) F' ≠ 0) :
    IsGeneric Λ (gS D) (lf D F0) F' ↔
      ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) :=
  frameGenLoc_of' Formalism.L2.SG.Closed.DNeZeroAt_holds Z (locEqC_holds D Z) (locSatC_holds D Z) (locDiffC_holds D Z)
    (locUnimodC_holds D Z) F0 Λ F' hR hPD hMI hG

end Formalism.L2.SG.Pf
