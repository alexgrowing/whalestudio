import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FundIotaTANeZero
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AwayExistsSelf

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseA

variable (l : ℕ) [Fact l.Prime]

theorem isCrisDR_ι : IsCrisDR l (ι l) := fun x => Loc2.lift_mk₀ _ _ _ x

theorem ι_eq : ι l = PositivityTheory.LocInh.ιCD l := (PositivityTheory.LocInh.isCrisDR_iff _).1 (isCrisDR_ι l)

theorem qB_eq : qB l = PositivityTheory.LocInh.qB l :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
    rw [RingHom.comp_apply, RingHom.comp_apply, qB, IsLocalization.lift_eq]
    exact (PositivityTheory.LocInh.qB_coe z).symm)

theorem ι_cB (y : ACris.ACris ℂ_[l] l) : ι l (cB l y) = iC l y := Loc2.lift_mk₀ _ _ _ y

end BaseA

open BaseA

theorem base_ι_inj (l : ℕ) [Fact l.Prime] : Function.Injective (ι l) := by
  rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_injective

theorem base_dom (l : ℕ) [Fact l.Prime] : IsDomain (B l) :=
  Function.Injective.isDomain (ι l) (base_ι_inj l)

theorem base_σ_one (l : ℕ) [Fact l.Prime] : σB (1 : GQ l) = RingHom.id _ :=
  RingHom.ext fun b => PositivityTheory.LocInh.σB_one b

theorem base_σ_mul (l : ℕ) [Fact l.Prime] : ∀ g h : GQ l, σB (g * h) = (σB g).comp (σB h) :=
  fun g h => RingHom.ext fun b => PositivityTheory.LocInh.σB_mul g h b

theorem base_φ_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, φ l (σB g x) = σB g (φ l x) :=
  fun g x => PositivityTheory.LocInh.φB_σB g x

theorem base_ι_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, ι l (σB g x) = σD g (ι l x) := by
  intro g x; rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_σB g x

theorem base_φ_q (l : ℕ) [Fact l.Prime] : ∀ q, φ l (qB l q) = qB l q := by
  intro q; rw [qB_eq]; exact PositivityTheory.LocInh.φB_qB q

theorem base_σ_q (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) q, σB g (qB l q) = qB l q := by
  intro g q
  apply base_ι_inj l
  rw [base_ι_σ, ι_eq, qB_eq, PositivityTheory.LocInh.ιCD_qB, PositivityTheory.LocInh.σD_oD, AlgEquiv.commutes]

theorem base_ι_q (l : ℕ) [Fact l.Prime] : ∀ q, ι l (qB l q) = qQ l q := by
  intro q; rw [ι_eq, qB_eq]; exact PositivityTheory.LocInh.fund_ιCD_qB q

theorem period_image_eq (l : ℕ) [Fact l.Prime] : ι l (t l) = tQ l := ι_cB l (tA l)

theorem base_t_unit (l : ℕ) [Fact l.Prime] : IsUnit (t l) := Loc2.isUnit_right _ _

theorem frobenius_period_holds (l : ℕ) [Fact l.Prime] : φ l (t l) = (l : B l) * t l := PositivityTheory.LocInh.φB_tB

theorem galois_period_cyclotomic (l : ℕ) [Fact l.Prime] : ∀ g : GQ l, σB g (t l) = qB l (χ g) * t l := by
  intro g; rw [qB_eq]; exact PositivityTheory.LocInh.σB_tB g

theorem base_χ_cont (l : ℕ) [Fact l.Prime] : Continuous (χ : GQ l → ℚ_[l]) :=
  by
  have h1 : Continuous (fun g : GQ l => ((DeRhamTwist.Twist.chi0 l g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (DeRhamTwist.Twist.continuous_cyclotomic_character (l := l))
  have h2 : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := by
    first
    | exact PadicInt.continuous_coe
    | exact continuous_subtype_val
    | exact (Isometry.of_dist_eq fun _ _ => rfl).continuous
  exact h2.comp h1

theorem base_ι_Bst (l : ℕ) [Fact l.Prime] : ∀ x, ι l x ∈ Bst l := by
  intro x
  obtain ⟨m, n, y, h⟩ := PositivityTheory.LocInh.bcris_surj x
  have h1 := congrArg (ι l) h
  have hl : ι l (cB l (l : ACris.ACris ℂ_[l] l)) = (l : BdR l) := by rw [map_natCast, map_natCast]
  rw [map_mul, map_mul, map_pow, map_pow, hl, ι_cB, ι_cB] at h1
  have htq : iC l (tA l) = tQ l := rfl
  rw [htq] at h1
  have hl0 : (l : BdR l) ≠ 0 := by
    have := (isUnit_l l).map (ι l)
    rw [map_natCast] at this
    exact this.ne_zero
  have ht0 : tQ l ≠ 0 := DeRhamTwist.Twist.tQ_ne
  have e : ι l x = iC l y * ((l : BdR l)⁻¹) ^ m * ((tQ l)⁻¹) ^ n := by
    rw [← h1, inv_pow, inv_pow]
    field_simp
  rw [e]
  have mem : ∀ z ∈ ({((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l} : Set (BdR l)), z ∈ Bst l :=
    fun z hz => Subring.subset_closure (Or.inr hz)
  exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨y, rfl⟩))
    (Subring.pow_mem _ (mem _ (by simp)) _)) (Subring.pow_mem _ (mem _ (by simp)) _)

theorem base_u_Bst (l : ℕ) [Fact l.Prime] : uQ l ∈ Bst l :=
  Subring.subset_closure (Or.inr (by simp))

theorem base_fs_ker (l : ℕ) [Fact l.Prime] : ∀ x, φ l x = x → ι l x ∈ Plus l → ∃ q, x = qB l q := by
  intro x hφ hx
  obtain ⟨z, hz⟩ := RingHom.mem_range.1 hx
  rw [ι_eq] at hz
  obtain ⟨q, hq⟩ := PositivityTheory.LocInh.fund x hφ ((IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨z, hz.symm⟩)
  exact ⟨q, by rw [qB_eq]; exact hq.symm⟩

theorem base_fs_surj (l : ℕ) [Fact l.Prime] : ∀ z : BdR l, ∃ x, φ l x = x ∧ ι l x - z ∈ Plus l := by
  intro z
  obtain ⟨x, hφ, c, hc⟩ := PositivityTheory.LocInh.fund_onto z
  exact ⟨x, hφ, RingHom.mem_range.2 ⟨c, by rw [ι_eq]; exact hc.symm⟩⟩

end period_ring_base
