import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetNontrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRepStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableComplexRepOfSupercuspidalUnitaryCeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercuspStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRepStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCuspidal_of_isSubquotient {n V W : Type} [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (hτ : IsCuspidal τ) (h : IsSubquotient π τ) : IsCuspidal π := by
  refine ⟨h.isSmooth hτ.1, fun s d e he => ?_⟩
  obtain ⟨S, f, hf⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e hτ.1 h
  haveI := hτ.2 s d e he
  exact hf.subsingleton

theorem exists_root_norm {ω : kˣ →* ℂˣ} (hω : IsSmoothChar ω) {b : ℕ} (hb : 0 < b) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ ∀ z, ‖((ω * ψ ^ b) z : ℂ)‖ = 1 := by
  let f : kˣ →* ℂ :=
    { toFun := fun z => ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul] }
  refine ⟨f.toHomUnits, Subgroup.isOpen_mono (H₁ := ω.ker) (fun z hz => ?_) hω, fun z => ?_⟩
  · refine Units.ext ?_
    have hz' : ω z = 1 := hz
    show ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) = 1
    rw [hz']; simp
  · have h0 : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have e : ((f.toHomUnits z : ℂˣ) : ℂ) = ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) := rfl
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, e, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), ← Real.rpow_natCast, ← Real.rpow_mul h0.le,
      neg_mul, inv_mul_cancel₀ (by positivity), Real.rpow_neg_one, mul_inv_cancel₀ h0.ne']

theorem exists_irreducible_sub {b : ℕ} (hb : 0 < b) {X : Type} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (τ : Representation ℂ (GL (Fin b) k) X) (hτ : IsCuspidal τ)
    (hz : ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ w, τ z w = c • w) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (ρ : Representation ℂ (GL (Fin b) k) Y),
      ρ.IsIrreducible ∧ IsCuspidal ρ ∧ ∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ g (ι v) := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  let S : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
    have hle : Submodule.span ℂ (Set.range fun g => τ g x) ≤
        (Submodule.span ℂ (Set.range fun g => τ g x)).comap (τ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp⟩
    exact hle hv⟩
  have hxS : x ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hnt : Nontrivial S.toSubmodule := ⟨⟨⟨x, hxS⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨Y, _, _, ρ, hρi, p, hp⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ S.toRepresentation {⟨x, hxS⟩} hnt (by
    refine Submodule.map_injective_of_injective S.toSubmodule.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show _ = Submodule.span ℂ (Set.range fun g => τ g x)
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, v, hv, rfl⟩, rfl⟩
      rw [Finset.mem_singleton.1 hv]
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, _, Finset.mem_singleton_self _, rfl⟩, rfl⟩)
  have hρc : IsCuspidal ρ := isCuspidal_of_isSubquotient hτ ⟨S, p, hp⟩
  have hSs : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, Representation.IntertwiningMap.id _, Function.surjective_id⟩ hτ.1
  obtain ⟨ω, hω, hωc⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar hρc.1 hρi
  obtain ⟨ψ, hψ, hψ1⟩ := exists_root_norm hω hb
  have hc' : IsCuspidal (twist ρ (detChar (Fin b) ψ)) := GlobalTheory.LocGL.isCuspidal_twist hρc hψ
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k b Y _ hc'
  haveI : Nontrivial Y := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρi
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨l, hl, hly⟩ := GlobalTheory.T.exists_smoothDual_ne_zero_at_vector _ _ (twist ρ (detChar (Fin b) ψ)) (fun U hU => by
    obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin b) hU
    exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, h⟩) hc'.1 y hy
  have hu := GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center _ _ _ l hl (fun h => hly (by rw [h]; rfl)) (GlobalTheory.LocGL.isIrreducible_twist hρi _) hsc
    (fun z hz => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      have h := GlobalTheory.LocGL.hasCentralChar_twist hωc ψ z
      rw [Fintype.card_fin] at h
      exact ⟨_, hψ1 z, h⟩)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal _ _ _ (twist S.toRepresentation (detChar (Fin b) ψ)) _ (twistMap p _)
    (isSmooth_twist hSs hψ.detChar) hsc hu
    (fun z hz' => by
      obtain ⟨c, hc⟩ := hz z hz'
      refine ⟨(detChar (Fin b) ψ z : ℂ) * c, fun w => ?_⟩
      rw [twist_apply, mul_smul]
      exact congrArg _ (Subtype.ext (hc w)))
    (fun h => by
      obtain ⟨w, hw⟩ := hp y
      have h1 : twistMap p (detChar (Fin b) ψ) w = y := hw
      rw [h] at h1
      exact hy h1.symm)
  refine ⟨Y, _, _, ρ, hρi, hρc, S.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun h => hι ?_, fun g v => ?_⟩
  · ext v
    exact LinearMap.congr_fun h v
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ ι g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact congrArg Subtype.val (smul_right_injective _ (Units.ne_zero _) h1)

theorem exists_map_jac₂ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      0 < b ∧ IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsCuspidal ρ ∧
      ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 := by
  classical
  have hex : ∃ b : ℕ, 0 < b ∧ ∃ (a : ℕ) (h : a + b = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) :=
    ⟨n, hn, 0, zero_add n, GlobalTheory.SmGL.JacquetEmptyFirstBlock.jacquet_nontrivial k n V π hi _⟩
  obtain ⟨hb, a, h, hnt⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  generalize Nat.find hex = b at hb h hnt hmin
  have hJc := GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing k a b n h V π hs fun r t h' h0 ht =>
    not_nontrivial_iff_subsingleton.1 fun h1 => hmin t ht ⟨h0, r, h', h1⟩
  obtain ⟨s, hspan⟩ := GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated k a b n h V π hs hi
  obtain ⟨X, _, _, τ, hτi, f, hf⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ _ s hnt hspan
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_jac₂ _ hs)
  have hτc : IsCuspidal (k := k) (n := Fin b) (τ.comp (MonoidHom.inr _ _)) :=
    isCuspidal_of_isSubquotient hJc (IsSubquotient.of_surjective (compMap f _) hf)
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτi
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin a)
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin b)
  obtain ⟨Y, _, _, ρ, hρi, hρc, hι⟩ := exists_irreducible_sub hb (τ.comp (MonoidHom.inr _ _)) hτc fun z hz =>
    GlobalTheory.LocGL.exists_eq_smul_of_isSmooth hτs hτi ⟨τ (1, z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz g.2).symm⟩
  obtain ⟨W, _, _, σ, hσs, hσi, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep _ _ X Y τ ρ hτs hτi hρi
    (GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible _ X Y (τ.comp (MonoidHom.inr _ _)) ρ hρi (GlobalTheory.LocGL.schur_GL hρc.1 hρi)) hι
  refine ⟨a, b, h, W, Y, _, _, _, _, σ, ρ, hb, hσs, hσi, hρc.1, hρi, hρc, φ.toIntertwiningMap.comp f, fun h0 => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨w, rfl⟩ := hf x
  have h1 : φ (f w) = 0 := congrArg (fun F => F w) h0
  exact hx ((map_eq_zero_iff φ φ.injective).1 h1)

end GlobalTheory.JacFactor
