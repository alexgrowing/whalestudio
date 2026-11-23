import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.SelfInjective

namespace GlobalTheory.WtDual

section alg

open NumberField ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem exists_finite_place : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 L⁺)) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField L⁺)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  exact ⟨⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩⟩

theorem nontrivial_finiteAdeles : Nontrivial (AFplus L) := by
  obtain ⟨v⟩ := exists_finite_place L
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (evalAt L v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem nontrivial_adeles : Nontrivial (AL L) := by
  haveI := nontrivial_finiteAdeles L
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
    (algebraMap (L⁺) (AFplus L)).injective

theorem includeLeft_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
  haveI := nontrivial_adeles L
  exact (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L).injective

variable {L n}

theorem mem_rationalUnitaryGroup_of_matrix_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) : γ₀ ∈ GQ0 L n := by
  have hγ : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := γ.2
  obtain ⟨γ₁, h₁, he⟩ := hγ
  have hmat : (γ₀ : Matrix (Fin n) (Fin n) L) = (γ₁ : Matrix (Fin n) (Fin n) L) := by
    ext i j
    apply includeLeft_injective L
    have e1 := congrFun (congrFun hm i) j
    have e2 := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) he
    simp only [Matrix.map_apply] at e1 e2
    rw [← e1, ← e2]
    rfl
  rw [show γ₀ = γ₁ from Units.ext hmat]
  exact h₁

theorem match_inv (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    ((((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  have hm : ((γ : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ :=
    Units.ext h
  have : (((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀⁻¹ := by
    rw [map_inv, ← hm]
    rfl
  rw [this]
  rfl

theorem inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

theorem isAlgWeight_dual (a : Formalism.L2.NG.AlgWt L n) : IsAlgWeight L n a.ρ.dual := by
  obtain ⟨hfd, ι, _, _, b, P, hP⟩ := a.alg
  refine ⟨inferInstance, ι, inferInstance, inferInstance, b.dualBasis,
    fun i j => MvPolynomial.rename
      (fun p : (L →+* ℂ) × Fin n × Fin n => (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i), ?_⟩
  intro γ γ₀ h
  have hinv := hP γ⁻¹ γ₀⁻¹ (match_inv γ γ₀ h)
  have hγ := mem_rationalUnitaryGroup_of_matrix_match γ γ₀ h
  have e : LinearMap.toMatrix b.dualBasis b.dualBasis (a.ρ.dual γ) =
      Matrix.transpose (LinearMap.toMatrix b b (a.ρ γ⁻¹)) := by
    rw [Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, hinv]
  ext i j
  change MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n =>
      p.1 (((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P j i) =
    MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
      (MvPolynomial.rename (fun p : (L →+* ℂ) × Fin n × Fin n =>
        (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i))
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (P j i)) (funext fun p => ?_)
  simp only [Function.comp_apply]
  rw [inv_entry γ₀ hγ, ComplexEmbedding.conjugate_coe_eq]
  exact IsCMField.complexEmbedding_complexConj L p.1 _

end alg

end GlobalTheory.WtDual

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.WtDual

theorem dual_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) : ρ.dual.IsIrreducible := by
  have hnt : Nontrivial V := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    obtain ⟨S, T, hST⟩ := (hρ : IsSimpleOrder _).toNontrivial.exists_pair_ne
    exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hntD : Nontrivial (Module.Dual ℂ V) := inferInstance
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℂ (Module.Dual ℂ V)) ≠ ⊤) h1
  · let C : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.dualCoannihilator
        apply_mem_toSubmodule := fun g v hv => by
          rw [Submodule.mem_dualCoannihilator] at hv ⊢
          intro φ hφ
          have h2 := hv _ (U.apply_mem_toSubmodule g⁻¹ hφ)
          simp [Representation.dual_apply] at h2
          exact h2 }
    rcases hρ.eq_bot_or_eq_top C with hC | hC
    · right
      apply Subrepresentation.toSubmodule_injective
      have hC' : U.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule hC
      show U.toSubmodule = ⊤
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U.toSubmodule), hC', Submodule.dualAnnihilator_bot]
    · left
      apply Subrepresentation.toSubmodule_injective
      have hC' : U.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule hC
      show U.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro φ hφ
      rw [Submodule.mem_bot]
      ext v
      have hv : v ∈ U.toSubmodule.dualCoannihilator := by rw [hC']; exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator _).1 hv φ hφ

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def dualWt (a : NG.AlgWt L n) : NG.AlgWt L n where
  W := Module.Dual ℂ a.W
  ρ := a.ρ.dual
  alg := isAlgWeight_dual a
  irr := by
    haveI := a.alg.1
    exact dual_isIrreducible a.ρ a.irr

theorem isDual_dualWt (a : NG.AlgWt L n) : a.IsDual (dualWt a) := by
  refine ⟨Module.Dual.eval ℂ a.W, ?_, ?_⟩
  · intro h0
    have hnt : Nontrivial a.W := by
      by_contra hs
      rw [not_nontrivial_iff_subsingleton] at hs
      obtain ⟨S, T, hST⟩ := (a.irr : IsSimpleOrder _).toNontrivial.exists_pair_ne
      exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ a.W, f x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).mp hc)
    have h1 := LinearMap.congr_fun (LinearMap.congr_fun h0 x) f
    simp only [Module.Dual.eval_apply, LinearMap.zero_apply] at h1
    exact hf h1
  · intro γ x (y : Module.Dual ℂ a.W)
    show y (a.ρ γ⁻¹ (a.ρ γ x)) = y x
    rw [Representation.inv_self_apply]

theorem isDual_iff_iso (a b b' : NG.AlgWt L n) (hab : a.IsDual b) : a.IsDual b' ↔ b.Iso b' := by
  haveI := a.alg.1; haveI := b.alg.1; haveI := b'.alg.1
  haveI := a.irr; haveI := b.irr; haveI := b'.irr
  constructor
  · rintro ⟨C, hC0, hC⟩
    obtain ⟨B, hB0, hB⟩ := hab
    exact PI.UnitaryGroupMassFormula.AlgWtDualUniq.dual_unique (ρa := a.ρ) B hB hB0 C hC hC0
  · rintro ⟨T, hT⟩
    obtain ⟨B, hB0, hB⟩ := hab
    refine ⟨B.compl₂ T.symm.toLinearMap, fun h => hB0 ?_, fun γ x y => ?_⟩
    · ext x y
      have := LinearMap.congr_fun (LinearMap.congr_fun h x) (T y)
      simpa using this
    · have e : T.symm (b'.ρ γ y) = b.ρ γ (T.symm y) := by
        apply T.injective
        rw [hT]
        simp
      simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
      rw [e, hB]

theorem isDual_of_iso {a a' b : NG.AlgWt L n} (h : a.Iso a') (hab : a.IsDual b) : a'.IsDual b := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨B, hB0, hB⟩ := hab
  refine ⟨B.comp T.symm.toLinearMap, fun h => hB0 ?_, fun γ x y => ?_⟩
  · ext x y
    have := LinearMap.congr_fun (LinearMap.congr_fun h (T x)) y
    simpa using this
  · have e : T.symm (a'.ρ γ x) = a.ρ γ (T.symm x) := by
      apply T.injective
      rw [hT]
      simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e, hB]

theorem hwAt_of_iso {a a' : NG.AlgWt L n} (h : a.Iso a') {τ : L →+* ℂ} {lam : Fin n → ℤ} (hw : a.HWAt τ lam) :
    a'.HWAt τ lam := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨ι, hfin, hdec, b, P, hP, v, hv0, hv⟩ := hw
  refine ⟨ι, hfin, hdec, b.map T, P, fun γ γ₀ hm => ?_, v, hv0, hv⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.trans_apply, ← hT, LinearEquiv.symm_apply_apply]

end GlobalTheory.WtDual

theorem GlobalTheory.algWt_contragredient : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ b : NG.AlgWt L n, a.IsDual b ∧ (∀ b', a.IsDual b' ↔ b.Iso b') ∧
      ∀ a' : NG.AlgWt L n, a.Iso a' → a'.IsDual b ∧ ∀ τ lam, a.HWAt τ lam → a'.HWAt τ lam := by
  intro L _ _ _ n a
  have hd := GlobalTheory.WtDual.isDual_dualWt a
  exact ⟨GlobalTheory.WtDual.dualWt a, hd, fun b' => GlobalTheory.WtDual.isDual_iff_iso a _ b' hd,
    fun a' h => ⟨GlobalTheory.WtDual.isDual_of_iso h hd, fun τ lam hw => GlobalTheory.WtDual.hwAt_of_iso h hw⟩⟩
