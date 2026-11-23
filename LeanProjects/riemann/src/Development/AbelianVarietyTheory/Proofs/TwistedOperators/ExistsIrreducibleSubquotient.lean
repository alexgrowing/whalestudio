import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundaryVanishingPullback
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IrreducibleTensorCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem exists_irreducible_subquotient [Nontrivial V] (ρ : Representation ℂ G V) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      τ.IsIrreducible ∧ IsSubquotient τ ρ := by
  let φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  haveI : Nontrivial ρ.asModule := inferInstanceAs (Nontrivial V)
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  have hc := CompleteLattice.Iic_coatomic_of_compact_element
    (Submodule.singleton_span_isCompactElement (R := MonoidAlgebra ℂ G) v)
  rcases hc.eq_top_or_exists_le_coatom ⊥ with h | ⟨T, hT, -⟩
  · have h1 : (⊥ : Submodule (MonoidAlgebra ℂ G) ρ.asModule) = Submodule.span _ {v} :=
      congrArg Subtype.val h
    exact absurd (Submodule.span_singleton_eq_bot.1 h1.symm) hv
  · have h1 : T.1 ⋖ Submodule.span _ {v} := (covBy_iff_coatom_Iic T.2).2 hT
    have h2 : φ.symm T.1 ⋖ φ.symm (Submodule.span _ {v}) := (apply_covBy_apply_iff φ.symm).2 h1
    exact ⟨_, _, _, _, isIrreducible_subQuot h2, _,
      ⟨Submodule.mkQ _, fun g => LinearMap.ext fun x => rfl⟩, Submodule.mkQ_surjective _⟩

def transpose [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (hπ : IsSmooth π) (f : ρ.IntertwiningMap (contra π)) :
    π.IntertwiningMap (contra ρ) :=
  have key : ∀ g w, ((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip (π g w) =
      ρ.dual g (((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip w) := fun g w =>
    LinearMap.ext fun v => by
      show (f v).1 (π g w) = (f (ρ g⁻¹ v)).1 w
      rw [f.isIntertwining, contra_apply, inv_inv]
  { toLinearMap := (((smoothPart π.dual).subtype ∘ₗ f.toLinearMap).flip).codRestrict _ fun w =>
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) fun g hg => by
        have hg' : π g w = w := hg
        rw [Set.mem_ofPred_eq, ← key, hg'])
    isIntertwining' := fun g => LinearMap.ext fun w => Subtype.ext (key g w) }

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_jac_map {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) {π : Representation ℂ (GL n k) V}
    (hπ : IsSmooth π) (f : (parInd e ρ).IntertwiningMap (contra π)) (hf : f.toLinearMap ≠ 0) :
    ∃ φ : (jac e π).IntertwiningMap (contra ρ), φ.toLinearMap ≠ 0 := by
  obtain ⟨Φ⟩ := (IndDual.inductionContragredient k).nonempty_equiv e hρ
  let g := Φ.symm.toIntertwiningMap.comp (transpose hπ f)
  refine ⟨Model.evalOne e g, fun h => hf (LinearMap.ext fun x => Subtype.ext (LinearMap.ext fun v => ?_))⟩
  have h1 : g v = 0 := Subtype.ext (Subtype.ext (funext fun y => by
    have h2 : (g (π y v)).1.1 1 = 0 := LinearMap.congr_fun h (Submodule.Quotient.mk (π y v))
    rwa [g.isIntertwining, parInd_apply, one_mul] at h2))
  have h2 : transpose hπ f v = 0 := (map_eq_zero_iff Φ.symm Φ.symm.injective).1 h1
  exact LinearMap.congr_fun (congrArg Subtype.val h2) x

theorem exists_jac₂_map {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (e' : b ⊕ a ≃ n) {R : Representation ℂ (GL a k) W}
    (hR : IsSmooth R) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {π : Representation ℂ (GL n k) V}
    (hπ : IsSmooth π) (f : (ind₂Lower e (extTensor R (detRep b χ))).IntertwiningMap (contra π))
    (hf : f.toLinearMap ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (Levi k (Two b a)) Y)
      (φ : (jac (two e') π).IntertwiningMap σ), φ.toLinearMap ≠ 0 ∧
        ∀ g : Levi k (Two b a), g true = 1 → ∀ y, σ g y = (detChar b χ⁻¹ (g false) : ℂ) • y := by
  obtain ⟨Φ⟩ := (SwapBlocks.lower_equiv_upper_swap k a b n e _).1 (extTensor R (detRep b χ))
  let ρ : Representation ℂ (Levi k (Two b a)) (W ⊗[ℂ] ℂ) := ((extTensor R (detRep b χ)).comp
    (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom).comp
      (leviTwo k b a).symm.toMonoidHom
  obtain ⟨Ψ⟩ := (Placing.parInd_jac_placing k _ n _ (two e') (two ((Equiv.sumComm b a).trans e)) _).1 ρ
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_comp
    (isSmooth_extTensor hR ((isSmooth_ofChar_iff _).2 hχ.detChar)) _ continuous_swap) _
      ((continuous_apply false).prodMk (continuous_apply true))
  obtain ⟨φ, hφ⟩ := exists_jac_map (two e') hρ hπ (f.comp (Ψ.trans Φ.symm).toIntertwiningMap) fun h =>
    hf (LinearMap.ext fun x => by
      obtain ⟨y, rfl⟩ := (Ψ.trans Φ.symm).surjective x
      exact LinearMap.congr_fun h y)
  refine ⟨_, _, _, _, φ, hφ, fun g hg l => Subtype.ext (LinearMap.ext fun w => ?_)⟩
  have key : ρ g⁻¹ w = (detChar b χ⁻¹ (g false) : ℂ) • w := by
    show extTensor R (detRep b χ) ((g true)⁻¹, (g false)⁻¹) w = _
    rw [hg]
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul x y =>
      rw [extTensor_tmul, ← TensorProduct.tmul_smul]
      simp [detRep]
  rw [contra_apply, key, map_smul]
  rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem hasCentralChar_detRep (β : ℕ) (χ : kˣ →* ℂˣ) : HasCentralChar (detRep (Fin β) χ) (χ ^ β) :=
  fun z v => by
    have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin β) z) = z ^ β := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    simp [detRep, this]

end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod, ← MultilinearMap.map_smul_univ]
    simp only [h]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne k e _ hab]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h2 := parInd_law e _ f ⟨_, leviEmb_mem_parab k e fun a => GeneralLinearGroup.scalar (m a) z⟩ x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
