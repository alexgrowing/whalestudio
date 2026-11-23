import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundaryVanishingPullback
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminedOnOpenStratum

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

def onRight (V : Type) [AddCommGroup V] [Module ℂ V] {G : Type} [Group G] (σ : Representation ℂ G W) :
    Representation ℂ G (V ⊗[ℂ] W) where
  toFun g := (σ g).lTensor V
  map_one' := by simp only [map_one]; exact LinearMap.lTensor_id _ _
  map_mul' g h := by simp only [map_mul]; exact LinearMap.lTensor_comp _ _ _

theorem isSmooth_onRight {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) : IsSmooth (onRight V σ) := by
  intro x
  show x ∈ smoothPart (onRight V σ)
  induction x with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hσ w).mem_nhds (by simp)) fun g hg => ?_)
    have h2 : σ g w = w := hg
    show (σ g).lTensor V (v ⊗ₜ w) = _
    rw [LinearMap.lTensor_tmul, h2]

def tmulMap {G : Type} [Group G] (σ : Representation ℂ G W) (v : V) : σ.IntertwiningMap (onRight V σ) where
  toLinearMap := TensorProduct.mk ℂ V W v
  isIntertwining' _ := rfl

def tensorInd (σ : Representation ℂ P W) :
    V ⊗[ℂ] smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P (onRight V σ)) :=
  TensorProduct.lift
    { toFun := fun v => (smIndMap (tmulMap σ v)).toLinearMap
      map_add' := fun v v' => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x =>
        TensorProduct.add_tmul v v' (f.1.1 x)))
      map_smul' := fun c v => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x =>
        (TensorProduct.smul_tmul' c v (f.1.1 x)).symm)) }

theorem tensorInd_apply (σ : Representation ℂ P W) (t : V ⊗[ℂ] smoothPart (ind P σ)) (x : H) :
    (tensorInd σ t).1.1 x = (MultiIrr.ev σ x).lTensor V t := by
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, ← hs, ← ht]; rfl
  | tmul v f => rfl

theorem tensorInd_bijective (σ : Representation ℂ P W) {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P, ∃ w ∈ K, x = p * w) : Function.Bijective (tensorInd (V := V) σ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => MultiIrr.eq_zero_of_ev σ t fun x => ?_, fun f => ?_⟩
  · rw [← tensorInd_apply, ht]; rfl
  · obtain ⟨t, ht⟩ := MultiIrr.exists_tensor σ hK hPK f.1.1 f.1.2 (MultiIrr.eventually_of_smooth f)
    exact ⟨t, Subtype.ext (Subtype.ext (funext fun x => (tensorInd_apply σ t x).trans (ht x)))⟩

theorem exists_factor (f : V →ₗ[ℂ] W) (g : V →ₗ[ℂ] U) (hf : Function.Surjective f)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ T : W →ₗ[ℂ] U, ∀ v, T (f v) = g v := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  refine ⟨g ∘ₗ s, fun v => ?_⟩
  have : s (f v) - v ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hs (f v)
  have := h this
  rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this

def contract (L : Submodule ℂ (Module.Dual ℂ V)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] :
    V →ₗ[ℂ] L ⊗[ℂ] Y →ₗ[ℂ] Y :=
  ((dualTensorHom ℂ V Y) ∘ₗ L.subtype.rTensor Y).flip

theorem exists_lift [T2Space H] {K : Subgroup H} (hP : IsClosed (P : Set H)) (hK : IsCompact (K : Set H))
    (hPK : ∀ g : H, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : H), ∃ J : Subgroup H, IsOpen (J : Set H) ∧ (J : Set H) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    {σ : Representation ℂ P W} (hσ : IsSmooth σ) {ρ : Representation ℂ P U}
    (R : Γ → V →ₗ[ℂ] V) (S : Γ → σ.IntertwiningMap σ) (A : V →ₗ[ℂ] σ.IntertwiningMap ρ)
    (hs : ∀ u, ∃ v w, A v w = u)
    (hu : ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : W →ₗ[ℂ] V →ₗ[ℂ] Z),
      (∀ γ w v, B (S γ w) (R γ v) = B w v) → ∃ B₀ : U →ₗ[ℂ] Z, ∀ w v, B w v = B₀ (A v w))
    {π' : Representation ℂ H Y} (B : V →ₗ[ℂ] (smInd P σ).IntertwiningMap π')
    (hB : ∀ γ v f, B (R γ v) (smIndMap (S γ) f) = B v f) :
    ∃ T : (smInd P ρ).IntertwiningMap π', ∀ v f, T (smIndMap (A v) f) = B v f := by
  let α : (onRight V σ).IntertwiningMap ρ :=
    { toLinearMap := TensorProduct.lift
        { toFun := fun v => (A v).toLinearMap
          map_add' := fun v v' => by rw [map_add]; rfl
          map_smul' := fun c v => by rw [map_smul]; rfl }
      isIntertwining' := fun p => TensorProduct.ext' fun v w => (A v).isIntertwining _ _ p w }
  have hα : ∀ v w, α (v ⊗ₜ w) = A v w := fun _ _ => rfl
  let T : Γ → (onRight V σ).IntertwiningMap (onRight V σ) := fun γ =>
    { toLinearMap := TensorProduct.map (R γ) (S γ).toLinearMap
      isIntertwining' := fun p => TensorProduct.ext' fun v w =>
        congrArg (fun z => R γ v ⊗ₜ[ℂ] z) ((S γ).isIntertwining _ _ p w) }
  obtain ⟨h1, h2⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants H P K hP hK hPK hb _ U (onRight V σ) ρ (isSmooth_onRight hσ) α Γ T
    (fun u => by obtain ⟨v, w, rfl⟩ := hs u; exact ⟨v ⊗ₜ w, rfl⟩) (fun x hx => by
      set N := Submodule.span ℂ {y : V ⊗[ℂ] W | ∃ γ z, y = T γ z - z}
      obtain ⟨B₀, hB₀⟩ := hu _ ((TensorProduct.mk ℂ V W).flip.compr₂ N.mkQ) fun γ w v =>
        (Submodule.Quotient.eq N).2 (Submodule.subset_span ⟨γ, v ⊗ₜ w, rfl⟩)
      have : N.mkQ = B₀ ∘ₗ α.toLinearMap := TensorProduct.ext' fun v w => hB₀ w v
      have h0 : N.mkQ x = 0 := by
        rw [this]
        show B₀ (α x) = 0
        rw [hx, map_zero]
      exact (Submodule.Quotient.mk_eq_zero N).1 h0)
  let E := LinearEquiv.ofBijective _ (tensorInd_bijective (V := V) σ hK fun x => by
    obtain ⟨p, hp, w, hw, e⟩ := hPK x
    exact ⟨⟨p, hp⟩, w, hw, e⟩)
  let β : V ⊗[ℂ] smoothPart (ind P σ) →ₗ[ℂ] Y := TensorProduct.lift
    { toFun := fun v => (B v).toLinearMap
      map_add' := fun v v' => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [map_smul]; rfl }
  have hker : LinearMap.ker (smIndMap α).toLinearMap ≤ LinearMap.ker (β ∘ₗ E.symm.toLinearMap) := by
    intro f hf
    refine Submodule.span_le.2 ?_ (h2 f hf)
    rintro _ ⟨γ, z, rfl⟩
    obtain ⟨t, rfl⟩ := E.surjective z
    have e1 : smIndMap (T γ) (E t) = E (TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap t) := by
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul v f => rfl
    have e2 : β (TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap t) = β t :=
      LinearMap.congr_fun (f := β ∘ₗ TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap) (g := β)
        (TensorProduct.ext' fun v f => hB γ v f) t
    show β (E.symm _) = 0
    rw [e1, map_sub, E.symm_apply_apply, E.symm_apply_apply, map_sub, e2, sub_self]
  obtain ⟨T₀, hT₁⟩ := exists_factor _ _ h1 hker
  have hT₀ : ∀ t, T₀ (smIndMap α (E t)) = β t := fun t =>
    (hT₁ (E t)).trans (congrArg β (E.symm_apply_apply t))
  have hT : ∀ v f, T₀ (smIndMap (A v) f) = B v f := fun v f => hT₀ (v ⊗ₜ f)
  refine ⟨⟨T₀, fun h => LinearMap.ext fun u => ?_⟩, hT⟩
  obtain ⟨z, rfl⟩ := h1 u
  obtain ⟨t, rfl⟩ := E.surjective z
  show T₀ (smInd P ρ h _) = π' h (T₀ _)
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul v f => exact (hT v (smInd P σ h f)).trans (((B v).isIntertwining _ _ h f).trans (congrArg _ (hT v f).symm))

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

def act (hπ : IsSmooth π) : V →ₗ[ℂ] SB G →ₗ[ℂ] V :=
  LinearMap.flip
    { toFun := fun φ => smoothOp π ν φ.1
      map_add' := fun φ ψ => hπ.smoothOp_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2
      map_smul' := fun c φ => hπ.smoothOp_smul φ.2.1 φ.2.2 c }

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def contraMap [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap := (f.toLinearMap.dualMap ∘ₗ Submodule.subtype _).codRestrict _ fun l =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds l.2 (by
      rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply])) fun g hg =>
      LinearMap.ext fun v => by
        have h1 : l.1 (σ g⁻¹ (f v)) = l.1 (f v) := LinearMap.congr_fun hg (f v)
        show l.1 (f (π g⁻¹ v)) = l.1 (f v)
        rw [f.isIntertwining, h1])
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem isUnitarisable_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsUnitarisable σ) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _, fun v hv => h2 _ ?_, fun g v w => ?_⟩
  · exact fun h => hv (E.toLinearEquiv.map_eq_zero_iff.1 h)
  · show B (E.toIntertwiningMap (π g v)) (E.toIntertwiningMap (π g w)) = _
    rw [E.toIntertwiningMap.isIntertwining, E.toIntertwiningMap.isIntertwining, h3]
    rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_twist {π : Representation ℂ G V} (h : π.IsIrreducible) (χ : G →* ℂˣ) :
    (twist π χ).IsIrreducible := by
  let φ : Subrepresentation (twist π χ) ≃o Subrepresentation π :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem ((χ g)⁻¹ : ℂˣ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact φ.isSimpleOrder_iff.2 h

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invTranspose_invTranspose {n : ℕ} (g : GL (Fin n) k) :
    WeilTensorLiftConclusion.invTranspose n k (WeilTensorLiftConclusion.invTranspose n k g) = g := Units.ext (transpose_transpose _)

end Final

end GlobalTheory.LocalThetaGL
