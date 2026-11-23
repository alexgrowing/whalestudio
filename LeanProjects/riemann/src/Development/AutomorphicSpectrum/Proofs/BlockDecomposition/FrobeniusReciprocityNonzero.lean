import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FrobInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mk_parab (e : (Σ a, m a) ≃ n) (τ : Representation ℂ (GL n k) V) (p : parab k e) (w : V) :
    (Submodule.Quotient.mk (τ (p : GL n k) w) : Jacquet τ (unipRad k e)) =
      Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) w) := by
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
  have key : ∀ y : V, (Submodule.Quotient.mk (τ u y) : Jacquet τ (unipRad k e)) = Submodule.Quotient.mk y := by
    intro y
    rw [Submodule.Quotient.eq]
    apply Submodule.subset_span
    refine Set.mem_ofPred.mpr ⟨⟨u, hu⟩, y, ?_⟩
    simp
  have hL : ∀ y : V, (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) y) : Jacquet τ (unipRad k e)) =
      ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • jac e τ (leviProj k e p) (Submodule.Quotient.mk y) := by
    intro y
    rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
  have e1 : τ (p : GL n k) w = τ (leviEmb k e (leviProj k e p)) (τ u w) := by
    first
    | (rw [hp, map_mul]; rfl)
    | rw [hp, map_mul]
  rw [e1, hL, hL, key]

def frobFun (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) : GL n k → W :=
  fun g => f (Submodule.Quotient.mk (τ g v))

theorem frobFun_law (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (p : parab k e) (g : GL n k) :
    frobFun e f v (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (frobFun e f v g) := by
  have h1 : frobFun e f v (p * g) =
      f (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) := by
    show f (Submodule.Quotient.mk (τ ((p : GL n k) * g) v)) = _
    rw [map_mul]
    exact congrArg f (mk_parab e τ p (τ g v))
  have h2 := LinearMap.congr_fun (f.isIntertwining' (leviProj k e p)) (Submodule.Quotient.mk (τ g v))
  simp only [LinearMap.comp_apply] at h2
  rw [h1]
  show f.toLinearMap (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) =
    ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • ρ (leviProj k e p) (f.toLinearMap (Submodule.Quotient.mk (τ g v)))
  rw [← h2, jac_mk, map_smul, smul_smul, Units.mul_inv, one_smul]

theorem frobFun_mem (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    frobFun e f v ∈ indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) := by
  show ∀ (h : ↥(parab k e)) (g : GL n k),
    frobFun e f v (↑h * g) = ((twist ρ (deltaHalf k m)).comp (leviProj k e)) h (frobFun e f v g)
  intro p x
  rw [frobFun_law, MonoidHom.comp_apply, twist_apply]

theorem frobFun_translate (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (h x : GL n k) :
    frobFun e f v (x * h) = frobFun e f (τ h v) x := by
  show f (Submodule.Quotient.mk (τ (x * h) v)) = f (Submodule.Quotient.mk (τ x (τ h v)))
  first
  | (rw [map_mul]; rfl)
  | rw [map_mul]

theorem frobFun_smooth (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (⟨frobFun e f v, frobFun_mem e f v⟩ : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) ∈
      smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) := by
  show IsOpen {g : GL n k | (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) g
    ⟨frobFun e f v, frobFun_mem e f v⟩ = ⟨frobFun e f v, frobFun_mem e f v⟩}
  set F : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) :=
    ⟨frobFun e f v, frobFun_mem e f v⟩ with hF
  set R := ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) with hR
  have hstab : ∀ s, τ s v = v → R s F = F := by
    intro s hs
    apply Subtype.ext
    funext x
    show frobFun e f v (x * s) = frobFun e f v x
    rw [frobFun_translate, hs]
  rw [isOpen_iff_forall_mem_open]
  intro g0 hg0
  refine ⟨(fun g => g0⁻¹ * g) ⁻¹' {g | τ g v = v}, ?_, IsOpen.preimage (continuous_const_mul g0⁻¹) (hτ v), ?_⟩
  · intro g hg
    have h1 : R (g0 * (g0⁻¹ * g)) F = R g0 (R (g0⁻¹ * g) F) := by
      first
      | (rw [map_mul]; rfl)
      | rw [map_mul]
    rw [mul_inv_cancel_left] at h1
    show R g F = F
    rw [h1, hstab _ hg]
    exact hg0
  · show τ (g0⁻¹ * g0) v = v
    rw [inv_mul_cancel, map_one]
    rfl

def frobInv (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (parInd e ρ) where
  toLinearMap :=
    { toFun := fun v => ⟨⟨frobFun e f v, frobFun_mem e f v⟩, frobFun_smooth e hτ f v⟩
      map_add' := fun v w => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (v + w))) = f (Submodule.Quotient.mk (τ g v)) + f (Submodule.Quotient.mk (τ g w))
        rw [map_add, Submodule.Quotient.mk_add, map_add]
      map_smul' := fun c v => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (c • v))) = c • f (Submodule.Quotient.mk (τ g v))
        rw [map_smul, Submodule.Quotient.mk_smul, map_smul] }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (frobFun_translate e f v g x).symm

theorem frobInv_one (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (frobInv e hτ f v).1.1 1 = f (Submodule.Quotient.mk v) := by
  show f (Submodule.Quotient.mk (τ 1 v)) = f (Submodule.Quotient.mk v)
  first
  | (rw [map_one]; rfl)
  | rw [map_one]

theorem exists_frobInv_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (hf : ∃ v, f v ≠ 0) :
    ∃ v, frobInv e hτ f v ≠ 0 := by
  obtain ⟨w, hw⟩ := hf
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨v, fun h => hw ?_⟩
  have h1 := frobInv_one e hτ f v
  rw [h] at h1
  exact h1.symm

theorem exists_map_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ)
    (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep))
    (hf : ∃ v, f v ≠ 0) : ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  exact ⟨frobInv (stdBlocks (fun a => (x a).1) hd) hτ f, exists_frobInv_ne_zero _ hτ f hf⟩

end GlobalTheory.CompanionTheory.FrobInv

end
