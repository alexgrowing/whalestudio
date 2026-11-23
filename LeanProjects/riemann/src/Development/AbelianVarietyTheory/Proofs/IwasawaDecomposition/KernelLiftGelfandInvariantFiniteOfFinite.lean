import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDerivStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorAdjointDecayingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivativesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftFin

variable {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
  {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)}

theorem word_ker (hκ : IsKerSys θ V W κ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (f : M) : ∃ f', ∀ h, word θ V l (fun g => κ f g h) = fun g => κ f' g h := by
  induction l with
  | nil => exact ⟨f, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨f'', e'⟩ := hκ.derV p.1 p.2 (hl p List.mem_cons_self) f'
    refine ⟨f'', fun h => ?_⟩
    change Rder θ V p.1 p.2 (word θ V l fun g => κ f g h) = _
    rw [e h]
    funext g
    exact (e' g h).deriv

theorem isMod_ker (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (f : M) (h : GA D W) : IsMod θ V fun g => κ f g h := by
  have hc : ∀ f, Continuous fun g => κ f g h := fun f => (hκ.cont f).comp (Continuous.prodMk_left h)
  refine ⟨GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ V (Set.range fun f g => κ f g h) ?_ ?_ _ ⟨f, rfl⟩, fun γ hγ g => ?_, fun l hl => ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact hc f
  · rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hκ.derV τ X hX f
    exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
  · simpa using hκ.left f γ hγ 1 (one_mem _) g h
  · obtain ⟨f', e⟩ := word_ker hκ l hl f
    obtain ⟨N, hN⟩ := hκ.growth
    obtain ⟨C, hC⟩ := hN f'
    rw [e h]
    refine ⟨hc f', N, C * (height θ W h : ℝ) ^ N, fun g => (hC g h).trans_eq ?_⟩
    ring

variable (κ) in

def lift (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (f : M) (F : GA D V → ℂ) : GA D W → ℂ :=
  fun h => ∫ g in 𝓕, κ f g h * F g ∂μ

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem lift_add_left (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (f f' : M) : lift κ μ 𝓕 (f + f') F = lift κ μ 𝓕 f F + lift κ μ 𝓕 f' F := by
  have I := (GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1
  funext h
  simp only [lift, map_add, Pi.add_apply, add_mul]
  exact integral_add (I f h) (I f' h)

theorem lift_add_right (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F F' : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (hF' : F' ∈ Decay θ V) (f : M) :
    lift κ μ 𝓕 f (F + F') = lift κ μ 𝓕 f F + lift κ μ 𝓕 f F' := by
  funext h
  simp only [lift, Pi.add_apply, mul_add]
  exact integral_add ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1 f h)
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F' hF').1 f h)

theorem lift_smul_left (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 (c • f) F = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem lift_smul_right (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 f (c • F) = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

variable (θ κ μ 𝓕) in

def Compat (T : (GA D W → ℂ) → (GA D W → ℂ)) : Prop :=
  ∀ f, ∃ f', (∀ g, T (κ f g) = κ f' g) ∧ ∀ F ∈ Decay θ V, T (lift κ μ 𝓕 f F) = lift κ μ 𝓕 f' F

theorem compat_id : Compat θ κ μ 𝓕 fun φ => φ := fun f => ⟨f, fun _ => rfl, fun _ _ => rfl⟩

theorem Compat.comp {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S (T φ) := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  obtain ⟨f'', c, d⟩ := hS f'
  exact ⟨f'', fun g => by simp only [a, c], fun F hF => by simp only [b F hF, d F hF]⟩

theorem Compat.add (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕)
    {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S φ + T φ := fun f => by
  obtain ⟨f', a, b⟩ := hS f
  obtain ⟨f'', c, d⟩ := hT f
  exact ⟨f' + f'', fun g => by simp only [a, c, map_add, Pi.add_apply],
    fun F hF => by simp only [b F hF, d F hF, lift_add_left hθ hκ hq hF]⟩

theorem Compat.smul (c : ℂ) {T : (GA D W → ℂ) → (GA D W → ℂ)} (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => c • T φ := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  exact ⟨c • f', fun g => by simp only [a, map_smul, Pi.smul_apply], fun F hF => by simp only [b F hF, lift_smul_left]⟩

theorem compat_sum (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {ι : Type} (s : Finset ι)
    (T : ι → (GA D W → ℂ) → (GA D W → ℂ)) (hT : ∀ i, Compat θ κ μ 𝓕 (T i)) :
    Compat θ κ μ 𝓕 fun φ => ∑ i ∈ s, T i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (compat_id (θ := θ) (κ := κ) (μ := μ) (𝓕 := 𝓕)).smul 0
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hT i).add hθ hκ hq ih

theorem compat_foldr (l : List ((GA D W → ℂ) → (GA D W → ℂ))) (hl : ∀ T ∈ l, Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => l.foldr (fun T acc => T acc) φ := by
  induction l with
  | nil => exact compat_id
  | cons T l ih => exact (hl T List.mem_cons_self).comp (ih fun S hS => hl S (List.mem_cons_of_mem _ hS))

theorem compat_Rder (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hX : X ∈ lieAt W τ) : Compat θ κ μ 𝓕 (Rder θ W τ X) := fun f => by
  obtain ⟨f', e⟩ := hκ.derW τ X hX f
  exact ⟨f', fun g => funext fun h => (e g h).deriv, fun F hF => funext fun h =>
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).2.2.2 τ X hX f f' e h).deriv⟩

theorem compat_gelf (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) (τ : D.what₂.Tau) (k : ℕ) :
    Compat θ κ μ 𝓕 (gelf θ W τ k) := by
  refine compat_sum hθ hκ hq Finset.univ _ fun idx : Fin (k + 1) → Fin W.rank =>
    compat_foldr (List.ofFn fun a : Fin (k + 1) => RderC θ W τ (Matrix.single (idx a) (idx (a + 1)) 1)) fun T hT => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem W τ (Matrix.single (idx a) (idx (a + 1)) 1)
  exact (compat_Rder hθ hκ hq h1).add hθ hκ hq ((compat_Rder hθ hκ hq h2).smul Complex.I)

theorem lift_adjoin (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {a : ℕ → Module.End ℂ M} (ha : ∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h)
    {Z : Submodule ℂ (GA D V → ℂ)} (hZ : ∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) {x : Module.End ℂ M}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ f, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, lift κ μ 𝓕 (x f) F = lift κ μ 𝓕 f F' := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro f F hF
    obtain ⟨F', hF', e⟩ := GlobalTheory.T.gelfand_operator_adjoint_decaying D θ hθ V μ 𝓕 hq τ Z hZ k F hF
    refine ⟨F', hF', funext fun h => ?_⟩
    have := e _ (isMod_ker hθ hκ f h)
    rw [ha] at this
    exact this
  | algebraMap r =>
    intro f F hF
    exact ⟨r • F, Submodule.smul_mem _ r hF, by rw [Module.algebraMap_end_apply, lift_smul_left, lift_smul_right]⟩
  | add x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx f F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F hF
    exact ⟨F₁ + F₂, add_mem h₁ h₂, by
      rw [LinearMap.add_apply, lift_add_left hθ hκ hq hF.1, lift_add_right hθ hκ hq h₁.1 h₂.1, e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx (y f) F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F₁ h₁
    exact ⟨F₂, h₂, by rw [Module.End.mul_apply, e₁, e₂]⟩

theorem lift_zfin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  rintro D θ hθ V W M _ _ κ hκ μ 𝓕 hq F hF ⟨Z, hfin, hFZ, hZ⟩ f
  let L : ↥(Decay θ V ⊓ Z) →ₗ[ℂ] (GA D W → ℂ) :=
    { toFun := fun F' => lift κ μ 𝓕 f F'.1
      map_add' := fun F₁ F₂ => lift_add_right hθ hκ hq F₁.2.1 F₂.2.1 f
      map_smul' := fun c F' => lift_smul_right c F'.1 f }
  refine ⟨LinearMap.range L, inferInstance, ⟨⟨F, hF, hFZ⟩, rfl⟩, ?_⟩
  rintro τ k _ ⟨F₁, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hκ.cap τ
  obtain ⟨f', e, e'⟩ := compat_gelf hθ hκ hq τ k f
  obtain ⟨F₂, h₂, e₂⟩ := lift_adjoin hθ hκ hq ha (hZ τ) (hab ▸ Algebra.subset_adjoin ⟨k, rfl⟩ : b k ∈ _) f F₁.1 F₁.2
  refine ⟨⟨F₂, h₂⟩, ?_⟩
  change lift κ μ 𝓕 f F₂ = gelf θ W τ k (lift κ μ 𝓕 f F₁.1)
  rw [e' _ F₁.2.1, ← e₂]
  funext h
  simp only [lift, ← e, hb]

end GlobalTheory.Mem.LiftFin

end
