import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem foldr_rderC_zero (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (τ : D.what₂.Tau) :
    (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons Z l ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    exact rderC_zero θ V τ Z

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) where
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}

theorem isMultMap_zero (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : IsMultMap θ M J χ 0 where
  aut v := by
    show IsAutFunSm θ V (fun _ => 0)
    exact isAutFunSm_zero θ V
  cusp v := by
    show IsCuspFun V (fun _ => 0)
    exact isCuspFun_zero V
  lev v k _ g := by simp
  equiv τ g _ v w _ := by
    funext x
    simp [rTr]
  cont τ v x := by
    refine ⟨0, ⟨[], 0, by simp, fun w _ => by simp⟩, fun w => by simp⟩

variable (V) in

theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _

variable (V) in

theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) where
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (V) in

theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]

theorem isMultMap_smul {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : IsMultMap θ M J χ T) (c : ℂ) : IsMultMap θ M J χ (c • T) where
  aut v := by
    show IsAutFunSm θ V (c • T v)
    exact isAutFunSm_smul θ V (hT.aut v) c
  cusp v := by
    show IsCuspFun V (c • T v)
    exact isCuspFun_smul V (hT.cusp v) c
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    rw [_root_.smul_apply, _root_.smul_apply, hT.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, ⟨L, C, hL, hC⟩, hℓ⟩ := hT.cont τ v x
    refine ⟨c • ℓ, ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩, fun w => ?_⟩
    · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, _root_.smul_apply, Pi.smul_apply, hℓ w]

theorem heckeLin_indep {D : D7} {V : HSp D} (K : Set (GA D V)) (x : GA D V) (R R' : Finset (GA D V))
    (F : GA D V → ℂ)
    (hinv : ∀ a ∈ K, a⁻¹ ∈ K)
    (hK : ∀ k ∈ K, ∀ g, F (g * k) = F g) (hR : IsCosetRep V K x R) (hR' : IsCosetRep V K x R') :
    heckeLin V R F = heckeLin V R' F := by
  funext g
  show ∑ γ ∈ R, F (g * γ) = ∑ γ ∈ R', F (g * γ)
  have ex1 : ∀ γ ∈ R, ∃ γ', γ' ∈ R' ∧ γ'⁻¹ * γ ∈ K := fun γ hγ => (hR'.2 γ (hR.1 γ hγ).2).exists
  have ex2 : ∀ γ ∈ R', ∃ γ', γ' ∈ R ∧ γ'⁻¹ * γ ∈ K := fun γ hγ => (hR.2 γ (hR'.1 γ hγ).2).exists
  choose! i hiR hiK using ex1
  choose! j hjR hjK using ex2
  refine Finset.sum_nbij' i j hiR hjR ?_ ?_ ?_
  · intro γ hγ
    have hk := hinv _ (hiK γ hγ)
    rw [_root_.mul_inv_rev, _root_.inv_inv] at hk
    exact (hR.2 (i γ) (hR'.1 (i γ) (hiR γ hγ)).2).unique
      ⟨hjR (i γ) (hiR γ hγ), hjK (i γ) (hiR γ hγ)⟩ ⟨hγ, hk⟩
  · intro γ hγ
    have hk := hinv _ (hjK γ hγ)
    rw [_root_.mul_inv_rev, _root_.inv_inv] at hk
    exact (hR'.2 (j γ) (hR.1 (j γ) (hjR γ hγ)).2).unique
      ⟨hiR (j γ) (hjR γ hγ), hiK (j γ) (hjR γ hγ)⟩ ⟨hγ, hk⟩
  · intro γ hγ
    show F (g * γ) = F (g * i γ)
    rw [← hK _ (hiK γ hγ) (g * i γ), _root_.mul_assoc, _root_.mul_inv_cancel_left]

theorem heckeOn_indep {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Set (GA D V))
    (x : GA D V) (R R' : Finset (GA D V)) (T : MMap M)
    (hinv : ∀ a ∈ K, a⁻¹ ∈ K)
    (hT : ∀ v, ∀ k ∈ K, ∀ g, T v (g * k) = T v g) (hR : IsCosetRep V K x R) (hR' : IsCosetRep V K x R') :
    heckeOn M R T = heckeOn M R' T := by
  ext v g
  exact congrFun (heckeLin_indep K x R R' (T v) hinv (hT v) hR hR') g

end Formalism.IndefR.Mult

end
