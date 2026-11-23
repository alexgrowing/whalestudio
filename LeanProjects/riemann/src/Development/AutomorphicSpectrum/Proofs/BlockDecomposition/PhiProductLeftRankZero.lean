import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.GLZero

section general
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def trT (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] : Representation ℂ G (V ⊗[ℂ] W) where
  toFun g := LinearMap.rTensor W (ρ g)
  map_one' := by
    rw [map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    rw [map_mul]
    exact LinearMap.rTensor_mul _ _ _

@[simp] theorem trT_tmul (ρ : Representation ℂ G V) (g : G) (v : V) (w : W) :
    trT ρ W g (v ⊗ₜ[ℂ] w) = ρ g v ⊗ₜ[ℂ] w := rfl

theorem twist_trT (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : twist (trT ρ W) χ = trT (twist ρ χ) W := by
  ext g v w
  simp [TensorProduct.smul_tmul']

theorem twKer_trT (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    twKer (trT ρ W) N θ = LinearMap.range (TensorProduct.map (twKer ρ N θ).subtype (LinearMap.id : W →ₗ[ℂ] W)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, x, rfl⟩
    show _ ∈ LinearMap.range _
    induction x with
    | zero => simp
    | add x y hx hy =>
      have : trT ρ W (n : G) (x + y) - ((θ n : ℂˣ) : ℂ) • (x + y) =
          (trT ρ W (n : G) x - ((θ n : ℂˣ) : ℂ) • x) + (trT ρ W (n : G) y - ((θ n : ℂˣ) : ℂ) • y) := by
        rw [map_add, smul_add]; abel
      rw [this]
      exact add_mem hx hy
    | tmul v w =>
      refine ⟨(⟨ρ (n : G) v - ((θ n : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨n, v, rfl⟩⟩ : twKer ρ N θ) ⊗ₜ[ℂ] w, ?_⟩
      simp [TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  · rintro _ ⟨y, rfl⟩
    induction y with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a w =>
      obtain ⟨a, ha⟩ := a
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, v, rfl⟩ := hx
        exact Submodule.subset_span ⟨n, v ⊗ₜ[ℂ] w, by simp [TensorProduct.sub_tmul, TensorProduct.smul_tmul']⟩
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact add_mem hx hy
      | smul c x _ hx => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ _ hx

theorem nonempty_twAct_trT (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hs' : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct (trT ρ W) N θ s hs).Equiv (trT (twAct ρ N θ s hs') W)) := by
  let E : TwJacquet (trT ρ W) N θ ≃ₗ[ℂ] (TwJacquet ρ N θ) ⊗[ℂ] W :=
    (Submodule.quotEquivOfEq _ _ (twKer_trT ρ N θ)).trans (TensorProduct.quotientTensorEquiv W (twKer ρ N θ)).symm
  have hE : ∀ (v : V) (w : W), E (Submodule.Quotient.mk (v ⊗ₜ[ℂ] w)) = Submodule.Quotient.mk v ⊗ₜ[ℂ] w := fun _ _ => rfl
  refine ⟨Representation.Equiv.mk E fun m => LinearMap.ext fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction x with
    | zero => simp
    | add x y hx hy =>
      rw [Submodule.Quotient.mk_add, map_add, map_add, hx, hy]
    | tmul v w =>
      show E (Submodule.Quotient.mk (ρ (s m) v ⊗ₜ[ℂ] w)) = trT (twAct ρ N θ s hs') W m (E (Submodule.Quotient.mk (v ⊗ₜ[ℂ] w)))
      rw [hE, hE]
      rfl

theorem nonempty_cInd_of_top [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (σ : Representation ℂ H W) (R : Representation ℂ G W) (hR : ∀ g, R g = σ ⟨g, hH g⟩) (hs : IsSmooth R) :
    Nonempty ((cInd H σ).Equiv R) := by
  let ev : cIndSpace H σ →ₗ[ℂ] W :=
    { toFun := fun f => f.1.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hval : ∀ (f : cIndSpace H σ) (g : G), f.1.1.1 g = R g (ev f) := by
    intro f g
    have := f.1.1.2 ⟨g, hH g⟩ 1
    simp only [mul_one] at this
    rw [hR]
    exact this
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext g
    rw [hval, hf]
    simp
  have hsurj : Function.Surjective ev := by
    intro w
    have hind : (fun g => R g w) ∈ indSpace H σ := by
      intro h g
      show R ((h : G) * g) w = σ h (R g w)
      rw [map_mul, hR]
      rfl
    have hset : {g : G | ind H σ g ⟨_, hind⟩ = ⟨_, hind⟩} = {g : G | R g w = w} := by
      ext g
      constructor
      · intro hg
        have := congrFun (congrArg Subtype.val hg) 1
        have h2 : R (1 * g) w = R 1 w := this
        simpa using h2
      · intro hg
        apply Subtype.ext
        funext x
        show R (x * g) w = R x w
        rw [map_mul, Module.End.mul_apply]
        exact congrArg _ hg
    have hsm : (⟨_, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
      show IsOpen _
      rw [hset]
      exact hs w
    refine ⟨⟨⟨⟨_, hind⟩, hsm⟩, {1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, rfl, by simp⟩⟩, ?_⟩
    show R 1 w = w
    simp
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun f => ?_⟩
  show ((cInd H σ g f).1.1.1 1) = R g (ev f)
  have : (cInd H σ g f).1.1.1 1 = f.1.1.1 (1 * g) := rfl
  rw [this, one_mul]
  exact hval f g

theorem isSmooth_trT [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    IsSmooth (trT ρ W) := by
  intro x
  show x ∈ smoothPart (trT ρ W)
  induction x with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) fun g hg => ?_)
    have h1 : ρ g v = v := hg
    simp [h1]

end general

section group
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_zero (i : ℕ) (g : Mir k (i + 0)) : g ∈ HPG k i 0 := by
  show (g : GL (Fin (i + 0 + 1)) k) ∈ parab k (ePG i 0)
  refine mem_parab_iff.2 fun a b x y hba => ?_
  cases a with
  | false => exact absurd hba (by simp)
  | true => exact x.elim0

theorem ePG_zero (i : ℕ) (a : Fin (i + 1)) : ePG i 0 ⟨false, a⟩ = a := by
  refine Fin.lastCases ?_ (fun c => ?_) a
  · exact ePG_false_last i 0
  · apply Fin.ext
    simp [ePG, finSumFinEquiv_symm_apply_castSucc]
    rfl

theorem pgProj_zero_fst (i : ℕ) (h : HPG k i 0) : (pgProj k i 0 h).1 = (h : Mir k (i + 0)) := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  show ((leviProj k (ePG i 0) (hpgIncl k i 0 h) false : GL (Fin (i + 1)) k) : Matrix _ _ k) a b = _
  rw [leviProj_apply]
  show (((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k) : Matrix _ _ k) (ePG i 0 ⟨false, a⟩) (ePG i 0 ⟨false, b⟩) = _
  rw [ePG_zero, ePG_zero]

instance subsingleton_GL_zero : Subsingleton (GL (Fin 0) k) :=
  ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

theorem nonempty_prodPG_zero {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin 0) k) W) (hρ : IsSmooth ρ) :
    Nonempty ((prodPG ρ σ).Equiv (trT (G := Mir k (i + 0)) ρ W)) := by
  refine nonempty_cInd_of_top (HPG k i 0) (hpg_zero i) _ _ (fun g => ?_) (isSmooth_trT hρ)
  refine TensorProduct.ext' fun v w => ?_
  have h2 : (pgProj k i 0 ⟨g, hpg_zero i g⟩).2 = 1 := Subsingleton.elim _ _
  show ρ g v ⊗ₜ[ℂ] w = extTensor ρ σ (pgProj k i 0 ⟨g, hpg_zero i g⟩) (v ⊗ₜ[ℂ] w)
  rw [extTensor_tmul, h2, pgProj_zero_fst]
  simp

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n (((0 : ℕ) : ℝ) / 2) = 1 := by
  have h0 : (((((0 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = 0 := by simp
  ext g
  simp [dpowM, dpow, h0, detChar]

theorem mtw_zero_rho {n : ℕ} (τ : MRep k n) : (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ = τ.ρ := by
  show twist τ.ρ (dpowM n (((0 : ℕ) : ℝ) / 2)) = τ.ρ
  rw [dpowM_zero, twist_one]

theorem miso_prodPGn_zero {i : ℕ} (τ : MRep k i) (σ : GRep k 0) (hτ : IsSmooth τ.ρ) :
    MIso (prodPGn τ σ) (⟨τ.V ⊗[ℂ] σ.V, trT (G := Mir k (i + 0)) τ.ρ σ.V⟩ : MRep k (i + 0)) := by
  have h := nonempty_prodPG_zero (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ
    (by rw [mtw_zero_rho]; exact hτ)
  have hh : trT (G := Mir k (i + 0)) (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ σ.V = trT (G := Mir k (i + 0)) τ.ρ σ.V := by
    rw [mtw_zero_rho]
    rfl
  show Nonempty ((prodPG (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).Equiv
    (trT (G := Mir k (i + 0)) τ.ρ σ.V))
  rw [← hh]
  exact h

theorem miso_phiN_trT (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (W : Type) [AddCommGroup W] [Module ℂ W] :
    MIso (phiN ψ (⟨τ.V ⊗[ℂ] W, trT τ.ρ W⟩ : MRep k (n + 1)))
      (⟨(phiN ψ τ).V ⊗[ℂ] W, trT (phiN ψ τ).ρ W⟩ : MRep k n) := by
  obtain ⟨e⟩ := nonempty_twAct_trT (W := W) τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)
    ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n) (levi_stab ψ n)
  have h := nonempty_twist_equiv e (dpowM n (-1 / 2))
  rw [twist_trT] at h
  exact h

end group

theorem phiN_prodPGn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0)
    (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ →
    MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  intro k _ _ _ _ ψ _ _ i τ σ h hτ _
  have e1 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (phiN ψ (⟨τ.V ⊗[ℂ] σ.V, trT τ.ρ σ.V⟩ : MRep k (i + 1))) :=
    miso_phiN k ψ (i + 0) _ _ (miso_prodPGn_zero τ σ hτ)
  exact miso_trans (miso_trans e1 (miso_phiN_trT ψ τ σ.V))
    (miso_symm (miso_prodPGn_zero (phiN ψ τ) σ (isSmooth_phiN ψ hτ)))

end GlobalTheory.CompanionTheory.LeibOrd.GLZero

end
