import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibTrivBlock

theorem nonempty_equiv_cInd {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (hH : ∀ g, g ∈ H) (L : V ≃ₗ[ℂ] W)
    (law : ∀ (h : H) v, σ h (L v) = L (π h v)) : Nonempty (π.Equiv (cInd H σ)) := by
  let f : V →ₗ[ℂ] cIndSpace H σ :=
    { toFun := fun v => ⟨⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩,
        ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, rfl, by simp⟩⟩⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by simp)))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by simp))) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1.1 1), Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1.1 1) h
      simpa using h1
    · have h1 := φ.1.1.2 ⟨x, hH x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hH x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f hb) fun g => LinearMap.ext fun v =>
    Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by
      show L (π x (π g v)) = L (π (x * g) v)
      simp)))⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

instance subsingleton_GL0 : Subsingleton (GL (Fin 0) k) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩

theorem absPow_zero_apply (s : ℂ) (hs : s = 0) (x : kˣ) : absPow k s x = 1 := by
  subst hs
  apply Units.ext
  simp [absPow]

theorem dpow_eq_one (n : ℕ) (s : ℝ) (hs : s = 0) (g : GL (Fin n) k) : dpow n s g = 1 := by
  simp only [dpow, detChar, MonoidHom.comp_apply]
  exact absPow_zero_apply _ (by simp [hs]) _

theorem mem_parab_zero {r : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ x, Two (Fin r) (Fin 0) x) ≃ n)
    (g : GL n k) : g ∈ parab k e := by
  have hb : ∀ x, blk e x = false := by
    intro x
    unfold blk
    rcases e.symm x with ⟨_ | _, c⟩
    · rfl
    · exact c.elim0
  intro a b hlt
  have h1 := hb a
  have h2 := hb b
  simp [h1, h2] at hlt

theorem deltaHalf_zero {r : ℕ} (z : Levi k (Two (Fin r) (Fin 0))) : deltaHalf k (Two (Fin r) (Fin 0)) z = 1 := by
  have h := deltaHalf_two (k := k) (a := Fin r) (b := Fin 0) ((leviTwo k (Fin r) (Fin 0)).symm z)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, absPow_zero_apply _ (by simp), Subsingleton.elim ((leviTwo k (Fin r) (Fin 0)).symm z).2 1]
  simp

theorem ePG_zero_val (i : ℕ) (b : Fin (i + 1)) : (ePG i 0 ⟨false, b⟩ : Fin (i + 0 + 1)).val = b.val := by
  induction b using Fin.lastCases with
  | last => rw [ePG_false_last]; simp
  | cast c =>
    simp [ePG, finSumFinEquiv_symm_apply_castSucc]
    rw [finSumFinEquiv_apply_left]
    rfl

theorem leviProj_std_false {i : ℕ} (p : parab k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)))) :
    (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p false : GL (Fin (i + 1)) k) = (p : GL (Fin (i + 1 + 0)) k) := by
  apply Units.ext
  ext a b
  rw [leviProj_apply]
  have : ∀ c : Fin (i + 1), two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)) ⟨false, c⟩ = c := fun c => by
    apply Fin.ext
    simp [two, stdSum]
  rw [this, this]

theorem pgProj_fst {i : ℕ} (h : HPG k i 0) :
    (((pgProj k i 0 h).1 : Mir k i) : GL (Fin (i + 1)) k) = ((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k) := by
  apply Units.ext
  ext a b
  show (leviProj k (ePG i 0) (hpgIncl k i 0 h) false : GL (Fin (i + 1)) k).val a b = _
  rw [leviProj_apply]
  have : ∀ c : Fin (i + 1), ePG i 0 ⟨false, c⟩ = c := fun c => Fin.ext (ePG_zero_val i c)
  rw [this, this]
  rfl

def actFst {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin n) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) :
    Representation ℂ (GL (Fin n) k) (V ⊗[ℂ] W) :=
  (extTensor π₁ π₂).comp (MonoidHom.inl _ _)

theorem actFst_tmul {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin n) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) (g : GL (Fin n) k) (v : V) (w : W) :
    actFst π₁ π₂ g (v ⊗ₜ w) = π₁ g v ⊗ₜ w := by
  simp [actFst, extTensor_tmul]

theorem isSmooth_actFst {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (GL (Fin n) k) V} {π₂ : Representation ℂ (GL (Fin 0) k) W}
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (actFst π₁ π₂) :=
  isSmooth_comp (isSmooth_extTensor h₁ h₂) _ (by
    show Continuous fun g : GL (Fin n) k => (g, (1 : GL (Fin 0) k))
    exact continuous_id.prodMk continuous_const)

theorem tE_piTensor {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (p : parab k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)))) (y : ⨂[ℂ] x, TwoT V W x) :
    BZRes.tE V W (piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p) y) =
      actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k) (BZRes.tE V W y) := by
  have key : ((BZRes.tE V W).toLinearMap ∘ₗ piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p)) =
      (actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k)) ∘ₗ (BZRes.tE V W).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show BZRes.tE V W (piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p)
        (PiTensorProduct.tprod ℂ x)) = actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k) (BZRes.tE V W (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod]
    refine (Exponents.boolTensorEquiv_tprod _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Exponents.boolTensorEquiv_tprod x).symm)
    rw [actFst_tmul, ← leviProj_std_false p]
    show π₁ _ (x false) ⊗ₜ[ℂ] π₂ _ (x true) = _
    rw [Subsingleton.elim (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p true : GL (Fin 0) k) 1, map_one]
    rfl
  exact LinearMap.congr_fun key y

theorem nonempty_actFst_equiv_prod2 {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) :
    Nonempty ((show Representation ℂ (GL (Fin (i + 1 + 0)) k) (V ⊗[ℂ] W) from actFst π₁ π₂).Equiv
      (prod2 (rfl : (i + 1) + 0 = (i + 1) + 0) π₁ π₂)) := by
  refine WordProd.OneBlockProd.nonempty_equiv_parInd _ (isSmooth_actFst h₁ h₂) (mem_parab_zero _) deltaHalf_zero
    (BZRes.tE V W).symm fun p v => ?_
  apply (BZRes.tE V W).injective
  rw [tE_piTensor, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hpg_act {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (χ₁ : Mir k i →* ℂˣ) (χ₂ : GL (Fin 0) k →* ℂˣ) (hχ : ∀ g, χ₁ g = 1) (h : HPG k i 0) (x : V ⊗[ℂ] W) :
    ((extTensor (twist (π₁.comp (Mir k i).subtype) χ₁) (twist π₂ χ₂)).comp (pgProj k i 0)) h x =
      actFst π₁ π₂ (((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v w =>
    rw [actFst_tmul, MonoidHom.comp_apply, extTensor_tmul, ← pgProj_fst h, Subsingleton.elim (pgProj k i 0 h).2 1]
    simp [twist_apply, hχ]

theorem miso_gres_prod_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  intro k _ _ _ _ i n π₁ π₂ h h' h₁ h₂
  subst h'
  obtain ⟨E₁⟩ := nonempty_actFst_equiv_prod2 π₁.ρ π₂.ρ h₁ h₂
  have hs : IsSmooth ((actFst π₁.ρ π₂.ρ : Representation ℂ (GL (Fin (i + 0 + 1)) k) (π₁.V ⊗[ℂ] π₂.V)).comp
      (Mir k (i + 0)).subtype) :=
    isSmooth_comp (isSmooth_actFst h₁ h₂) _ continuous_subtype_val
  obtain ⟨E₂⟩ := nonempty_equiv_cInd (HPG k i 0)
    ((extTensor (mtw (gres π₁) (((0 : ℕ) : ℝ) / 2)).ρ (π₂.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i 0)) hs
    (fun g => mem_parab_zero _ _) (LinearEquiv.refl ℂ _) (fun g x => hpg_act π₁.ρ π₂.ρ _ _ (fun a => dpow_eq_one _ _ (by simp) _) g x)
  refine ⟨Representation.Equiv.trans (Representation.Equiv.mk E₁.symm.toLinearEquiv fun g => ?_) E₂⟩
  ext v
  exact eint E₁.symm _ v

end GlobalTheory.CompanionTheory.LeibTrivBlock

end
