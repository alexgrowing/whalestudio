import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx

structure Level (G : Type*) [Group G] where

  J : Subgroup G

  lam : J →* ℂˣ

def Level.map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (P : Level G) : Level G' where
  J := P.J.comap φ.symm.toMonoidHom
  lam := P.lam.comp (φ.symm.toMonoidHom.subgroupComap P.J)

theorem Level.mem_map {G G' : Type*} [Group G] [Group G'] {φ : G ≃* G'} {P : Level G} {h : G'} :
    h ∈ (P.map φ).J ↔ φ.symm h ∈ P.J := Iff.rfl

theorem Level.map_lam {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (P : Level G) (h : (P.map φ).J) :
    (P.map φ).lam h = P.lam ⟨φ.symm h, h.2⟩ := rfl

section Plain
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]

open Classical in

def extZ (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (M : Matrix a a k) : ℂ :=
  if h : ∃ g : J, (g : GL a k).val = M then (ρ h.choose : ℂ) else 0

theorem extZ_coe (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (g : J) : extZ J ρ (g : GL a k).val = ρ g := by
  have h : ∃ g' : J, (g' : GL a k).val = (g : GL a k).val := ⟨g, rfl⟩
  rw [extZ, dif_pos h, show h.choose = g from Subtype.ext (Units.ext h.choose_spec)]

theorem extZ_of_not (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) {M : Matrix a a k}
    (h : ¬ ∃ g ∈ J, g.val = M) : extZ J ρ M = 0 :=
  dif_neg fun ⟨g, hg⟩ => h ⟨g, g.2, hg⟩

theorem extZ_ne_zero_iff (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) {M : Matrix a a k} :
    extZ J ρ M ≠ 0 ↔ ∃ g ∈ J, g.val = M := by
  refine ⟨fun h => by_contra fun h' => h (extZ_of_not J ρ h'), ?_⟩
  rintro ⟨g, hg, rfl⟩
  rw [extZ_coe J ρ ⟨g, hg⟩]; exact Units.ne_zero _

def reGL (e : a ≃ b) : GL a k ≃* GL b k := Units.mapEquiv (Matrix.reindexRingEquiv k e).toMulEquiv

theorem reGL_val (e : a ≃ b) (g : GL a k) : (reGL e g).val = g.val.submatrix e.symm e.symm := rfl

theorem reGL_symm_val (e : a ≃ b) (g : GL b k) : ((reGL e).symm g).val = g.val.submatrix e e := rfl

theorem det_reGL (e : a ≃ b) (g : GL a k) :
    Matrix.GeneralLinearGroup.det (reGL e g) = Matrix.GeneralLinearGroup.det g :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, reGL_val])

def embTop (t : Type*) [Fintype t] [DecidableEq t] : GL a k →* GL (a ⊕ t) k :=
  Units.map
    { toFun := fun g : Matrix a a k => (fromBlocks g 0 0 1 : Matrix (a ⊕ t) (a ⊕ t) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }

theorem embTop_val (g : GL a k) : (embTop t g).val = fromBlocks g.val 0 0 1 := rfl

omit [DecidableEq a] [DecidableEq t] in
theorem mul_toBlocks₁₁ (M M' : Matrix (a ⊕ t) (a ⊕ t) k) :
    (M * M').toBlocks₁₁ = M.toBlocks₁₁ * M'.toBlocks₁₁ + M.toBlocks₁₂ * M'.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks M', fromBlocks_multiply, toBlocks_fromBlocks₁₁]

omit [DecidableEq a] [DecidableEq t] in
theorem mul_toBlocks₂₁ (M M' : Matrix (a ⊕ t) (a ⊕ t) k) :
    (M * M').toBlocks₂₁ = M.toBlocks₂₁ * M'.toBlocks₁₁ + M.toBlocks₂₂ * M'.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks M', fromBlocks_multiply, toBlocks_fromBlocks₂₁]

end Plain

abbrev Ix (r t : Type*) (j : ℕ) : Type _ := r ⊕ (Fin j × t)

def Ix.blk {r t : Type*} {j : ℕ} : Ix r t j → ℕ := Sum.elim (fun _ => 0) (fun p => p.1.val + 1)

def Ix.diagonalBlockOfMatrix {r t k : Type*} {j : ℕ} (M : Matrix (Ix r t j) (Ix r t j) k) (i : Fin j) : Matrix t t k :=
  M.submatrix (fun s => Sum.inr (i, s)) (fun s => Sum.inr (i, s))

def ixZero (r t : Type*) : r ≃ Ix r t 0 := (Equiv.sumEmpty r (Fin 0 × t)).symm

def ixSucc (r t : Type*) (j : ℕ) : Ix r t j ⊕ t ≃ Ix r t (j + 1) where
  toFun := Sum.elim (Sum.map id fun p => (p.1.castSucc, p.2)) fun s => Sum.inr (Fin.last j, s)
  invFun := Sum.elim (fun i => Sum.inl (Sum.inl i))
    fun p => Fin.lastCases (Sum.inr p.2) (fun i => Sum.inl (Sum.inr (i, p.2))) p.1
  left_inv := by rintro ((i | ⟨i, s⟩) | s) <;> simp
  right_inv := by
    rintro (i | ⟨i, s⟩)
    · simp
    · induction i using Fin.lastCases <;> simp

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]

variable (k a) in

structure TypeDatum extends Level (GL a k) where
  KOne_le : KOne k a ≤ J
  le_KO : J ≤ KO k a
  lam_eq_one : ∀ g : J, (g : GL a k) ∈ KOne k a → lam g = 1

namespace TypeDatum

variable (k a) in

def full : TypeDatum k a := ⟨⟨KO k a, 1⟩, StepData.KOne_le_KO, le_rfl, fun _ _ => rfl⟩

variable (k a) in

def principal : TypeDatum k a := ⟨⟨KOne k a, 1⟩, le_rfl, StepData.KOne_le_KO, fun _ _ => rfl⟩

def ofResidue (H : Subgroup (GL a 𝓀[k])) (χ : H →* ℂˣ) : TypeDatum k a where
  J := (H.comap (Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]))).map
    (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k))
  lam := (χ.comp ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H)).comp
    (Subgroup.equivMapOfInjective _ _ (Units.map_injective
      (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k)))).symm.toMonoidHom
  KOne_le := Subgroup.map_mono fun g hg => by
    rw [Subgroup.mem_comap, show _ = (1 : GL a 𝓀[k]) from hg]; exact H.one_mem
  le_KO := Subgroup.map_le_range _ _
  lam_eq_one := by
    rintro ⟨_, u, hu, rfl⟩ ⟨u', hu', e⟩
    have inj : Function.Injective (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k)) :=
      Units.map_injective (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k))
    obtain rfl : u' = u := inj e
    have h1 : (Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u', hu, rfl⟩ = ⟨u', hu⟩ :=
      (MulEquiv.symm_apply_eq _).2 rfl
    change χ ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H
      ((Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u', hu, rfl⟩)) = 1
    rw [h1, ← map_one χ]
    exact congrArg χ (Subtype.ext hu')

theorem ofResidue_lam (H : Subgroup (GL a 𝓀[k])) (χ : H →* ℂˣ) (u : GL a 𝒪[k])
    (hu : Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]) u ∈ H) :
    (ofResidue H χ).lam ⟨Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k) u, u, hu, rfl⟩ = χ ⟨_, hu⟩ := by
  have inj : Function.Injective (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k)) :=
    Units.map_injective (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k))
  have h1 : (Subgroup.equivMapOfInjective
      (H.comap (Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]))) _ inj).symm ⟨_, u, hu, rfl⟩ =
      ⟨u, hu⟩ := (MulEquiv.symm_apply_eq _).2 rfl
  change χ ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H
    ((Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u, hu, rfl⟩)) = _
  rw [h1]; rfl

variable (P : TypeDatum k a)

theorem isOpen : IsOpen (P.J : Set (GL a k)) := Subgroup.isOpen_mono P.KOne_le isOpen_KOne

theorem isCompact : IsCompact (P.J : Set (GL a k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ P.isOpen) P.le_KO

theorem exists_of_congr {g : GL a k} (hg : g ∈ P.J) {M : Matrix a a k} (h : MaxM (M - g.val)) :
    ∃ g' ∈ P.J, g'.val = M := by
  obtain ⟨u, hu, hu'⟩ := exists_mul_KOne (P.le_KO hg) h
  exact ⟨g * u, P.J.mul_mem hg (P.KOne_le hu), hu'⟩

def reindex (e : a ≃ b) : TypeDatum k b where
  toLevel := P.toLevel.map (reGL e)
  KOne_le := fun g hg => P.KOne_le (mem_KOne.2 fun i j => by
    simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hg (e i) (e j))
  le_KO := fun g hg => by
    obtain ⟨h1, h2⟩ := mem_KO.1 (P.le_KO hg)
    exact mem_KO.2 ⟨fun i j => by simpa [reGL_symm_val] using h1 (e.symm i) (e.symm j),
      fun i j => by
        have := h2 (e.symm i) (e.symm j)
        rw [← map_inv] at this
        simpa [reGL_symm_val] using this⟩
  lam_eq_one := fun g hg => P.lam_eq_one ⟨(reGL e).symm g, g.2⟩ (mem_KOne.2 fun i j => by
    simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hg (e i) (e j))

def rho (μ : kˣ →* ℂˣ) : P.J →* ℂˣ :=
  P.lam * (μ.comp (Matrix.GeneralLinearGroup.det.comp P.J.subtype))⁻¹

theorem rho_apply (μ : kˣ →* ℂˣ) (g : P.J) :
    P.rho μ g = P.lam g * (μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ := rfl

theorem rho_congr {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g g' : P.J} (h : MaxM ((g' : GL a k).val - (g : GL a k).val)) :
    P.rho μ g' = P.rho μ g := by
  have hu := inv_mul_mem_KOne (P.le_KO g.2) h
  have : P.rho μ (g⁻¹ * g') = 1 := by
    rw [rho_apply, P.lam_eq_one _ hu, show ((g⁻¹ * g' : P.J) : GL a k) = (g : GL a k)⁻¹ * g' from rfl,
      tame_det_of_mem_KOne hμ hu]; simp
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

variable (t) in

def stepJ : Subgroup (GL (a ⊕ t) k) where
  carrier := {h | h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧ IntM h.val.toBlocks₁₂ ∧
    MaxM h.val.toBlocks₂₁ ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂}
  one_mem' := ⟨one_mem _, ⟨1, one_mem _, by simp [← fromBlocks_one]⟩, by simpa [← fromBlocks_one] using intM_zero,
    by simpa [← fromBlocks_one] using maxM_zero, 1, one_mem _, by simp [← fromBlocks_one]⟩
  mul_mem' := by
    rintro h h' ⟨h0, ⟨g, hg, eg⟩, hB, hC, D, hD, eD⟩ ⟨h0', ⟨g', hg', eg'⟩, hB', hC', -⟩
    have hC'' : MaxM (h * h').val.toBlocks₂₁ := by
      rw [Units.val_mul, mul_toBlocks₂₁, ← eg', ← eD]
      exact (hC.mul_intM (intM_of_mem_KO (P.le_KO hg'))).add ((intM_of_mem_KO hD).mul_maxM hC')
    refine ⟨mul_mem h0 h0', P.exists_of_congr (P.J.mul_mem hg hg') ?_,
      fun i j => intM_of_mem_KO (mul_mem h0 h0') _ _, hC'', (exists_diag_blocks (mul_mem h0 h0') hC'').2⟩
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_mul, eg, eg']
    simpa using hB.mul_maxM hC'
  inv_mem' := by
    rintro h ⟨h0, ⟨g, hg, eg⟩, -, hC, -⟩
    obtain ⟨m1, -, m3⟩ := blocks_inv h0 hC
    refine ⟨inv_mem h0, P.exists_of_congr (P.J.inv_mem hg) ?_, fun i j => intM_of_mem_KO (inv_mem h0) _ _, m3,
      (exists_diag_blocks (inv_mem h0) m3).2⟩
    have := (mem_KO.1 (P.le_KO hg)).2.mul_maxM m1
    rwa [← eg, Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at this

theorem mem_stepJ {h : GL (a ⊕ t) k} : h ∈ P.stepJ t ↔ h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧
    IntM h.val.toBlocks₁₂ ∧ MaxM h.val.toBlocks₂₁ ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂ := Iff.rfl

theorem mem_stepJ_iff {h : GL (a ⊕ t) k} : h ∈ P.stepJ t ↔
    h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧ MaxM h.val.toBlocks₂₁ :=
  ⟨fun H => ⟨H.1, H.2.1, H.2.2.2.1⟩, fun H => ⟨H.1, H.2.1, fun _ _ => intM_of_mem_KO H.1 _ _, H.2.2,
    (exists_diag_blocks H.1 H.2.2).2⟩⟩

def corner (h : P.stepJ t) : P.J := ⟨h.2.2.1.choose, h.2.2.1.choose_spec.1⟩

theorem corner_val (h : P.stepJ t) : (P.corner h : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁ :=
  h.2.2.1.choose_spec.2

theorem corner_mul (h h' : P.stepJ t) :
    MaxM ((P.corner (h * h') : GL a k).val - ((P.corner h * P.corner h' : P.J) : GL a k).val) := by
  rw [corner_val, Subgroup.coe_mul, Units.val_mul, mul_toBlocks₁₁, Subgroup.coe_mul, Units.val_mul, corner_val, corner_val]
  simpa using h.2.2.2.1.mul_maxM h'.2.2.2.2.1

variable (t) in

def stepLam (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : P.stepJ t →* ℂˣ :=
  MonoidHom.mk' (fun h => P.lam (P.corner h) * (μ (Matrix.GeneralLinearGroup.det (P.corner h : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k))) fun h h' => by
    simp only [← rho_apply]
    rw [P.rho_congr hμ (P.corner_mul h h'), map_mul, Subgroup.coe_mul, map_mul, map_mul, mul_mul_mul_comm]

variable (t) in

def step (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : TypeDatum k (a ⊕ t) where
  J := P.stepJ t
  lam := P.stepLam t μ hμ
  KOne_le := fun h hh => by
    have m := mem_KOne.1 hh
    refine P.mem_stepJ_iff.2 ⟨StepData.KOne_le_KO hh, P.exists_of_congr P.J.one_mem fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.one_apply, toBlocks₁₁] using m (.inl i) (.inl j)
    · simpa [Matrix.one_apply, toBlocks₂₁] using m (.inr i) (.inl j)
  le_KO := fun _ hh => hh.1
  lam_eq_one := fun h hh => by
    have m := mem_KOne.1 hh
    have hc : (P.corner h : GL a k) ∈ KOne k a := mem_KOne.2 fun i j => by
      rw [corner_val]; simpa [Matrix.one_apply, toBlocks₁₁] using m (.inl i) (.inl j)
    change P.lam (P.corner h) * (μ (Matrix.GeneralLinearGroup.det (P.corner h : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k)) = 1
    rw [P.lam_eq_one _ hc, tame_det_of_mem_KOne hμ hc, tame_det_of_mem_KOne hμ hh]; simp

theorem step_J (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : (P.step t μ hμ).J = P.stepJ t := rfl

theorem step_lam (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (h : P.stepJ t) (g : P.J)
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) :
    (P.step t μ hμ).lam h = P.lam g * (μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k)) := by
  obtain rfl : g = P.corner h := Subtype.ext (Units.ext (hg.trans (P.corner_val h).symm))
  rfl

theorem step_lam_eq (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (h : P.stepJ t) (g : P.J)
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) (D : GL t k)
    (hD : D.val = (h : GL (a ⊕ t) k).val.toBlocks₂₂) :
    (P.step t μ hμ).lam h = P.lam g * μ (Matrix.GeneralLinearGroup.det D) := by
  rw [P.step_lam μ hμ h g hg, tame_det_blocks hμ h.2.1 h.2.2.2.2.1 hg hD, mul_assoc, inv_mul_cancel_left]

open Classical in
variable (t) in

def Phi (μ : kˣ →* ℂˣ) : Matrix (a ⊕ t) a k → ℂ := fun x =>
  if MaxM x.toRows₂ then extZ P.J (P.rho μ) x.toRows₁ else 0

omit [Fintype t] [DecidableEq t] in
theorem Phi_of_mem (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} (g : P.J) (hg : (g : GL a k).val = x.toRows₁)
    (hx : MaxM x.toRows₂) :
    P.Phi t μ x = (P.lam g : ℂ) * ((μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ : ℂˣ) := by
  rw [Phi, if_pos hx, ← hg, extZ_coe, rho_apply, Units.val_mul]

omit [Fintype t] [DecidableEq t] in
theorem Phi_ne_zero_iff (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} :
    P.Phi t μ x ≠ 0 ↔ (∃ g ∈ P.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂ := by
  unfold Phi
  split_ifs with h <;> simp [h, extZ_ne_zero_iff]

theorem extZ_add {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (M : Matrix a a k) {Y : Matrix a a k} (hY : MaxM Y) :
    extZ P.J (P.rho μ) (M + Y) = extZ P.J (P.rho μ) M := by
  by_cases h : ∃ g ∈ P.J, g.val = M
  · obtain ⟨g, hg, rfl⟩ := h
    obtain ⟨g', hg', e⟩ := P.exists_of_congr hg (M := g.val + Y) (by simpa using hY)
    rw [← e, extZ_coe _ _ ⟨g', hg'⟩, extZ_coe _ _ ⟨g, hg⟩, P.rho_congr hμ (g := ⟨g, hg⟩) (by simpa [e] using hY)]
  · rw [extZ_of_not _ _ h, extZ_of_not]
    rintro ⟨g, hg, e⟩
    exact h (P.exists_of_congr hg (by simpa [e] using hY.neg))

open Classical in
omit [Fintype t] [DecidableEq t] in

theorem Phi_add {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (x : Matrix (a ⊕ t) a k) {y : Matrix (a ⊕ t) a k} (hy : MaxM y) :
    P.Phi t μ (x + y) = P.Phi t μ x := by
  have h2 : MaxM y.toRows₂ := fun i j => hy _ _
  have e : MaxM (x + y).toRows₂ ↔ MaxM x.toRows₂ :=
    ⟨fun h => by simpa using (show MaxM (x.toRows₂ + y.toRows₂) from h).add h2.neg, fun h => h.add h2⟩
  have e' : extZ P.J (P.rho μ) (x + y).toRows₁ = extZ P.J (P.rho μ) x.toRows₁ :=
    P.extZ_add hμ x.toRows₁ (Y := y.toRows₁) fun i j => hy _ _
  unfold Phi
  exact if_congr e e' rfl

omit [Fintype t] [DecidableEq t] in

theorem intM_of_Phi_ne_zero (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} (h : P.Phi t μ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
  rintro (i | i) j
  · have := intM_of_mem_KO (P.le_KO hg) i j
    rwa [e] at this
  · exact h2.intM i j

end TypeDatum

omit [DecidableEq a] [DecidableEq b] in

theorem mem_SB_of_periodic {f : Matrix b a k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, MaxM y → f (x + y) = f x) : f ∈ SB (Matrix b a k) := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{x' | MaxM (x' - x)}, ?_, by simpa using maxM_zero,
    fun x' hx' => by rw [← hp x _ hx', add_sub_cancel]⟩,
    HasCompactSupport.intro (SplitFlip.isCompact_intMatrix (k := k) (m := b) (n := a))
      fun x hx => by_contra fun h => hx (hs x h)⟩
  simp only [MaxM, Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact IsOpen.preimage (f := fun x' : Matrix b a k => (x' - x) i j) (t := {z | valuation k z < 1}) (by fun_prop)
    (by simpa using (valuation k).isOpen_ball 1)

omit [DecidableEq t] in
theorem TypeDatum.Phi_mem_SB (P : TypeDatum k a) {μ : kˣ →* ℂˣ} (hμ : IsTame μ) :
    P.Phi t μ ∈ SB (Matrix (a ⊕ t) a k) :=
  mem_SB_of_periodic (fun _ => P.intM_of_Phi_ne_zero μ) fun x _ hy => P.Phi_add hμ x hy

section Iter
variable {r : Type*} [Fintype r] [DecidableEq r]

variable (t) in

def TypeDatum.iter (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    TypeDatum k (Ix r t j) :=
  Nat.rec (motive := fun j => TypeDatum k (Ix r t j)) (P.reindex (ixZero r t))
    (fun j Q => (Q.step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)) j

theorem TypeDatum.iter_zero (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    P.iter t μ hμ 0 = P.reindex (ixZero r t) := rfl

theorem TypeDatum.iter_succ (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    P.iter t μ hμ (j + 1) = ((P.iter t μ hμ j).step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j) := rfl

variable (t) in

def TypeDatum.iterPhi (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    Matrix (Ix r t (j + 1)) (Ix r t j) k → ℂ := fun x =>
  (P.iter t μ hμ j).Phi t (μ (j + 1)) (x.submatrix (ixSucc r t j) id)

theorem TypeDatum.iterPhi_mem_SB (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    P.iterPhi t μ hμ j ∈ SB (Matrix (Ix r t (j + 1)) (Ix r t j) k) :=
  mem_SB_of_periodic
    (fun x hx i l => by simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc r t j).symm i) l)
    fun x y hy => TypeDatum.Phi_add _ (hμ _) (x.submatrix (ixSucc r t j) id) (y := y.submatrix (ixSucc r t j) id)
      fun _ _ => hy _ _

end Iter

section Parahoric
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

variable (r s) in

def parahoric (δ : kˣ →* ℂˣ) (hδ : IsTame δ) : TypeDatum k (r ⊕ s) := (TypeDatum.full k r).step s δ hδ

theorem mem_parahoric {δ : kˣ →* ℂˣ} {hδ : IsTame δ} {h : GL (r ⊕ s) k} :
    h ∈ (parahoric r s δ hδ).J ↔ h ∈ KO k (r ⊕ s) ∧ MaxM h.val.toBlocks₂₁ :=
  (TypeDatum.mem_stepJ_iff _).trans
    ⟨fun H => ⟨H.1, H.2.2⟩, fun H => ⟨H.1, (exists_diag_blocks H.1 H.2).1, H.2⟩⟩

theorem parahoric_lam {δ : kˣ →* ℂˣ} {hδ : IsTame δ} (h : (parahoric r s δ hδ).J) (D : GL s k)
    (hD : D.val = (h : GL (r ⊕ s) k).val.toBlocks₂₂) :
    (parahoric r s δ hδ).lam h = δ (Matrix.GeneralLinearGroup.det D) := by
  have := (TypeDatum.full k r).step_lam_eq δ hδ h _ (TypeDatum.corner_val _ h) D hD
  exact this.trans (one_mul _)

open Classical in

def parPhi (δ : kˣ →* ℂˣ) : Matrix (r ⊕ s) (r ⊕ s') k → ℂ := fun x =>
  if MaxM x.toBlocks₂₁ ∧ IntM x.toBlocks₁₂ ∧ IntM x.toBlocks₂₂ then
    extZ (KO k r) (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ x.toBlocks₁₁ else 0

omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem parPhi_of_mem (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} {g : GL r k} (hg : g ∈ KO k r)
    (e : g.val = x.toBlocks₁₁) (h21 : MaxM x.toBlocks₂₁) (h12 : IntM x.toBlocks₁₂) (h22 : IntM x.toBlocks₂₂) :
    parPhi δ x = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) := by
  rw [parPhi, if_pos ⟨h21, h12, h22⟩, ← e, extZ_coe _ _ ⟨g, hg⟩]; rfl

omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem parPhi_fromBlocks (δ : kˣ →* ℂˣ) {A : Matrix r r k} {B : Matrix r s' k} {C : Matrix s r k} {D : Matrix s s' k}
    {g : GL r k} (hg : g ∈ KO k r) (e : g.val = A) (h21 : MaxM C) (h12 : IntM B) (h22 : IntM D) :
    parPhi δ (fromBlocks A B C D) = ((δ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) :=
  parPhi_of_mem δ hg e h21 h12 h22

omit [Fintype s] [DecidableEq s] in

theorem parPhi_eq_Phi [IsEmpty s'] (δ : kˣ →* ℂˣ)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x = (TypeDatum.full k r).Phi s δ x.toCols₁ := by
  have e4 : (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ = (TypeDatum.full k r).rho δ :=
    (one_mul _).symm
  by_cases h : MaxM x.toBlocks₂₁
  · rw [parPhi, if_pos ⟨h, fun _ j => isEmptyElim j, fun _ j => isEmptyElim j⟩, TypeDatum.Phi,
      if_pos (show MaxM x.toCols₁.toRows₂ from h), e4]; rfl
  · rw [parPhi, if_neg fun H => h H.1, TypeDatum.Phi, if_neg (show ¬ MaxM x.toCols₁.toRows₂ from h)]

omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem parPhi_ne_zero_iff (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} :
    parPhi δ x ≠ 0 ↔ (∃ g ∈ KO k r, g.val = x.toBlocks₁₁) ∧ MaxM x.toBlocks₂₁ ∧ IntM x.toBlocks₁₂ ∧
      IntM x.toBlocks₂₂ := by
  unfold parPhi
  split_ifs with h <;> simp [h, extZ_ne_zero_iff]

open Classical in
omit [DecidableEq s] in
theorem parPhi_mem_SB [Fintype s'] {δ : kˣ →* ℂˣ} (hδ : IsTame δ) :
    parPhi δ ∈ SB (Matrix (r ⊕ s) (r ⊕ s') k) := by
  refine mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
    rw [← fromBlocks_toBlocks x, ← e]
    exact intM_fromBlocks.2 ⟨intM_of_mem_KO hg, h12, h21.intM, h22⟩
  · rw [← fromBlocks_toBlocks y] at hy
    obtain ⟨y11, y12, y21, y22⟩ := maxM_fromBlocks.1 hy
    have e1 : MaxM (x + y).toBlocks₂₁ ↔ MaxM x.toBlocks₂₁ :=
      ⟨fun h => by simpa using (show MaxM (x.toBlocks₂₁ + y.toBlocks₂₁) from h).add y21.neg, fun h => h.add y21⟩
    have e2 : IntM (x + y).toBlocks₁₂ ↔ IntM x.toBlocks₁₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₁₂ + y.toBlocks₁₂) from h).add y12.intM.neg,
        fun h => h.add y12.intM⟩
    have e3 : IntM (x + y).toBlocks₂₂ ↔ IntM x.toBlocks₂₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₂₂ + y.toBlocks₂₂) from h).add y22.intM.neg,
        fun h => h.add y22.intM⟩
    unfold parPhi
    have e4 : (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k r).subtype))⁻¹ = (TypeDatum.full k r).rho δ :=
      (one_mul _).symm
    rw [e4]
    exact if_congr (and_congr e1 (and_congr e2 e3)) ((TypeDatum.full k r).extZ_add hδ x.toBlocks₁₁ y11) rfl

end Parahoric

example (P : TypeDatum k a) (μ : kˣ →* ℂˣ) : P.Phi t μ (fromRows 1 0) = 1 := by
  rw [P.Phi_of_mem μ 1 (by simp) (by simpa using maxM_zero)]; simp

example [Nonempty a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ) : P.Phi t μ 0 = 0 := by
  by_contra h
  obtain ⟨⟨g, -, e⟩, -⟩ := (P.Phi_ne_zero_iff μ).1 h
  exact g.ne_zero (e.trans (by ext; simp))

example (μ : kˣ →* ℂˣ) (u : GL a k) (hu : u ∈ KO k a) :
    (TypeDatum.full k a).Phi t μ (fromRows u.val 0) = ((μ (Matrix.GeneralLinearGroup.det u))⁻¹ : ℂˣ) := by
  rw [TypeDatum.Phi_of_mem _ μ ⟨u, hu⟩ (by simp) (by simpa using maxM_zero)]; exact one_mul _

end Local

section Frames
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

variable (k ι Y) in

structure LatFrame where

  ord : ι ≃ Y

  bas : GL Y k

namespace LatFrame

variable (k ι) in

def refl : LatFrame k ι ι := ⟨Equiv.refl ι, 1⟩

def conj (F : LatFrame k ι Y) : GL ι k ≃* GL Y k := (reGL F.ord).trans (MulAut.conj F.bas)

theorem conj_apply (F : LatFrame k ι Y) (g : GL ι k) : F.conj g = F.bas * reGL F.ord g * F.bas⁻¹ := rfl

def coords (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x : Matrix Y Y' k) : Matrix ι ι' k :=
  ((F.bas⁻¹).val * x * F'.bas.val).submatrix F.ord F'.ord

def transport (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (Φ : Matrix ι ι' k → ℂ) : Matrix Y Y' k → ℂ :=
  fun x => Φ (F.coords F' x)

theorem det_conj (F : LatFrame k ι Y) (g : GL ι k) :
    Matrix.GeneralLinearGroup.det (F.conj g) = Matrix.GeneralLinearGroup.det g := by
  rw [conj_apply, map_mul, map_mul, map_inv, det_reGL, mul_inv_cancel_comm]

theorem coords_mul (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (h : GL ι k) (g : GL ι' k) (x : Matrix Y Y' k) :
    F.coords F' ((F.conj h).val * x * (F'.conj g).val) = h.val * F.coords F' x * g.val := by
  have e : (F.bas⁻¹).val * ((F.conj h).val * x * (F'.conj g).val) * F'.bas.val =
      (reGL F.ord h).val * ((F.bas⁻¹).val * x * F'.bas.val) * (reGL F'.ord g).val := by
    simp only [conj_apply, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold coords
  rw [e, ← submatrix_mul_equiv _ _ _ F'.ord, ← submatrix_mul_equiv _ _ _ F.ord]
  simp [reGL_val]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_transport (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (μ : kˣ →* ℂˣ) (g : GL ι' k) (h : GL ι k)
    (Φ : Matrix ι ι' k → ℂ) :
    om μ (F'.conj g) (F.conj h) (F.transport F' Φ) = F.transport F' (om μ g h Φ) := by
  funext x
  simp only [om, transport, det_conj, ← Fintype.card_congr F.ord, ← Fintype.card_congr F'.ord]
  rw [← map_inv F.conj, coords_mul]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem transport_mem_SB (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') {Φ : Matrix ι ι' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix ι ι' k)) : F.transport F' Φ ∈ SB (Matrix Y Y' k) := by
  let e : Matrix Y Y' k ≃ₜ Matrix ι ι' k :=
    { Matrix.reindex F.ord.symm F'.ord.symm with
      continuous_toFun := continuous_id.matrix_reindex _ _
      continuous_invFun := continuous_id.matrix_reindex _ _ }
  let e' := (sideMul F'.bas F.bas).trans e
  exact ⟨hΦ.1.comp_continuous e'.continuous, hΦ.2.comp_homeomorph e'⟩

end LatFrame

variable [ValuativeRel k]

def latOf (g : GL Y k) : Submodule 𝒪[k] (Y → k) where
  carrier := {y | ∀ i, ((g⁻¹).val *ᵥ y) i ∈ 𝒪[k]}
  add_mem' := fun hy hz i => by rw [mulVec_add]; exact add_mem (hy i) (hz i)
  zero_mem' := fun i => by simp
  smul_mem' := fun c y hy i => by
    rw [show c • y = (c : k) • y from rfl, mulVec_smul]; exact mul_mem c.2 (hy i)

theorem mem_latOf {g : GL Y k} {y : Y → k} : y ∈ latOf g ↔ ∀ i, ((g⁻¹).val *ᵥ y) i ∈ 𝒪[k] := Iff.rfl

theorem mem_latOf_one {y : Y → k} : y ∈ latOf (1 : GL Y k) ↔ ∀ i, y i ∈ 𝒪[k] := by simp [mem_latOf]

theorem mulVec_mem_latOf (h : GL Y k) {g : GL Y k} {y : Y → k} : h.val *ᵥ y ∈ latOf (h * g) ↔ y ∈ latOf g := by
  simp [mem_latOf, mulVec_mulVec, Matrix.mul_assoc]

def box (n : Type*) (c : kˣ) : Submodule 𝒪[k] (n → k) where
  carrier := {y | ∀ i, valuation k (y i) ≤ valuation k (c : k)}
  add_mem' := fun hy hz i => Valuation.map_add_le _ (hy i) (hz i)
  zero_mem' := fun i => by simp
  smul_mem' := fun x y hy i => by
    rw [show (x • y) i = (x : k) * y i from rfl, map_mul]
    exact mul_le_of_le_one_of_le x.2 (hy i)

theorem mem_box {n : Type*} {c : kˣ} {y : n → k} : y ∈ box n c ↔ ∀ i, valuation k (y i) ≤ valuation k (c : k) :=
  Iff.rfl

theorem box_one : box Y (1 : kˣ) = latOf 1 := by
  ext y; simp [mem_box, mem_latOf_one, Valuation.mem_integer_iff]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stabLat (g : GL Y k) : Subgroup (GL Y k) := (KO k Y).comap (MulAut.conj g⁻¹).toMonoidHom

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_stabLat {g h : GL Y k} : h ∈ stabLat g ↔ g⁻¹ * h * g ∈ KO k Y := by
  simp [stabLat, Subgroup.mem_comap]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem latOf_le_iff {g g' : GL Y k} : latOf g ≤ latOf g' ↔ IntM (g'⁻¹ * g).val := by
  constructor
  · intro h i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := h this i
    rwa [mulVec_mulVec, mulVec_single_one] at this
  · intro h y hy i
    have : (g'⁻¹).val *ᵥ y = (g'⁻¹ * g).val *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (h i l) (hy l)

theorem mem_stabLat_iff {g h : GL Y k} : h ∈ stabLat g ↔ latOf (h * g) = latOf g := by
  rw [mem_stabLat, mem_KO, le_antisymm_iff, latOf_le_iff, latOf_le_iff]
  simp [mul_assoc]

theorem isOpen_isCompact_conj (g : GL Y k) {J : Subgroup (GL Y k)} (ho : IsOpen (J : Set (GL Y k)))
    (hc : IsCompact (J : Set (GL Y k))) :
    IsOpen (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) ∧
      IsCompact (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) := by
  let e : GL Y k ≃ₜ GL Y k := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g⁻¹⁻¹)
  exact ⟨ho.preimage e.continuous, e.isCompact_preimage.2 hc⟩

theorem TypeDatum.map_conj (P : TypeDatum k ι) (F : LatFrame k ι Y) :
    IsOpen ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧ IsCompact ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧
      (P.toLevel.map F.conj).J ≤ stabLat F.bas := by
  have e : (P.toLevel.map F.conj).J = (P.reindex F.ord).J.comap (MulAut.conj F.bas⁻¹).toMonoidHom := by
    ext h; exact Iff.rfl
  rw [e]
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj F.bas (P.reindex F.ord).isOpen (P.reindex F.ord).isCompact
  exact ⟨h1, h2, Subgroup.comap_mono (P.reindex F.ord).le_KO⟩

end Frames

section StdFrames
variable {k : Type*} [Field k] {ι n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def typeFrame (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) :=
  ⟨ord, embA n (SplitFlip.diagGL fun i => ϖ ^ (i.val + 1))⟩

def plainFrame (ord : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) := ⟨ord, 1⟩

def normalBasis (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)

theorem normalBasis_val (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : (normalBasis ϖ e z).val =
    fromBlocks 1 (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp

theorem mem_latOf_typeFrame [ValuativeRel k] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (y : n ⊕ Fin c → k) :
    y ∈ latOf (typeFrame ϖ ord).bas ↔ (∀ i, y (.inl i) ∈ 𝒪[k]) ∧
      ∀ i : Fin c, valuation k (y (.inr i)) ≤ valuation k ((ϖ : k) ^ (i.val + 1)) := by
  have e : ((typeFrame ϖ ord).bas⁻¹).val = fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  rw [mem_latOf, e, Sum.forall, fromBlocks_mulVec]
  refine and_congr (by simp) (forall_congr' fun i => ?_)
  have : 0 < valuation k ((ϖ : k) ^ (i.val + 1)) := by simp [zero_lt_iff]
  simp only [zero_mulVec, zero_add, Sum.elim_inr, mulVec_diagonal, Valuation.mem_integer_iff, map_mul, map_inv₀,
    Function.comp]
  rw [inv_mul_le_one₀ this]

end StdFrames

abbrev XIx (κ t : Type*) (j : ℕ) : Type _ := (κ ⊕ Fin j) ⊕ (Fin j × t)

def stdOrd (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) : Ix (κ ⊕ Fin l) t j ≃ XIx κ t j ⊕ Fin c :=
  ((((Equiv.refl κ).sumCongr ((finCongr (by omega : l = c + j)).trans
      (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)))).trans (Equiv.sumAssoc _ _ _).symm).sumCongr
    (Equiv.refl _)).trans
  ((Equiv.sumAssoc _ _ _).trans (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

theorem stdOrd_eps (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : κ) :
    stdOrd κ t j c h (.inl (.inl i)) = .inl (.inl (.inl i)) := rfl

theorem standardOrderExtendedBasis_apply_low_block (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : Fin c) :
    stdOrd κ t j c h (.inl (.inr ⟨i.val, by omega⟩)) = .inr i := by
  have : finCongr (by omega : l = c + j) ⟨i.val, by omega⟩ = Fin.castAdd j i := rfl
  simp [stdOrd, this]

theorem stdOrd_f (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : Fin j) :
    stdOrd κ t j c h (.inl (.inr ⟨c + i.val, by omega⟩)) = .inl (.inl (.inr i)) := by
  have : finCongr (by omega : l = c + j) ⟨c + i.val, by omega⟩ = Fin.natAdd c i := rfl
  simp [stdOrd, this]

theorem stdOrd_d (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (p : Fin j × t) :
    stdOrd κ t j c h (.inr p) = .inl (.inr p) := rfl

section Groups
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def Cgrp (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) : Subgroup (GL (n ⊕ Fin c) k) :=
  R k n c 1 ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

theorem mem_Cgrp {J : Subgroup (GL (n ⊕ Fin c) k)} {h x : GL (n ⊕ Fin c) k} :
    x ∈ Cgrp J h ↔ x ∈ R k n c 1 ∧ h⁻¹ * x * h ∈ J := by
  simp [Cgrp, Subgroup.mem_comap]

def prX (C : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL n k) where
  carrier := {g | ∃ u ∈ N k n c 1, u * embX c g ∈ C}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro g g' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u * ((embX c g⁻¹)⁻¹ * u' * embX c g⁻¹), mul_mem hu (RootEx.Model.conj_mem hu' g⁻¹), ?_⟩
    convert C.mul_mem h h' using 1
    simp [mul_assoc]
  inv_mem' := by
    rintro g ⟨u, hu, h⟩
    refine ⟨(embX c g)⁻¹ * u⁻¹ * embX c g, RootEx.Model.conj_mem (inv_mem hu) g, ?_⟩
    convert C.inv_mem h using 1
    simp [mul_assoc]

theorem mem_prX {C : Subgroup (GL (n ⊕ Fin c) k)} {g : GL n k} :
    g ∈ prX C ↔ ∃ u ∈ N k n c 1, u * embX c g ∈ C := Iff.rfl

def IsColChar (ψ : AddChar k Circle) (P : Level (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (χ : prX (Cgrp P.J h) →* ℂˣ) : Prop :=
  ∀ (g : prX (Cgrp P.J h)), ∀ u ∈ N k n c 1, ∀ hm : h⁻¹ * (u * embX c (g : GL n k)) * h ∈ P.J,
    (χ g : ℂ) = (ψ (simpleSum u) : ℂ) * ((P.lam ⟨_, hm⟩)⁻¹ : ℂˣ)

theorem IsColChar.unique {ψ : AddChar k Circle} {P : Level (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    {χ χ' : prX (Cgrp P.J h) →* ℂˣ} (H : IsColChar ψ P h χ) (H' : IsColChar ψ P h χ') : χ = χ' := by
  ext g
  obtain ⟨u, hu, hc⟩ := g.2
  rw [H g u hu (mem_Cgrp.1 hc).2, H' g u hu (mem_Cgrp.1 hc).2]

end Groups

section Unfold
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
  (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)

def flat (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) : Matrix n n' k → ℂ := opE ψ ν 1 (om μ h' h Φ)

def idxAt (J : Subgroup (GL (n ⊕ Fin c) k)) (h' : GL (n' ⊕ Fin (c + 1)) k) :
    Set (DoubleCoset.Quotient (R k n c 1 : Set (GL (n ⊕ Fin c) k)) J) :=
  {β | ∃ h, DoubleCoset.mk (R k n c 1) J h = β ∧ flat ψ ν μ Φ h' h ≠ 0}

def volNat (b : GL (n ⊕ Fin c) k) (S : Subgroup (GL (n ⊕ Fin c) k)) : ℝ :=
  (volN ν n c 1 (S.subgroupOf (N k n c 1))).toReal / (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1))).toReal

def xi (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k)
    (h : GL (n ⊕ Fin c) k) : Matrix n n' k → ℂ := fun x₀ =>
  (((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ) * flat ψ ν μ Φ h' h x₀

omit [BorelSpace k] in

theorem xi_eq_zero {J : Subgroup (GL (n ⊕ Fin c) k)} (b : GL (n ⊕ Fin c) k) {h' : GL (n' ⊕ Fin (c + 1)) k}
    {h : GL (n ⊕ Fin c) k} (hh : DoubleCoset.mk (R k n c 1) J h ∉ idxAt ψ ν μ Φ J h') :
    xi ψ ν μ Φ J b h' h = 0 := by
  have : flat ψ ν μ Φ h' h = 0 := by_contra fun h0 => hh ⟨h, rfl, h0⟩
  funext x; simp [xi, this]

theorem volN_stabLat [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) :
    0 < (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1))).toReal := by
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj b SplitFlip.isOpen_KO SplitFlip.isCompact_KO
  obtain ⟨h3, h4⟩ := volN_ne_zero_ne_top ν 1 h1 h2
  exact ENNReal.toReal_pos h3 h4

theorem volNat_stabLat [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) : volNat ν b (stabLat b) = 1 :=
  div_self (volN_stabLat ν b).ne'

theorem volN_Cgrp [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k))) (h : GL (n ⊕ Fin c) k) :
    volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ 0 ∧ volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj h ho hc
  have e : (Cgrp J h).subgroupOf (N k n c 1) = (J.comap (MulAut.conj h⁻¹).toMonoidHom).subgroupOf (N k n c 1) := by
    ext u
    exact ⟨fun H => H.2, fun H => ⟨(le_sup_right : N k n c 1 ≤ R k n c 1) u.2, H⟩⟩
  rw [e]
  exact volN_ne_zero_ne_top ν 1 h1 h2

theorem volNat_Cgrp_pos [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)}
    (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k)))
    (b h : GL (n ⊕ Fin c) k) : 0 < volNat ν b (Cgrp J h) :=
  div_pos (ENNReal.toReal_pos (volN_Cgrp ν ho hc h).1 (volN_Cgrp ν ho hc h).2) (volN_stabLat ν b)

theorem xi_eq_zero_iff [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)}
    (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k)))
    (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    xi ψ ν μ Φ J b h' h = 0 ↔ flat ψ ν μ Φ h' h = 0 := by
  have := (volNat_Cgrp_pos ν ho hc b h).ne'
  simp [funext_iff, xi, this]

end Unfold

section Couple
variable {k : Type*} [Field k] {n n' : Type*}

def withCol (x₀ : Matrix n n' k) (y : n → k) : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k :=
  fromBlocks x₀ (Matrix.of fun r _ => y r) 0 0

theorem withCol_blocks (x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k) :
    withCol x.toBlocks₁₁ (fun r => x (.inl r) (.inr 0)) = x := by
  ext (r | r) (s | s)
  · rfl
  · rw [Subsingleton.elim (α := Fin 1) s 0]; rfl
  · exact r.elim0
  · exact r.elim0

variable [ValuativeRel k]

def cosetInd (M : Submodule 𝒪[k] (n → k)) (yb : (n → k) ⧸ M) : (n → k) → ℂ :=
  Set.indicator {y | Submodule.Quotient.mk y = yb} fun _ => 1

variable [Fintype n] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k)

omit [ValuativeRel k] in

def hat (f : (n → k) → ℂ) (η : n → k) : ℂ := ∫ y, f y * (ψ (ε * (η ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν)

omit [ValuativeRel k] in

def hatCol (Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) (x₀ : Matrix n n' k) (η : n → k) : ℂ :=
  hat ψ ν ε (fun y => Ψ (withCol x₀ y)) η

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]

theorem integrable_hat [ν.IsAddHaarMeasure] (hψ : Continuous ψ) {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (η : n → k) : Integrable (fun y => f y * (ψ (ε * (η ⬝ᵥ y)) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  refine Continuous.integrable_of_hasCompactSupport (hf.1.continuous.mul ?_) hf.2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))

omit [MeasurableSpace k] [BorelSpace k] in

theorem cosetInd_mem_SB (c : kˣ) (yb : (n → k) ⧸ box n c) : cosetInd (box n c) yb ∈ SB (n → k) := by
  have := t2Space k
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
  have e : {y : n → k | Submodule.Quotient.mk (p := box n c) y = Submodule.Quotient.mk y₀} =
      (Homeomorph.subRight y₀) ⁻¹' (Set.pi Set.univ fun _ => cball c) := by
    ext y; simp [Submodule.Quotient.eq, mem_box, cball]
  have ho : IsOpen (Set.pi Set.univ fun _ : n => cball c) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c
  have hc : IsCompact (Set.pi Set.univ fun _ : n => cball c) := isCompact_univ_pi fun _ => isCompact_cball c
  have hc' := (Homeomorph.subRight y₀).isCompact_preimage.2 hc
  unfold cosetInd
  rw [e]
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc'.isClosed, ho.preimage (Homeomorph.continuous _)⟩).isLocallyConstant,
    HasCompactSupport.intro hc' fun x hx => Set.indicator_of_notMem hx _⟩

example (hν : IsUnitVol ν) : hat ψ ν ε (cosetInd (box n 1) 0) 0 = 1 := by
  have := hν.1
  have := secondCountable k
  have e : {y : n → k | Submodule.Quotient.mk (p := box n 1) y = 0} = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext y; simp [mem_box, Valuation.mem_integer_iff]
  simp only [hat, cosetInd, e, zero_dotProduct, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_int k).measurableSet), Measure.real,
    Measure.pi_pi]
  simp [hν.2]

end Couple

section Chains

structure Chain (k : Type*) [Field k] (s : ℕ) (X : ℕ → Type*) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (Z : Type*) [Fintype Z] [DecidableEq Z] where

  lev : ∀ j c, j + c = s + 1 → Level (GL (X j ⊕ Fin c) k)

  bas : ∀ j c, j + c = s + 1 → GL (X j ⊕ Fin c) k

  levTop : Level (GL Z k)

  mu : ℕ → kˣ →* ℂˣ

  Phi : ∀ j c, j + c = s → Matrix (X (j + 1) ⊕ Fin c) (X j ⊕ Fin (c + 1)) k → ℂ

  PhiTop : Matrix Z (X (s + 1) ⊕ Fin 0) k → ℂ

abbrev RepFam (k : Type*) [Field k] (s : ℕ) (X : ℕ → Type*) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] :=
  ∀ j c, j + c = s → Set (GL (X j ⊕ Fin (c + 1)) k)

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]

def HasTypes {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (P' : Level (GL a k)) (P : Level (GL b k)) (Φ : Matrix b a k → ℂ) : Prop :=
  (∀ g : P'.J, om μ (g : GL a k) 1 Φ = (P'.lam g : ℂ) • Φ) ∧
    ∀ h : P.J, om μ 1 (h : GL b k) Φ = (((P.lam h)⁻¹ : ℂˣ) : ℂ) • Φ

namespace Chain
variable (T : Chain k s X Z)

def Laws : Prop :=
  (∀ j c (h : j + c = s), HasTypes (T.mu (j + 1)) (T.lev j (c + 1) (by omega)) (T.lev (j + 1) c (by omega))
    (T.Phi j c h)) ∧ HasTypes (T.mu (s + 2)) (T.lev (s + 1) 0 rfl) T.levTop T.PhiTop

def Regular : Prop :=
  (∀ j c h, T.Phi j c h ∈ SB _) ∧ T.PhiTop ∈ SB _ ∧
    ∀ j c h, IsOpen ((T.lev j c h).J : Set (GL (X j ⊕ Fin c) k)) ∧
      IsCompact ((T.lev j c h).J : Set (GL (X j ⊕ Fin c) k)) ∧ (T.lev j c h).J ≤ stabLat (T.bas j c h)

def Psi (h : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) : ℂ :=
  om (T.mu (s + 1)) h 1 (T.Phi s 0 rfl) (withCol x₀ y)

variable (A : RepFam k s X)

def RepsInStab : Prop := ∀ j c h, ∀ g ∈ A j c h, g ∈ stabLat (T.bas j (c + 1) (by omega))

def RepsMeet : Prop := ∀ j c h, ∀ g ∈ A j c h, ∀ y : X j → k,
  Sum.elim y 0 ∈ latOf (g * T.bas j (c + 1) (by omega)) ↔ ∀ i, y i ∈ 𝒪[k]

def RepsNormal (ϖ : kˣ) : Prop := ∀ j c h, ∀ g ∈ A j c h, ∃ (e : Fin (c + 1) → ℤ) (z : X j → k),
  (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)

def RepsOne : Prop := ∀ j c h, ∀ g ∈ A j c h,
  DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g =
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J 1 → g = 1

variable (S M : Submodule 𝒪[k] (X (s + 1) → k))

def Adapted : Prop := ∀ g ∈ A s 0 rfl, ∀ x₀ y,
  (T.Psi g x₀ y ≠ 0 → y ∈ S) ∧ ∀ z ∈ M, T.Psi g x₀ (y + z) = T.Psi g x₀ y

def coupIdx : Set ((X (s + 1) → k) ⧸ M) :=
  {yb | ∃ y ∈ S, Submodule.Quotient.mk y = yb ∧ ∃ g ∈ A s 0 rfl, ∃ x₀, T.Psi g x₀ y ≠ 0}

def xiPen (h : GL (X s ⊕ Fin (0 + 1)) k) (yb : (X (s + 1) → k) ⧸ M) : Matrix (X (s + 1)) (X s) k → ℂ :=
  fun x₀ => T.Psi h x₀ (Quotient.out yb)

variable {T A S M} in

theorem xiPen_mk (H : T.Adapted A S M) {g : GL (X s ⊕ Fin (0 + 1)) k} (hg : g ∈ A s 0 rfl) (y : X (s + 1) → k)
    (x₀ : Matrix (X (s + 1)) (X s) k) : T.xiPen M g (Submodule.Quotient.mk y) x₀ = T.Psi g x₀ y := by
  have h1 : Quotient.out (Submodule.Quotient.mk (p := M) y) - y ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq' _)
  rw [← (H g hg x₀ y).2 _ h1, add_sub_cancel]; rfl

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

def xiTop (ε : k) (yb : (X (s + 1) → k) ⧸ M) : Matrix (Z ⊕ Unit) (X (s + 1)) k → ℂ := fun x =>
  T.PhiTop (fromCols x.toRows₁ 0) * hat ψ ν ε (cosetInd M yb) (x (Sum.inr ()))

def idx (j c : ℕ) (h : j + 1 + c = s) (g : GL (X j ⊕ Fin (c + 1 + 1)) k) :
    Set (DoubleCoset.Quotient (R k (X (j + 1)) (c + 1) 1 : Set (GL (X (j + 1) ⊕ Fin (c + 1)) k))
      (T.lev (j + 1) (c + 1) (by omega)).J) :=
  idxAt ψ ν (T.mu (j + 1)) (T.Phi j (c + 1) (by omega)) (T.lev (j + 1) (c + 1) (by omega)).J g

def entry (j c : ℕ) (h : j + 1 + c = s) (g : GL (X j ⊕ Fin (c + 1 + 1)) k) (g' : GL (X (j + 1) ⊕ Fin (c + 1)) k) :
    Matrix (X (j + 1)) (X j) k → ℂ :=
  xi ψ ν (T.mu (j + 1)) (T.Phi j (c + 1) (by omega)) (T.lev (j + 1) (c + 1) (by omega)).J
    (T.bas (j + 1) (c + 1) (by omega)) g g'

structure IsRepSystem : Prop where
  zero : ∀ c h, A 0 c h = {1}
  bij : ∀ j c (h : j + 1 + c = s),
    Set.BijOn (DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (by omega)).J) (A (j + 1) c h)
      (⋃ g ∈ A j (c + 1) (by omega), T.idx ψ ν j c h g)

def someReps : RepFam k s X := fun j =>
  Nat.rec (motive := fun j => ∀ c, j + c = s → Set (GL (X j ⊕ Fin (c + 1)) k)) (fun _ _ => {1})
    (fun j B c h => Quotient.out '' ⋃ g ∈ B (c + 1) (by omega), T.idx ψ ν j c h g) j

omit [BorelSpace k] in
theorem isRepSystem_someReps : T.IsRepSystem (T.someReps ψ ν) ψ ν := by
  refine ⟨fun _ _ => rfl, fun j c h => ⟨?_, ?_, fun β hβ => ⟨_, ⟨β, hβ, rfl⟩, DoubleCoset.out_eq' _ _ β⟩⟩⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact (DoubleCoset.out_eq' _ _ β).symm ▸ hβ
  · rintro _ ⟨β, -, rfl⟩ _ ⟨β', -, rfl⟩ e
    exact congrArg _ ((DoubleCoset.out_eq' _ _ β).symm.trans (e.trans (DoubleCoset.out_eq' _ _ β')))

end Chain

variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

def Chain.ofType (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    Chain k s X Z where
  lev j c h := (P.iter t μ hμ j).toLevel.map (F j c h).conj
  bas j c h := (F j c h).bas
  levTop := (P.iter t μ hμ (s + 2)).toLevel.map Ftop.conj
  mu := μ
  Phi j c h := (F (j + 1) c (by omega)).transport (F j (c + 1) (by omega)) (P.iterPhi t μ hμ j)
  PhiTop := Ftop.transport (F (s + 1) 0 rfl) (P.iterPhi t μ hμ (s + 1))

def Chain.ofTwist (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ)
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    Chain k s X Z where
  lev j c h := (parahoric r (Fin j × t) δ hδ).toLevel.map (F j c h).conj
  bas j c h := (F j c h).bas
  levTop := (parahoric r (Fin (s + 2) × t) δ hδ).toLevel.map Ftop.conj
  mu j := ν j * δ
  Phi j c h := (F (j + 1) c (by omega)).transport (F j (c + 1) (by omega)) (parPhi δ)
  PhiTop := Ftop.transport (F (s + 1) 0 rfl) (parPhi δ)

theorem Chain.ofType_regular (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofType P μ hμ F Ftop).Regular :=
  ⟨fun _ _ _ => LatFrame.transport_mem_SB _ _ (P.iterPhi_mem_SB μ hμ _),
    LatFrame.transport_mem_SB _ _ (P.iterPhi_mem_SB μ hμ _), fun _ _ _ => TypeDatum.map_conj _ _⟩

theorem Chain.ofTwist_regular (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ)
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofTwist δ hδ ν F Ftop).Regular :=
  ⟨fun _ _ _ => LatFrame.transport_mem_SB _ _ (parPhi_mem_SB hδ),
    LatFrame.transport_mem_SB _ _ (parPhi_mem_SB hδ), fun _ _ _ => TypeDatum.map_conj _ _⟩

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable (t) in

def typeChain (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    Chain k s (XIx κ t) (Ix (κ ⊕ Fin (s + 1)) t (s + 2)) :=
  Chain.ofType P μ hμ (fun j c h => typeFrame ϖ (stdOrd κ t j c h)) (LatFrame.refl k _)

variable (κ t s) in

def twistChain (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ) :
    Chain k s (XIx κ t) (Ix (κ ⊕ Fin (s + 1)) t (s + 2)) :=
  Chain.ofTwist δ hδ ν (fun j c h => plainFrame (stdOrd κ t j c h)) (LatFrame.refl k _)

end Chains

section Laws
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]

theorem extZ_mul_right (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (g g' : J) :
    extZ J ρ ((g : GL a k).val * (g' : GL a k).val) = extZ J ρ (g : GL a k).val * ρ g' := by
  rw [extZ_coe, ← Units.val_mul, ← Subgroup.coe_mul, extZ_coe, map_mul, Units.val_mul]

theorem eq_mul_of_support {G S : Type*} [Group G] (act : G → S → S) (hact : ∀ g x, act g⁻¹ (act g x) = x)
    {f : S → ℂ} {c : G → ℂˣ} (h : ∀ g x, f x ≠ 0 → f (act g x) = c g * f x) (g : G) (x : S) :
    f (act g x) = c g * f x := by
  by_cases hx : f x = 0
  · by_contra hne
    have h1 : f (act g x) ≠ 0 := fun h0 => hne (by rw [h0, hx, mul_zero])
    have h2 := h g⁻¹ _ h1
    rw [hact, hx] at h2
    exact mul_ne_zero (Units.ne_zero _) h1 h2.symm
  · exact h g x hx

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_of_mem_KO (μ : kˣ →* ℂˣ) {g : GL a k} (hg : g ∈ KO k a) {h : GL b k}
    (hh : h ∈ KO k b) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) :
    om μ g h Φ x = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
      Φ ((h⁻¹).val * x * g.val) := by
  simp [om, nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hg),
    nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hh)]

namespace TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}

omit [Fintype t] [DecidableEq t] in
theorem Phi_mul_right (g : P.J) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ (x * (g : GL a k).val) = P.rho μ g * P.Phi t μ x := by
  refine eq_mul_of_support (G := P.J) (fun g x => x * (g : GL a k).val) (fun g x => by simp [Matrix.mul_assoc])
    (c := P.rho μ) (fun g x hx => ?_) g x
  obtain ⟨⟨g', hg', e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 hx
  rw [P.Phi_of_mem μ ⟨g', hg'⟩ e h2, P.Phi_of_mem μ (⟨g', hg'⟩ * g) (by rw [Subgroup.coe_mul, Units.val_mul, e]; rfl)
    (h2.mul_intM (intM_of_mem_KO (P.le_KO g.2))), ← Units.val_mul, ← Units.val_mul, ← rho_apply, ← rho_apply,
    map_mul, Units.val_mul, mul_comm]

theorem Phi_mul_left (hμ : IsTame μ) (h : P.stepJ t) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ ((h : GL (a ⊕ t) k).val * x) = P.rho μ (P.corner h) * P.Phi t μ x := by
  refine eq_mul_of_support (G := P.stepJ t) (fun g x => (g : GL (a ⊕ t) k).val * x)
    (fun g x => by simp [← Matrix.mul_assoc]) (c := fun h => P.rho μ (P.corner h)) (fun h x hx => ?_) h x
  obtain ⟨⟨g', hg', e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 hx
  obtain ⟨-, -, hB, hC, D, hD, eD⟩ := h.2
  have e0 : (h : GL (a ⊕ t) k).val * x = fromRows ((P.corner h : GL a k).val * g'.val) 0 +
      fromRows ((h : GL (a ⊕ t) k).val.toBlocks₁₂ * x.toRows₂)
        ((h : GL (a ⊕ t) k).val.toBlocks₂₁ * g'.val + D.val * x.toRows₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks (h : GL (a ⊕ t) k).val, ← fromRows_toRows x, fromBlocks_mul_fromRows]
    rw [corner_val, e, eD]
    ext (i | i) j <;> simp
  rw [e0, P.Phi_add hμ, P.Phi_of_mem μ ⟨g', hg'⟩ e h2, P.Phi_of_mem μ (P.corner h * ⟨g', hg'⟩) (by simp)
    (by simpa using maxM_zero), ← Units.val_mul, ← Units.val_mul, ← rho_apply, ← rho_apply, map_mul, Units.val_mul]
  rintro (i | i) j
  · exact hB.mul_maxM h2 i j
  · exact (hC.mul_intM (intM_of_mem_KO (P.le_KO hg'))).add ((intM_of_mem_KO hD).mul_maxM h2) i j

theorem hasTypes_Phi (hμ : IsTame μ) : HasTypes μ P.toLevel (P.step t μ hμ).toLevel (P.Phi t μ) := by
  refine ⟨fun g => funext fun x => ?_, fun h => funext fun x => ?_⟩
  · rw [om_of_mem_KO μ (P.le_KO g.2) (one_mem _), inv_one, Units.val_one, Matrix.one_mul, Phi_mul_right, rho_apply]
    simp; field_simp
  · rw [om_of_mem_KO μ (one_mem _) h.2.1, Units.val_one, Matrix.mul_one, ← map_inv (P.step t μ hμ).lam]
    erw [P.step_lam μ hμ h⁻¹ _ (P.corner_val _), ← rho_apply, P.Phi_mul_left hμ h⁻¹ x]
    rw [show ((h⁻¹ : P.stepJ t) : GL (a ⊕ t) k) = (h : GL (a ⊕ t) k)⁻¹ from rfl]
    simp; ring

end TypeDatum

section
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}

omit [Fintype s] [DecidableEq s] in
theorem parPhi_mul_right (hδ : IsTame δ) (g : (TypeDatum.full k r).stepJ s') (x : Matrix (r ⊕ s) (r ⊕ s') k) :
    parPhi δ (x * (g : GL (r ⊕ s') k).val) =
      (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g) * parPhi δ x := by
  refine eq_mul_of_support (G := (TypeDatum.full k r).stepJ s') (fun g x => x * (g : GL (r ⊕ s') k).val)
    (fun g x => by simp [Matrix.mul_assoc]) (c := fun g => (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g))
    (fun g x hx => ?_) g x
  obtain ⟨⟨u, hu, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
  obtain ⟨-, -, hB, hC, D, hD, eD⟩ := g.2
  set A := (TypeDatum.full k r).corner g
  have hA := intM_of_mem_KO A.2
  have eA : (A : GL r k).val = _ := TypeDatum.corner_val _ g
  obtain ⟨w, hw, ew⟩ := exists_mul_KOne (mul_mem hu A.2)
    (M := u.val * (A : GL r k).val + x.toBlocks₁₂ * (g : GL (r ⊕ s') k).val.toBlocks₂₁)
    (by simpa using h12.mul_maxM hC)
  rw [parPhi_of_mem δ hu e h21 h12 h22, ← fromBlocks_toBlocks x, ← fromBlocks_toBlocks (g : GL (r ⊕ s') k).val,
    fromBlocks_multiply, ← e, ← eA, ← eD,
    parPhi_fromBlocks δ (mul_mem (mul_mem hu A.2) (KOne_le_KO hw)) ew ((h21.mul_intM hA).add (h22.mul_maxM hC))
      (((intM_of_mem_KO hu).mul hB).add (h12.mul (intM_of_mem_KO hD)))
      ((h21.intM.mul hB).add (h22.mul (intM_of_mem_KO hD))),
    map_mul, map_mul, map_mul, map_mul, tame_det_of_mem_KOne hδ hw, TypeDatum.rho_apply]
  change _ = ((1 * _ : ℂˣ) : ℂ) * _
  simp

omit [Fintype s'] [DecidableEq s'] in
theorem parPhi_mul_left (hδ : IsTame δ) (g : (TypeDatum.full k r).stepJ s) (x : Matrix (r ⊕ s) (r ⊕ s') k) :
    parPhi δ ((g : GL (r ⊕ s) k).val * x) =
      (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g) * parPhi δ x := by
  refine eq_mul_of_support (G := (TypeDatum.full k r).stepJ s) (fun g x => (g : GL (r ⊕ s) k).val * x)
    (fun g x => by simp [← Matrix.mul_assoc])
    (c := fun g => (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g)) (fun g x hx => ?_) g x
  obtain ⟨⟨u, hu, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
  obtain ⟨-, -, hB, hC, D, hD, eD⟩ := g.2
  set A := (TypeDatum.full k r).corner g
  have hA := intM_of_mem_KO A.2
  have eA : (A : GL r k).val = _ := TypeDatum.corner_val _ g
  obtain ⟨w, hw, ew⟩ := exists_mul_KOne (mul_mem A.2 hu)
    (M := (A : GL r k).val * u.val + (g : GL (r ⊕ s) k).val.toBlocks₁₂ * x.toBlocks₂₁)
    (by simpa using hB.mul_maxM h21)
  rw [parPhi_of_mem δ hu e h21 h12 h22, ← fromBlocks_toBlocks x, ← fromBlocks_toBlocks (g : GL (r ⊕ s) k).val,
    fromBlocks_multiply, ← e, ← eA, ← eD,
    parPhi_fromBlocks δ (mul_mem (mul_mem A.2 hu) (KOne_le_KO hw)) ew
      ((hC.mul_intM (intM_of_mem_KO hu)).add ((intM_of_mem_KO hD).mul_maxM h21))
      ((hA.mul h12).add (hB.mul h22)) ((hC.intM.mul h12).add ((intM_of_mem_KO hD).mul h22)),
    map_mul, map_mul, map_mul, map_mul, tame_det_of_mem_KOne hδ hw, TypeDatum.rho_apply]
  change _ = ((1 * _ : ℂˣ) : ℂ) * _
  simp [mul_comm]

theorem hasTypes_parPhi (hδ : IsTame δ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) :
    HasTypes (ν * δ) (parahoric r s' δ hδ).toLevel (parahoric r s δ hδ).toLevel (parPhi δ) := by
  refine ⟨fun g => funext fun x => ?_, fun h => funext fun x => ?_⟩
  · rw [om_of_mem_KO _ g.2.1 (one_mem _), inv_one, Units.val_one, Matrix.one_mul]
    erw [parPhi_mul_right hδ g x, (TypeDatum.full k r).step_lam δ hδ g _ (TypeDatum.corner_val _ _),
      ← TypeDatum.rho_apply]
    simp [hν _ (valuation_det_of_mem_KO g.2.1)]; ring
  · rw [om_of_mem_KO _ (one_mem _) h.2.1, Units.val_one, Matrix.mul_one, ← map_inv (parahoric r s δ hδ).lam]
    erw [(TypeDatum.full k r).step_lam δ hδ h⁻¹ _ (TypeDatum.corner_val _ _), ← TypeDatum.rho_apply,
      parPhi_mul_left hδ h⁻¹ x]
    rw [show ((h⁻¹ : (TypeDatum.full k r).stepJ s) : GL (r ⊕ s) k) = (h : GL (r ⊕ s) k)⁻¹ from rfl]
    simp [hν _ (valuation_det_of_mem_KO h.2.1)]; ring

end

theorem HasTypes.transport {Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {μ : kˣ →* ℂˣ}
    {P' : Level (GL a k)} {P : Level (GL b k)} {Φ : Matrix b a k → ℂ} (H : HasTypes μ P' P Φ)
    (F : LatFrame k b Y) (F' : LatFrame k a Y') :
    HasTypes μ (P'.map F'.conj) (P.map F.conj) (F.transport F' Φ) := by
  refine ⟨fun g => ?_, fun h => ?_⟩
  · have := F.om_transport F' μ (F'.conj.symm g) 1 Φ
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact this.trans (congrArg (F.transport F') (H.1 ⟨_, g.2⟩))
  · have := F.om_transport F' μ 1 (F.conj.symm h) Φ
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact this.trans (congrArg (F.transport F') (H.2 ⟨_, h.2⟩))

theorem TypeDatum.hasTypes_iterPhi {r : Type*} [Fintype r] [DecidableEq r] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    HasTypes (μ (j + 1)) (P.iter t μ hμ j).toLevel (P.iter t μ hμ (j + 1)).toLevel (P.iterPhi t μ hμ j) := by
  have H := (P.iter t μ hμ j).hasTypes_Phi (t := t) (hμ (j + 1))
  have key : ∀ g h, om (μ (j + 1)) g (reGL (ixSucc r t j) h) (P.iterPhi t μ hμ j) =
      fun x => om (μ (j + 1)) g h ((P.iter t μ hμ j).Phi t (μ (j + 1))) (x.submatrix (ixSucc r t j) id) := by
    intro g h
    funext x
    simp only [om, TypeDatum.iterPhi, det_reGL, ← Fintype.card_congr (ixSucc r t j), ← map_inv (reGL _), reGL_val]
    congr 2
    rw [← submatrix_mul_equiv _ _ _ (Equiv.refl _), ← submatrix_mul_equiv _ _ _ (ixSucc r t j)]
    simp
  refine ⟨fun g => ?_, fun h => ?_⟩
  · have := key g 1
    rw [map_one, H.1 g] at this
    exact this
  · have := key 1 ((reGL (ixSucc r t j)).symm h)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.trans (funext fun x => congrFun (H.2 ⟨_, h.2⟩) _)

variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  {r : Type*} [Fintype r] [DecidableEq r]

theorem Chain.ofType_laws (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofType P μ hμ F Ftop).Laws :=
  ⟨fun j _ _ => (P.hasTypes_iterPhi μ hμ j).transport _ _, (P.hasTypes_iterPhi μ hμ (s + 1)).transport _ _⟩

theorem Chain.ofTwist_laws (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν : ℕ → kˣ →* ℂˣ) (hν : ∀ j, IsUnram (ν j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofTwist δ hδ ν F Ftop).Laws :=
  ⟨fun _ _ _ => (hasTypes_parPhi hδ (hν _)).transport _ _, (hasTypes_parPhi hδ (hν _)).transport _ _⟩

end Laws

section Nonempty
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] in
theorem exists_affPt {p : ℕ} {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (h : ∀ r s, ¬ Free p (r, s) → x r s = basePt c x.toBlocks₁₁ r s) : ∃ e, affPt p x.toBlocks₁₁ e = x := by
  refine ⟨fun rs => x rs.1.1 rs.1.2 - basePt c x.toBlocks₁₁ rs.1.1 rs.1.2, ?_⟩
  ext r s
  by_cases hf : Free p (r, s) <;> simp [affPt, hf, h]

omit [DecidableEq n] [DecidableEq n'] in

theorem opE_ne_zero [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = 1 ∧ IntM x) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by
  classical
  have := secondCountable k
  have := t2Space k
  have hc : Continuous (affPt (c := c) p x₀) := by
    refine continuous_const.add (continuous_pi fun r => continuous_pi fun s => ?_)
    by_cases hf : Free p (r, s)
    · simp only [Matrix.of_apply, dif_pos hf]; exact continuous_apply _
    · simp only [Matrix.of_apply, dif_neg hf]; exact continuous_const
  have key : ∀ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) = (‖Φ (affPt p x₀ e)‖ : ℝ) := fun e => by
    by_cases h : Φ (affPt p x₀ e) = 0
    · simp [h]
    · obtain ⟨h1, h2⟩ := h01 _ h
      have hi : -ch (affPt p x₀ e) ∈ 𝒪[k] := neg_mem (sum_mem fun i _ => h2 _ _)
      rw [h1, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]; simp
  unfold opE
  simp only [key]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hΦ.1.continuous.comp hc).norm ?_
    (fun _ => norm_nonneg _) (x := e₀) (norm_ne_zero_iff.2 he)).ne'
  refine HasCompactSupport.intro (isCompact_univ_pi fun rs => (isCompact_int k).image
    (continuous_sub_right (basePt c x₀ rs.1.1 rs.1.2))) fun e he' => norm_eq_zero.2 (by_contra fun h => he' ?_)
  rintro ⟨⟨r, s⟩, hf⟩ -
  exact ⟨_, (h01 _ h).2 r s, by simp [affPt, hf]⟩

theorem twistChain_entry_ne_zero [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    (ν : Measure k) [ν.IsAddHaarMeasure] (κ t : Type*) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
    (s c : ℕ) (h : 0 + 1 + c = s) :
    DoubleCoset.mk _ _ 1 ∈ (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).idx ψ ν 0 c h 1 ∧
      (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).entry ψ ν 0 c h 1 1 ≠ 0 := by
  set T := twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1
  have hT : T.Regular := Chain.ofTwist_regular _ _ _ _ _
  let o := stdOrd κ t (l := s + 1) (0 + 1) (c + 1) (by omega)
  let o' := stdOrd κ t (l := s + 1) 0 (c + 1 + 1) (by omega)
  have hP : ∀ x, T.Phi 0 (c + 1) (by omega) x = parPhi 1 (x.submatrix o o') := fun x => by
    change parPhi 1 ((plainFrame o).coords (plainFrame o') x) = _
    simp [plainFrame, LatFrame.coords]
  let x : Matrix _ _ k := (fromBlocks (1 : Matrix _ _ k) 0 0 0).submatrix o.symm o'.symm
  have a1 : ∀ i, o.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a2 : ∀ i, o'.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o'.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a3 : ∀ i, o.symm (.inl (.inl (.inr i))) = .inl (.inr ⟨c + 1 + i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (stdOrd_f κ t _ _ _ i).symm
  have a4 : ∀ i, o.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o.symm_apply_eq.2 rfl
  have a5 : ∀ i, o'.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o'.symm_apply_eq.2 rfl
  have a6 : ∀ i, o.symm (.inl (.inr i)) = .inr i := fun i => o.symm_apply_eq.2 rfl
  obtain ⟨e, he⟩ := exists_affPt (p := 1) (x := x) (by
    rintro (r | r) (i | i) hf
    · rfl
    · have hi : i.val = 0 := by simp only [Free] at hf; omega
      rcases r with (r | r) | r
      · simp [x, basePt, a2, a4]
      · simp [x, basePt, a2, a3, hi]
      · simp [x, basePt, a2, a6]
    · rcases i with (i | i) | i
      · simp [x, basePt, a1, a5]
      · exact i.elim0
      · exact i.1.elim0
    · simp [x, basePt, a1, a2, Matrix.one_apply])
  have hflat : flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) (by omega)) 1 1 ≠ 0 := by
    rw [flat, om_one]
    refine fun h0 => opE_ne_zero hψ ν 1 (hT.1 0 (c + 1) (by omega)) (fun y hy => ?_) (e₀ := e) ?_
      (congrFun h0 x.toBlocks₁₁)
    · rw [hP] at hy ⊢
      obtain ⟨⟨g, hg, eg⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff 1).1 hy
      refine ⟨by rw [parPhi_of_mem 1 hg eg h21 h12 h22]; simp, fun i j => ?_⟩
      have : IntM (y.submatrix o o') := by
        rw [← fromBlocks_toBlocks (y.submatrix o o'), ← eg]
        exact intM_fromBlocks.2 ⟨intM_of_mem_KO hg, h12, h21.intM, h22⟩
      simpa using this (o.symm i) (o'.symm j)
    · rw [he, hP]
      simp only [x, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
      rw [parPhi_fromBlocks 1 (one_mem _) Units.val_one maxM_zero intM_zero intM_zero]
      exact Units.ne_zero _
  exact ⟨⟨1, rfl, hflat⟩, fun h0 => hflat ((xi_eq_zero_iff ψ ν _ _ (hT.2.2 _ _ _).1 (hT.2.2 _ _ _).2.1 _ _ _).1 h0)⟩

end Nonempty

end GlobalTheory.StepData
