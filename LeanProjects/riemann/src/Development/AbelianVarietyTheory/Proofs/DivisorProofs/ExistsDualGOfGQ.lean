import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSwap

section Alg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def invT : GL n A →* GL n A where
  toFun g := ⟨((g⁻¹ : GL n A) : Matrix n n A)ᵀ, (g : Matrix n n A)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transpose_mul])

theorem invT_val (g : GL n A) : ((invT g : GL n A) : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A)ᵀ := rfl

theorem invT_inv_val (g : GL n A) : (((invT g)⁻¹ : GL n A) : Matrix n n A) = (g : Matrix n n A)ᵀ := rfl

theorem invT_invT (g : GL n A) : invT (invT g) = g := Units.ext rfl

theorem bc_invT {B : Type} [CommRing B] (φ : A →+* B) (g : GL n A) :
    Formalism.UG.bc φ (invT g) = invT (Formalism.UG.bc φ g) := Units.ext rfl

theorem continuous_invT [TopologicalSpace A] : Continuous (invT : GL n A → GL n A) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_mem (σ : A →+* A) {J J' : Matrix n n A} (h : J'ᵀ * J = 1) {g : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J') : invT g ∈ Formalism.UG.UJ σ J := by
  have h' : J * J'ᵀ = 1 := mul_eq_one_comm.1 h
  have hg' : (g : Matrix n n A)ᵀ * J'ᵀ * (g : Matrix n n A).map σ = J'ᵀ := by
    have := congrArg Matrix.transpose (show Formalism.UG.cT σ (g : Matrix n n A) * J' * (g : Matrix n n A) = J' from hg)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  show ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ = J
  have e1 : ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ = 1 := (invT g).val_inv
  have e2 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * (g : Matrix n n A).map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have e3 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ = 1 := by
    rw [← hg']
    calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * (J * (((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ) * J'ᵀ) *
          (g : Matrix n n A).map σ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, h', Matrix.mul_one, e2]
  calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ * J := by
        rw [Matrix.mul_assoc _ J'ᵀ, h, Matrix.mul_one]
    _ = J := by rw [e3, Matrix.one_mul]

end Alg

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def formLat (G : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∃ x ∈ Λ, y = star x ᵥ* G}
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Λ.add_mem hx hy, by rw [star_add, Matrix.add_vecMul]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨(⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) • x, Λ.smul_mem _ hx, ?_⟩
    change (c : E) • (star x ᵥ* G) = star (star (c : E) • x) ᵥ* G
    rw [star_smul, star_star, Matrix.smul_vecMul]

theorem formLat_isLattice {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : Submodule.IsLattice E Λ) : Submodule.IsLattice E (formLat G Λ) where
  fg := by
    obtain ⟨s, hs⟩ := h.fg
    classical
    refine ⟨s.image fun x => star x ᵥ* G, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨x, hs ▸ Submodule.subset_span hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
      | zero => simp
      | add x y _ _ hx hy => rw [star_add, Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have := Submodule.smul_mem _ (⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) hx
        change star ((c : E) • x) ᵥ* G ∈ _
        rw [star_smul, Matrix.smul_vecMul]
        exact this
  span_eq_top := by
    rw [eq_top_iff]
    intro y _
    have hy : y = star (star (y ᵥ* G⁻¹)) ᵥ* G := by
      rw [star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
    have hx : star (y ᵥ* G⁻¹) ∈ Submodule.span E (Λ : Set (Fin n → E)) := h.span_eq_top ▸ Submodule.mem_top
    rw [hy]
    generalize star (y ᵥ* G⁻¹) = x at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add, Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [star_smul, Matrix.smul_vecMul]
      exact Submodule.smul_mem _ _ hx

theorem form_dual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) (x y : Fin n → E) :
    ∑ i, ∑ j, star ((star x ᵥ* G) i) * G⁻¹ᵀ i j * (star y ᵥ* G) j = star (∑ i, ∑ j, star (x i) * G i j * y j) := by
  have h1 : ∀ (M : Matrix (Fin n) (Fin n) E) (a b : Fin n → E), ∑ i, ∑ j, star (a i) * M i j * b j = star a ⬝ᵥ (M *ᵥ b) := by
    intro M a b
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, h1, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one,
    Matrix.star_vecMul, star_star, hh, ← star_dotProduct_star, star_star, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hh]

theorem formLat_selfDual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) (y : Fin n → E) :
    y ∈ formLat G Λ ↔ ∀ x ∈ formLat G Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G⁻¹ᵀ i j * y j := by
  have hy : y = star (star (y ᵥ* G⁻¹)) ᵥ* G := by
    rw [star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := (h z).1 hz x hx
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by rw [form_dual hG hh, ← hb]; rfl⟩
  · intro H
    refine ⟨_, (h _).2 fun x hx => ?_, hy⟩
    obtain ⟨b, hb⟩ := H _ ⟨x, hx, rfl⟩
    rw [hy, form_dual hG hh] at hb
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by
      change star (b : E) = _
      rw [hb, star_star]⟩

theorem toLin_apply (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) M x y = ∑ i, ∑ j, star (x i) * M i j * y j := by
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]

end Lat

variable {D : D7}

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i

theorem gramInvT_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ᵀ i j) = S.gram⁻¹ᵀ j i := by
  have : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  exact congrFun (congrFun this i) j

@[reducible] def dualSp (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ) : HSp D where
  V := Fin S.rank → D.host.E
  hT := Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
  herm := ⟨fun x y => by
    rw [toLin_apply, toLin_apply, starRingEnd_apply, star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_mul', star_star, gramInvT_star]; ring⟩
  nondeg := by
    have hd := GlobalTheory.LatVac.gram_det_isUnit S
    constructor
    · intro x hx
      have h1 : star x ᵥ* S.gram⁻¹ᵀ = 0 := by
        funext j
        have := hx (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.vecMul, dotProduct] using this
      have h2 := congrArg (· ᵥ* S.gramᵀ) h1
      simp only [Matrix.vecMul_vecMul, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
        Matrix.vecMul_one, Matrix.zero_vecMul] at h2
      exact star_eq_zero.1 h2
    · intro y hy
      have h1 : S.gram⁻¹ᵀ *ᵥ y = 0 := by
        funext j
        have := hy (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.mulVec, dotProduct, apply_ite] using this
      have h2 := congrArg (S.gramᵀ *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.transpose_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      exact h2
  rank := S.rank
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := S.sig
  L0 := formLat S.gram Λ
  standardTuple_isLattice := formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1
  baseLattice_isUnimodular := by
    ext y
    rw [formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
      LinearMap.restrictScalars_apply, toLin_apply]

variable (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ)

theorem dualSp_gram : (dualSp S Λ hΛ).gram = S.gram⁻¹ᵀ := by
  refine Matrix.ext fun i j => ?_
  change Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
    (Pi.basisFun _ _ i) (Pi.basisFun _ _ j) = _
  rw [toLin_apply]
  simp [Pi.single_apply, apply_ite]

theorem dualSp_selfDual : IsSelfDualC (dualSp S Λ hΛ) (formLat S.gram Λ) := by
  refine ⟨formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1, fun y => ?_⟩
  rw [dualSp_gram]
  exact formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2 y

theorem gram_dual_mul : (dualSp S Λ hΛ).gramᵀ * S.gram = 1 := by
  rw [dualSp_gram, Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]

theorem gram_mul_dual : S.gramᵀ * (dualSp S Λ hΛ).gram = 1 := by
  rw [dualSp_gram, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.transpose_one]

theorem dualSp_gram_inv : (dualSp S Λ hΛ).gram⁻¹ = S.gramᵀ := Matrix.inv_eq_left_inv (gram_mul_dual S Λ hΛ)

def dualG : GA D (dualSp S Λ hΛ) →* GA D S :=
  (invT.comp (matHom (dualSp S Λ hΛ))).codRestrict (HR (AF D.host.F) D.sp.cm.sig S.gram) fun g =>
    invT_mem _ (J' := JR (AF D.host.F) (dualSp S Λ hΛ).gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]) g.2

theorem matHom_dualG (g : GA D (dualSp S Λ hΛ)) : matHom S (dualG S Λ hΛ g) = invT (matHom (dualSp S Λ hΛ) g) := rfl

theorem mt_dualG (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g) = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g⁻¹)ᵀ := rfl

theorem mt_dualG_inv (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g)⁻¹ = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g)ᵀ := rfl

theorem continuous_dualG : Continuous (dualG S Λ hΛ) :=
  (continuous_invT.comp continuous_subtype_val).subtype_mk _

theorem dualG_mem_GfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GfC S := by
  have h : infHom S (dualG S Λ hΛ g) = invT (infHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem dualG_mem_GinfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GinfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GinfC S := by
  have h : finHom S (dualG S Λ hΛ g) = invT (finHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GinfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem exists_dualG_of_GQ {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ γ' ∈ GQ (dualSp S Λ hΛ), dualG S Λ hΛ γ' = γ := by
  have hγ' : matHom S γ ∈ HFin (AF D.host.F) D.sp.cm.sig S.gram := hγ
  obtain ⟨g, hg, hgγ⟩ := hγ'
  have h1 : invT (matHom S γ) ∈ HR (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    invT_mem _ (J' := JR (AF D.host.F) S.gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_mul_dual,
        Matrix.map_one _ (map_zero _) (map_one _)]) γ.2
  have h2 : invT (matHom S γ) ∈ HFin (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    ⟨invT g, invT_mem _ (gram_mul_dual S Λ hΛ) hg, by rw [bc_invT, hgγ]⟩
  refine ⟨⟨invT (matHom S γ), h1⟩, h2, Subtype.ext ?_⟩
  exact invT_invT (matHom S γ)

end GlobalTheory.DualSwap

end
