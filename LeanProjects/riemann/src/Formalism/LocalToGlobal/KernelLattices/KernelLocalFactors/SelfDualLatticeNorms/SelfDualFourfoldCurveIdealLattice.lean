import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS.MM

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.Th1.GD (LocNorm)

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

theorem locNorm_of_kappa (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hg₀ : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, cmTheta b₀ dK • x ∈ Λ)
    (i1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0)
    (κ : ℂ) (θ : (n → ℂ) → ℂ)
    (hθ : tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hκ : ∀ u : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
      IsIsom (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
        (u : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
      relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (u : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) ≠ 0 →
      ¬ p ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (u : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) →
      relIdx (imgLat (u : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 →
      ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))‖ = 1) :
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι := by
  have hsda := CmData.selfDual_img _ _ g₀ hg₀ _ (CmData.isSelfDual_matH_blk4_pow4 h Λ hsd)
  have hsta : ∀ x ∈ imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ),
      cmTheta b₀ dK • x ∈ imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ dK • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ dK ha hdK lam hlam hcm (Fin 4 × n) _ hsda hsta i1 i2
    p Fact.out
  have hκu := hκ u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      ((g₀.trans u : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
    intro x y
    have h1 := huiso (g₀ x) (g₀ y)
    have h0 := hg₀ x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₀ hg₀ hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ (g₀.trans u) hg₁ hsd hst j1 j2
  have hcomp : g₀.symm.trans (g₀.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (g₀.trans u) x = g₀ x → x = 0 := by
    intro x hx
    have h1 : g₀ x = 0 := hufix _ hx
    simpa using congrArg g₀.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ n h Λ _ _ g₀ (g₀.trans u) D0 D1 hfix
  exact ⟨g₀.trans u, κ * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι κ c _ hc8 hκu).le, by rw [hθ, hc, smul_smul]⟩

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

theorem locNormMM_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀)
    (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d) (hB : B.IsCm a₀ b₀ ha hd lam hlam)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hK : B.KappaAt p ι) : B.LocNormMM a₀ b₀ ha hd lam hlam p ι := by
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := (B.thMM_spec (B.stdOK hcc hδ)).2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  unfold Base.LocNormMM
  rw [hω] at h2
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  exact locNorm_of_kappa a₀ b₀ c₀ D.host.d ha hd lam hlam hcm _ _ B.gC iso hsd hst i1 i2 B.kappa B.thMM h2 p ι hK

end Base

section Transport

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mem_imgLat (R : V ≃ₗ[ℂ] W) (Λ : AddSubgroup V) (y : W) : y ∈ imgLat (R : V →ₗ[ℂ] W) Λ ↔ R.symm y ∈ Λ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : R.symm (R x) = x := R.symm_apply_apply x
    show R.symm (R x) ∈ Λ
    rw [this]
    exact hx
  · intro hy
    exact ⟨R.symm y, hy, R.apply_symm_apply y⟩

theorem apply_mem_imgLat (R : V ≃ₗ[ℂ] W) (Λ : AddSubgroup V) (x : V) : R x ∈ imgLat (R : V →ₗ[ℂ] W) Λ ↔ x ∈ Λ := by
  rw [mem_imgLat, R.symm_apply_apply]

theorem opU_map (H : Sesq V) (H' : Sesq W) (R : V ≃ₗ[ℂ] W) (hR : IsIsom H H' (R : V →ₗ[ℂ] W)) (F : V → ℂ) (F' : W → ℂ)
    (hF : ∀ x, F' (R x) = F x) (x z : V) : opU H' (R x) F' (R z) = opU H x F z := by
  have h1 : H' (R z) (R x) = H z x := hR z x
  have h2 : H' (R x) (R x) = H x x := hR x x
  unfold opU
  rw [← map_add, hF, h1, h2]

theorem isReps_map (R : V ≃ₗ[ℂ] W) {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (h : IsReps Λ₁ Λ₂ S) :
    IsReps (imgLat (R : V →ₗ[ℂ] W) Λ₁) (imgLat (R : V →ₗ[ℂ] W) Λ₂) (S.map R.toEquiv.toEmbedding) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    exact (apply_mem_imgLat R _ y).2 (h.1 y hy)
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    have h1 : R (x' - y') ∈ imgLat (R : V →ₗ[ℂ] W) Λ₁ := by
      rw [map_sub]
      exact hxy
    rw [h.2.1 x' hx' y' hy' ((apply_mem_imgLat R _ _).1 h1)]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := h.2.2 (R.symm y) ((mem_imgLat R _ y).1 hy)
    refine ⟨R x, Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    rw [mem_imgLat, map_sub, R.symm_apply_apply]
    exact hxy

theorem relIdx_map (R : V ≃ₗ[ℂ] W) (Λ₁ Λ₂ : AddSubgroup V) :
    relIdx (imgLat (R : V →ₗ[ℂ] W) Λ₁) (imgLat (R : V →ₗ[ℂ] W) Λ₂) = relIdx Λ₁ Λ₂ :=
  AddSubgroup.relIndex_map_map_of_injective Λ₁ Λ₂ (f := (R : V →ₗ[ℂ] W).toAddMonoidHom) R.injective

theorem semiChar_map (H : Sesq V) (H' : Sesq W) (R : V ≃ₗ[ℂ] W) (hR : IsIsom H H' (R : V →ₗ[ℂ] W)) (Λ : AddSubgroup V)
    (α : V → ℂ) (α' : W → ℂ) (hα : ∀ x, α' (R x) = α x) (h : IsSemiChar H Λ α) :
    IsSemiChar H' (imgLat (R : V →ₗ[ℂ] W) Λ) α' := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show α' (R x) = 1 ∨ α' (R x) = -1
    rw [hα]
    exact h.1 x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show α' (R x + R y) = α' (R x) * α' (R y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H' (R x) (R y) : ℂ))
    have h1 : altE H' (R x) (R y) = altE H x y := by
      unfold altE
      rw [show H' (R x) (R y) = H x y from hR x y]
    rw [← map_add, hα, hα, hα, h1]
    exact h.2 x hx y hy

theorem fixedBy_map (H : Sesq V) (H' : Sesq W) (R : V ≃ₗ[ℂ] W) (hR : IsIsom H H' (R : V →ₗ[ℂ] W)) (Λ : AddSubgroup V)
    (α : V → ℂ) (α' : W → ℂ) (hα : ∀ x, α' (R x) = α x) (F : V → ℂ) (F' : W → ℂ) (hF : ∀ x, F' (R x) = F x)
    (h : F ∈ fixedBy H α Λ) : F' ∈ fixedBy H' α' (imgLat (R : V →ₗ[ℂ] W) Λ) := by
  rintro _ ⟨x, hx, rfl⟩ z
  obtain ⟨z, rfl⟩ := R.surjective z
  show α' (R x) * opU H' (R x) F' (R z) = F' (R z)
  rw [hα, opU_map H H' R hR F F' hF, hF]
  exact h x hx z

theorem inter_map (H : Sesq V) (H' : Sesq W) (hH : IsHerm H) (hH' : IsHerm H') (R : V ≃ₗ[ℂ] W)
    (hR : IsIsom H H' (R : V →ₗ[ℂ] W)) (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ) (α' : W → ℂ) (hα : ∀ x, α' (R x) = α x)
    (hS : IsSemiChar H Λ₂ α) (hidx : relIdx Λ₁ Λ₂ ≠ 0) (F : V → ℂ) (F' : W → ℂ) (hF' : ∀ x, F' (R x) = F x)
    (hF : F ∈ fixedBy H α Λ₁) (z : V) :
    inter H' α' (imgLat (R : V →ₗ[ℂ] W) Λ₁) (imgLat (R : V →ₗ[ℂ] W) Λ₂) F' (R z) = inter H α Λ₁ Λ₂ F z := by
  obtain ⟨S, hSr⟩ := (repsExist V Λ₁ Λ₂ hidx).1
  rw [interReps V H hH Λ₁ Λ₂ α hS F hF S hSr z,
    interReps W H' hH' _ _ α' (semiChar_map H H' R hR Λ₂ α α' hα hS) F' (fixedBy_map H H' R hR Λ₁ α α' hα F F' hF' hF) _
      (isReps_map R hSr) (R z), relIdx_map]
  congr 1
  unfold sumU
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  show α' (R x) * opU H' (R x) F' (R z) = _
  rw [hα, opU_map H H' R hR F F' hF']

end Transport

section Reindex

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def rx {n n' : Type} (e : n' ≃ n) : (n → ℂ) ≃ₗ[ℂ] (n' → ℂ) where
  toFun f := fun i => f (e i)
  invFun g := fun j => g (e.symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by funext j; simp
  right_inv g := by funext i; simp

def e4 {n n' : Type} (e : n' ≃ n) : Fin 4 × n' ≃ Fin 4 × n := Equiv.prodCongr (Equiv.refl _) e

theorem matH_rx (e : n' ≃ n) (h : Matrix n n ℂ) (x y : n → ℂ) :
    matH (h.submatrix e e) (rx e x) (rx e y) = matH h x y := by
  rw [matH_apply, matH_apply, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  rfl

theorem block_fourfold_submatrix_reindex (e : n' ≃ n) (h : Matrix n n ℂ) : blk4 (h.submatrix e e) = (blk4 h).submatrix (e4 e) (e4 e) := by
  funext w w'
  rfl

theorem stdH_rx (L : PeriodPair) (e : n' ≃ n) (x y : n → ℂ) : stdH L n' (rx e x) (rx e y) = stdH L n x y := by
  rw [stdH_apply, stdH_apply, ← Equiv.sum_comp e]
  rfl

theorem stdLat_rx (L : PeriodPair) (e : n' ≃ n) : stdLat L n' = imgLat (rx e : (n → ℂ) →ₗ[ℂ] (n' → ℂ)) (stdLat L n) := by
  ext z
  rw [mem_imgLat, mem_stdLat, mem_stdLat]
  constructor
  · intro hz j
    exact hz (e.symm j)
  · intro hz i
    have := hz (e i)
    simpa [rx] using this

theorem thetaSeries_reindex_invariant (L : PeriodPair) (ω₀ : ℂ) (e : n' ≃ n) (x : n → ℂ) : F0 L ω₀ n' (rx e x) = F0 L ω₀ n x := by
  unfold F0 prodFn
  rw [← Equiv.prod_comp e]
  rfl

theorem fourth_power_image_reindex (e : n' ≃ n) (Λ : AddSubgroup (n → ℂ)) :
    pow4 (imgLat (rx e : (n → ℂ) →ₗ[ℂ] (n' → ℂ)) Λ) = imgLat (rx (e4 e) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ)) (pow4 Λ) := by
  ext z
  rw [mem_imgLat]
  constructor
  · intro hz a
    exact (mem_imgLat (rx e) Λ _).1 (hz a)
  · intro hz a
    exact (mem_imgLat (rx e) Λ _).2 (hz a)

theorem hOne_rx (L : PeriodPair) (e : n' ≃ n) : (hOne L n).submatrix e e = hOne L n' := by
  unfold hOne
  ext i j
  simp [Matrix.one_apply]

theorem locNorm_reindex (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) (e : n' ≃ n) (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, cmTheta b₀ dK • x ∈ Λ) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hN : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι) :
    LocNorm a₀ b₀ dK ha hdK lam hlam (h.submatrix e e) (imgLat (rx e : (n → ℂ) →ₗ[ℂ] (n' → ℂ)) Λ)
      (fun z => θ ((rx e).symm z)) p ι := by
  obtain ⟨g₁, ε, hI, hidx, hidx2, hε, hten⟩ := hN
  have hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := fun h0 => hidx (h0 ▸ dvd_zero p)
  have hSD := stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁ hI hsd hst hidx1 hidx2
  have hR4 : IsIsom (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n'))
      (rx (e4 e) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ)) := fun x y => stdH_rx _ (e4 e) x y
  have himg : imgLat (((rx (e4 e)).symm.trans (g₁.trans (rx (e4 e))) : (Fin 4 × n' → ℂ) ≃ₗ[ℂ] (Fin 4 × n' → ℂ)) :
        (Fin 4 × n' → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ)) (pow4 (imgLat (rx e : (n → ℂ) →ₗ[ℂ] (n' → ℂ)) Λ)) =
      imgLat (rx (e4 e) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ))
        (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
    rw [fourth_power_image_reindex]
    ext y
    rw [mem_imgLat, mem_imgLat, mem_imgLat, mem_imgLat]
    simp
  refine ⟨(rx (e4 e)).symm.trans (g₁.trans (rx (e4 e))), ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    obtain ⟨x, rfl⟩ := (rx (e4 e)).surjective x
    obtain ⟨y, rfl⟩ := (rx (e4 e)).surjective y
    rw [block_fourfold_submatrix_reindex, matH_rx]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [stdH_rx]
    exact hI x y
  · rw [himg, stdLat_rx _ (e4 e), relIdx_map]
    exact hidx
  · rw [himg, stdLat_rx _ (e4 e), relIdx_map]
    exact hidx2
  · funext z
    obtain ⟨z, rfl⟩ := (rx (e4 e)).surjective z
    have h1 : tens4 (fun z => θ ((rx e).symm z)) (rx (e4 e) z) = tens4 θ z := by
      unfold tens4
      refine Finset.prod_congr rfl fun a _ => ?_
      show θ ((rx e).symm (rx e (slice a z))) = θ (slice a z)
      rw [LinearEquiv.symm_apply_apply]
    rw [h1, hten]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [himg, stdLat_rx _ (e4 e)]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (inter_map _ _ (stdHBasic _ _).2.1 (stdHBasic _ _).2.1 (rx (e4 e)) hR4 _ _ _ _
      (fun x => alphaQRules.1 _ _ _ _ _ hR4 _ x) hSD.betaSemi hidx1 _ _ (fun x => thetaSeries_reindex_invariant _ _ (e4 e) x)
      (product_theta_mem' _ _ _ hSD.per hSD.half _ hSD.betaStd).1.2 (g₁ z)).symm

end Reindex

section Flat

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def lamMX : AddSubgroup (X.Tau → ℂ) := B.lamM.comap (LinearEquiv.funCongrLeft ℂ ℂ s.iT.symm).toLinearMap.toAddMonoidHom

def thMMX : (X.Tau → ℂ) → ℂ := fun z => B.thMM fun τ => z (s.iT.symm τ)

theorem mem_lamMX (z : X.Tau → ℂ) : z ∈ lamMX s B ↔ (fun τ => z (s.iT.symm τ)) ∈ B.lamM := Iff.rfl

theorem lamMX_eq : lamMX s B = imgLat (rx s.iT : (D.what₂.Tau → ℂ) →ₗ[ℂ] (X.Tau → ℂ)) B.lamM := by
  ext z
  rw [mem_imgLat]
  exact Iff.rfl

theorem isom_rx : IsIsom (matH (hOne B.L D.what₂.Tau)) (matH (hOne B.L X.Tau)) (rx s.iT : (D.what₂.Tau → ℂ) →ₗ[ℂ] (X.Tau → ℂ)) := by
  intro x y
  rw [← hOne_rx B.L s.iT]
  exact matH_rx s.iT _ x y

theorem selfDual_lamMX (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L X.Tau)) (lamMX s B) := by
  rw [lamMX_eq]
  exact CmData.selfDual_img _ _ (rx s.iT) (isom_rx s B) _ (selfDual_lamM B hcc hδ)

theorem stable_lamMX (b : ℤ) (hb : Odd b) : ∀ x ∈ lamMX s B, cmTheta b D.host.d • x ∈ lamMX s B :=
  fun _ hx => stable_lamM B b hb _ hx

theorem thMMX_mem (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    thMMX s B ∈ Th (matH (hOne B.L X.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L X.Tau))) (lamMX s B) := by
  rw [lamMX_eq, thIsom _ _ _ _ (rx s.iT) (isom_rx s B)]
  have h1 : (fun v => thMMX s B (rx s.iT v)) = B.thMM := by
    funext v
    show B.thMM ((rx s.iT).symm (rx s.iT v)) = B.thMM v
    rw [LinearEquiv.symm_apply_apply]
  have h2 : (fun v => alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L X.Tau)) (rx s.iT v)) =
      alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)) := by
    funext v
    exact alphaQRules.1 _ _ _ _ _ (isom_rx s B) _ v
  rw [h1, h2]
  exact (B.thMM_spec (B.stdOK hcc hδ)).1

theorem locNorm_thMMX (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀)
    (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d) (hB : B.IsCm a₀ b₀ ha hd lam hlam)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hK : B.KappaAt p ι) :
    LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B.L X.Tau) (lamMX s B) (thMMX s B) p ι := by
  have h := locNorm_reindex a₀ b₀ c₀ D.host.d ha hd lam hlam hcm s.iT (hOne B.L D.what₂.Tau) B.lamM (selfDual_lamM B hcc hδ)
    (stable_lamM B b₀ (odd_of_cmOK hcm)) B.thMM p ι (locNormMM_of B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB p ι hK)
  rw [hOne_rx, ← lamMX_eq] at h
  exact h

end Flat

end Formalism.L2.Ker.KS.MM
