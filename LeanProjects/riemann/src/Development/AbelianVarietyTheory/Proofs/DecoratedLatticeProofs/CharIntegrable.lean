import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ReflectionBoostMatrixConjTransposeMulSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.PlaceModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocReduction

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S0 T0 : HSp D} {m n : ℕ}

theorem isHalf_smul {e : AE D} {u : Mx D m n} : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heis_add {x y : WO S T} (h : symplO S T x y = 0) (f : WO S T → ℂ) :
    heisO ψ S T (x + y) f = heisO ψ S T x (heisO ψ S T y f) := by
  have := heisL_heisL S T ψ x y f
  rw [symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  exact this.symm

theorem heis_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := heisL_comm S T ψ x y f

theorem heis_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f :=
  (heisL S T ψ x).map_smul c f

section Model

variable {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}

theorem fix_half (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf e u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.trans _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  rw [halfInd_eq_ind]
  exact ind_add _ t (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hu'⟩)

theorem fix_conj (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf (cA D e) u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  unfold halfInd
  split_ifs with h
  · rw [hLL' t h.1 h.2 u hu hu', mul_one]
  · rw [mul_zero]

end Model

section Periodic

open GlobalTheory.MixModel

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}

end Periodic

def red (ψ : AddChar (AF D.host.F) ℂ) (jA : Mx D m n →+ WO S T) (j0 : WO S0 T0 →+ WO S T) (μ : Measure (Mx D m n))
    (𝓕 : Set (Mx D m n)) (f : WO S T → ℂ) : WO S0 T0 → ℂ :=
  fun z => ∫ a in 𝓕, heisO ψ S T (j0 z) f (jA a) ∂μ

section Red

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x) (hcont : Continuous jA)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)

end Red

section Main

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {e : AE D} {Λ : AddSubgroup (WO S T)}
  {Λ0 : AddSubgroup (WO S0 T0)}
  (sA : ∀ (c : AE D) a, jA (c • a) = c • jA a) (sB : ∀ (c : AE D) b, jB (c • b) = c • jB b)
  (s0 : ∀ (c : AE D) z, j0 (c • z) = c • j0 z)
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hBB : ∀ b b', symplO S T (jB b) (jB b') = 0)
  (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0) (hB0 : ∀ b z, symplO S T (jB b) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hdec : ∀ x : WO S T, ∃ a b z, x = jA a + jB b + j0 z)
  (hhalf : ∀ (c : AE D) a b z, IsHalf c (jA a + jB b + j0 z) → IsHalf c a ∧ IsHalf c b ∧ IsHalf c z)
  (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
  (hX : ∀ x, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
  (hY : ∀ y, IsHalf (cA D e) y → (∀ x ∈ Λ, IsHalf e x → ψ (symplO S T x y) = 1) → y ∈ Λ)
  (hsp : ∀ a b z, IsHalf e a → IsHalf e b → IsHalf e z →
    (jA a + jB b + j0 z ∈ Λ ↔ jA a ∈ Λ ∧ jB b ∈ Λ ∧ j0 z ∈ Λ))
  (hsp0 : ∀ z, IsHalf e z → (j0 z ∈ Λ ↔ z ∈ Λ0))

variable {μw : Measure (Mx D m n)} (hψ : IsStdChar D ψ (-1)) (hcont : Continuous jA)
  (hcl : IsClosed {x : WO S T | x ∈ Λ ∧ IsHalf e x})
  (hw0 : μw {a | ¬ IsHalf e a} = 0) (hw1 : ∀ a₀ : Mx D m n, IsHalf e a₀ → Measure.map (fun a => a + a₀) μw = μw)
  (hw2 : μw {a | IsHalf e a ∧ jA a ∈ Λ} = 1)

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)
  (hec : e * cA D e = 0) (hinf : infPart D e = 0)
  {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hf₀ : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)

end Main

section Lattice

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {e : AE D}

open GlobalTheory.PlaceDatum in

theorem lattice_facts (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hinf : infPart D e = 0) :
    (∀ u ∈ latO S T ΛS ΛT fun _ => True, IsHalf e u → ∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y →
      ψ (symplO S T u y) = 1) ∧
    (∀ x, IsHalf e x → (∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) →
      x ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ y, IsHalf (cA D e) y → (∀ x ∈ latO S T ΛS ΛT fun _ => True, IsHalf e x → ψ (symplO S T x y) = 1) →
      y ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∃ r ∈ R, ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u) ∧
    ∀ y, IsHalf (cA D e) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latO S T ΛS ΛT fun _ => True := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  refine ⟨fun u hu hu' y hy _ => (hdual u (infPart_of_half hinf hu')).1 hu y hy, fun x hx h => ?_, fun y hy h => ?_,
    fun k hk => ?_, fun y hy => exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) hy)⟩
  · refine (hdual x (infPart_of_half hinf hx)).2 fun u hu => ?_
    have := h _ (hsm _ he' u hu).1 ((isHalf_iff S T).2 (hsm _ he' u hu).2)
    rwa [← symplO_smul, isHalf_smul.1 hx] at this
  · refine (hdual y (infPart_of_half (infPart_cA hinf) hy)).2 fun u hu => ?_
    have := h _ (hsm _ he u hu).1 ((isHalf_iff S T).2 (hsm _ he u hu).2)
    rw [symplO_smul, isHalf_smul.1 hy] at this
    rw [symplO_skew, ← one_mul (ψ _), ← this, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, this]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

end Lattice

end GlobalTheory.LocReduction

end
