import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem markMove_finVec_mem {D : D7} (V : HSp D) (g : GA D V) {v : Fin V.rank → D.host.E} (hv : v ∈ latG V g) :
    finVec V v ∈ latGHat V g := by
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1]
  exact AddSubgroup.subset_closure ⟨1, fun w => one_mem _, v, hv, rfl⟩

theorem markMove_mulVec_mem {D : D7} (V : HSp D) (g : GA D V)
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ latGHat V 1) :
    (finHom V g).1 *ᵥ y ∈ latGHat V g := by
  have h := (GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.1
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at hy
  rw [← SetLike.mem_coe, h]
  exact ⟨y, hy, rfl⟩

theorem markMove_finVec_add_nsmul {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) (n : ℕ) :
    finVec V (x + n • y) = finVec V x + n • finVec V y := by
  funext i
  simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
  congr 1
  exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) n (y i)

theorem markMove_mulVec_nsmul {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (n : ℕ)
    (y : Fin m → R) : A *ᵥ (n • y) = n • (A *ᵥ y) := Matrix.mulVec_smul _ _ _

theorem markMove_finHom_mul {D : D7} (V : HSp D) (g h : GA D V)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ y = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ y) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

set_option maxHeartbeats 800000 in

theorem mark_move : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k γ, C.Mark h k γ → (∀ γ₀ ∈ GQ V, C.Mark (γ₀ * h) k (γ * γ₀⁻¹)) ∧ (∀ u, FinCong V l.M u → C.Mark (h * u) k γ) ∧ (∀ u ∈ GinfC V, C.Mark (h * u) k γ) ∧ ∀ δ ∈ (C.M.X k).Γ, ∃ γ₁ ∈ GQ V, C.Mark h k (γ₁ * γ) ∧ C.fr (γ₁ * γ * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h k γ hM
  obtain ⟨hγ, hΛ, hmk⟩ := hM
  refine ⟨fun γ₀ hγ₀ => ?_, fun u hu => ?_, fun u hu => ?_, fun δ hδ => ?_⟩
  · have e : γ * γ₀⁻¹ * (γ₀ * h) = γ * h := by group
    refine ⟨mul_mem hγ (inv_mem hγ₀), ?_, ?_⟩
    · rw [e]; exact hΛ
    · rw [e]; exact hmk
  · have e : γ * (h * u) = γ * h * u := (mul_assoc _ _ _).symm
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.2.1 l.M (γ * h) u hu
    refine ⟨hγ, ?_, ?_⟩
    · rw [e, e1]; exact hΛ
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hιa : C.ι a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • latG V 1 := by
        rw [← hC.iota.emb.2, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ha
      obtain ⟨y, hy, hy'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 l.M _).1 (((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).1 u).1 hu) _ hιa
      rw [e, e2]
      refine ⟨w - (finHom V (γ * h)).1 *ᵥ y, sub_mem hw (markMove_mulVec_mem V _ hy), ?_⟩
      rw [markMove_finHom_mul, sub_eq_iff_eq_add'.1 hy', Matrix.mulVec_add, markMove_mulVec_nsmul, nsmul_sub, ← hw',
        sub_add_eq_sub_sub]
  · have e : finHom V (γ * (h * u)) = finHom V (γ * h) := by
      have hu' : finHom V u = 1 := hu
      rw [← mul_assoc, map_mul _ _ u, hu', mul_one]
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.1 _ _ e
    refine ⟨hγ, ?_, ?_⟩
    · rw [e1]; exact hΛ
    · rw [e2, e]; exact hmk
  · have hr := C.hr
    subst hr
    obtain ⟨⟨hU, hS⟩, hcong, -⟩ := (hC.base.gam k δ).1 hδ
    have hG : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
    rw [hG] at hU
    obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
    obtain ⟨γ₁, hγ₁⟩ := r3 δ hU
    have hq : γ₁ ∈ GQ V := (r1 γ₁).2 ⟨δ, hγ₁⟩
    obtain ⟨m1, m2⟩ := (GlobalTheory.Member.latG_move D V).1 γ₁ δ (γ * h) hγ₁
    obtain ⟨f1, f2⟩ := r5 γ₁ δ hγ₁
    have hΛ' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
      rw [← SetLike.mem_coe, hΛ]
      exact ⟨fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx, fun hv => ⟨v, hv, rfl⟩⟩
    have hΛ'' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ₁ * (γ * h)) := fun v => by
      have e : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
          (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h0 := ((hS _).symm.trans (hΛ' (((δ⁻¹ : GL (Fin V.rank) D.host.E) :
        Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v))).trans (m1 _)
      rwa [e] at h0
    refine ⟨γ₁, hq, ⟨mul_mem hq hγ, ?_, ?_⟩, ?_⟩
    · rw [mul_assoc]
      ext v
      rw [SetLike.mem_coe, hΛ'']
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx⟩
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hta : C.F.t k a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) •
          (⊤ : Submodule (𝓞 D.host.E) (C.F.Di k).La) := by
        have h1 := Submodule.mem_map_of_mem (f := C.F.t k) ha
        rw [Submodule.map_smul''] at h1
        exact Submodule.smul_mono le_rfl le_top h1
      obtain ⟨b, hb⟩ := hcong _ hta
      rw [mul_assoc]
      refine ⟨(finHom V γ₁).1 *ᵥ w - finVec V (C.M.φ k b : Fin V.rank → D.host.E),
        sub_mem ((m2 w).1 hw) (markMove_finVec_mem V _ ((hΛ'' _).1 (C.M.φ k b).2)), ?_⟩
      have hw2 : finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
          (finHom V (γ * h)).1 *ᵥ (finVec V (C.ι a)) = (l.M : ℕ) • w := hw'
      have h3 := f1 (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E)
      rw [hb, markMove_finVec_add_nsmul] at h3
      show finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      rw [markMove_finHom_mul, nsmul_sub, ← markMove_mulVec_nsmul, ← hw2, Matrix.mulVec_sub, h3]
      abel
    · funext τ
      have a1 := ((GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf).1 τ.1).2.1 γ₁ (γ * h)
      have a2 := f2 τ.1 (C.θ τ.1) (hC.inf τ.1)
      show (archM V (C.θ τ.1) (γ₁ * γ * h) * C.x₀ τ.1 : Matrix _ _ ℂ) =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [mul_assoc γ₁, a1, a2, Matrix.mul_assoc]

end GlobalTheory.Member
