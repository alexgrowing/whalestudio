import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatMove

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_hatL {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hz ⊢
  intro i
  have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z) = (intGL F E n y).1 *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    change β⁻¹ * (β * intGL F E n y * β⁻¹) = _
    group
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hq : Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom q ∈ St β)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have h := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _
    (mulVec_mem_hatL hβ hq (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

omit [NumberField F] [NumberField E] in

theorem bc_map_bc_inclR {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (g : GL (Fin n) E) :
    Formalism.UG.bc (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g) =
      Formalism.UG.bc (inclR (F := F) S) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.map f (AlgHom.id F E) (1 ⊗ₜ g.1 i j) = 1 ⊗ₜ g.1 i j
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

omit [NumberField F] [NumberField E] in

theorem span_move {R O : Type} [CommRing R] [Algebra F R] [CommRing O] [Algebra O E] (H : AddSubgroup (Fin n → R ⊗[F] E))
    (g : GL (Fin n) E) (h q : GL (Fin n) (R ⊗[F] E)) (h1 : ∀ z ∈ H, q.1 *ᵥ z ∈ H) (h2 : ∀ z ∈ H, (q⁻¹).1 *ᵥ z ∈ H) :
    Submodule.span O {x : Fin n → E |
        ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H} =
      (Submodule.span O {x : Fin n → E | (h⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H}).map
        ((Matrix.mulVecLin g.1).restrictScalars O) := by
  have hv : ∀ (g : GL (Fin n) E) (x : Fin n → E),
      (Formalism.UG.bc (inclR (F := F) R) g).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) = fun i => (1 : R) ⊗ₜ[F] (g.1 *ᵥ x) i := by
    intro g x
    funext i
    exact (RingHom.map_mulVec (inclR (F := F) R) g.1 x i).symm
  have key : ∀ z, (q⁻¹).1 *ᵥ z ∈ H ↔ z ∈ H := by
    refine fun z => ⟨fun hz => ?_, h2 z⟩
    have := h1 _ hz
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
  have hs : ∀ x : Fin n → E,
      ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) =
        (q⁻¹).1 *ᵥ ((h⁻¹).1 *ᵥ fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ x) i) := by
    intro x
    rw [← hv, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      mul_inv_rev, mul_inv_rev, mul_assoc]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(g⁻¹).1 *ᵥ x, (key _).1 (hs x ▸ hx), ?_⟩
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    change _ *ᵥ _ ∈ H
    rw [hs, key]
    change _ *ᵥ (fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ (g.1 *ᵥ y)) i) ∈ H
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy

end General

variable {D : D7}

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧
    (Bridge.ratF V γ).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
  obtain ⟨γE, -, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  refine ⟨γE, hm, ?_⟩
  change finHom V γ.1 = _
  rw [finHom, MonoidHom.comp_apply, hm]
  exact bc_map_bc_inclR _ _

theorem hLat_eq_span {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (h : Bridge.Gf V) :
    Bridge.hLat V h = Submodule.span (𝓞 D.host.E) {x : Fin V.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))} := by
  rw [GlobalTheory.PrincInLevel.eq_latC hΛ, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  rfl

theorem mulVec_mem_hat_swap {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)} (hq : Formalism.UG.bc (swapAE D) q ∈ St β) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)),
      q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
  fun _ hz => mulVec_mem_hat hβ hq hz

theorem hLat_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (g h q : Bridge.Gf V) (γE : GL (Fin V.rank) D.host.E)
    (hf : g.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE) (hq : Formalism.UG.bc (swapAE D) q.1 ∈ St β) :
    Bridge.hLat V (g * h * q) = (Bridge.hLat V h).map ((Matrix.mulVecLin γE.1).restrictScalars (𝓞 D.host.E)) := by
  have hfr : IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hq' : Formalism.UG.bc (swapAE D) (q.1⁻¹) ∈ St β := by
    rw [MonoidHom.map_inv]; exact (St β).inv_mem hq
  have e : (g * h * q).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE * h.1 * q.1 := hf ▸ rfl
  rw [hLat_eq_span hΛ, hLat_eq_span hΛ, e]
  exact span_move _ γE h.1 q.1 (mulVec_mem_hat_swap hfr hq) (mulVec_mem_hat_swap hfr hq')

theorem hLat_rat_mul_stab : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ γ : GQ V, ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧ ∀ h q : Bridge.Gf V, Formalism.UG.bc (swapAE D) (q : GL (Fin V.rank) _) ∈ St β → Bridge.hLat V (Bridge.ratF V γ * h * q) = Formalism.HermitianLatticesTheory.gmap ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V h) := by
  intro D V β Λ hΛ γ
  obtain ⟨γE, hγ, hf⟩ := exists_ratMat V γ
  refine ⟨γE, hγ, fun h q hq => ?_⟩
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]
  exact hLat_mul hΛ _ h q γE hf hq

end GlobalTheory.HLatMove
