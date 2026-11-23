import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

@[reducible] def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by
    show σ (x * y) = σ y * σ x
    rw [map_mul, mul_comm]
  star_add x y := map_add σ x y

section General

variable {E : Type} [Field E] {M : ℕ}

theorem hform_add_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J (c • x) y = σ c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J x (c • y) = RingHom.id E c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [StarRing E]

def hSes (J : Matrix (Fin M) (Fin M) E) : (Fin M → E) →ₗ⋆[E] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (hform_add_left' _ J) (hform_smul_left' _ J) (hform_add_right' _ J) (hform_smul_right' _ J)

theorem hSes_apply (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hSes J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hSes_herm (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (x y : Fin M → E) : star (hSes J x y) = hSes J y x := by
  rw [hSes_apply, hSes_apply]
  show starRingEnd E _ = _
  simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hSes_nondeg (J : Matrix (Fin M) (Fin M) E) (hdet : J.det ≠ 0) (x : Fin M → E)
    (hx : ∀ y, hSes J x y = 0) : x = 0 := by
  have h1 : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have := hx (Pi.single j 1)
    rw [hSes_apply] at this
    simpa [Formalism.UG.hform, Pi.single_apply, vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have := congrFun h2 i
  simpa using this

theorem linInd_of_gram (J : Matrix (Fin M) (Fin M) E) {a : ℕ} (X : Fin a → Fin M → E)
    (G : Matrix (Fin a) (Fin a) E) (hG : ∀ i j, G i j = Formalism.UG.hform (starRingEnd E) J (X i) (X j))
    (hdet : G.det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : G *ᵥ c = 0 := by
    funext j
    have := congrArg (hSes J (X j)) hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [mulVec, dotProduct, Pi.zero_apply, hG]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSes_apply]
    ring
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h1) i

variable [CharZero E]

theorem witt_tuple (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (hdet : J.det ≠ 0) {a : ℕ} (X0 X : Fin a → Fin M → E) (h0 : LinearIndependent E X0)
    (h1 : LinearIndependent E X)
    (hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j)) :
    ∃ g ∈ Formalism.UG.UJ (starRingEnd E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E) *ᵥ X0 i = X i := by
  let U := Submodule.span E (Set.range X0)
  let bU : Module.Basis (Fin a) E U := Module.Basis.span h0
  have hb : ∀ i, ((bU i : U) : Fin M → E) = X0 i := fun i => by
    show ((Module.Basis.span h0 i : U) : Fin M → E) = X0 i
    rw [Module.Basis.span_apply]
  let f : U →ₗ[E] (Fin M → E) := bU.constr E X
  have hf : ∀ i, f (bU i) = X i := fun i => bU.constr_basis E X i
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hs := bU.sum_repr u
    rw [← hs] at hu
    simp only [map_sum, map_smul, hf] at hu
    have hc := (Fintype.linearIndependent_iff.mp h1) _ hu
    rw [← hs]
    simp [hc]
  have key : ((hSes J).comp f).compl₂ f = ((hSes J).comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis bU bU fun i j => ?_
    show hSes J (f (bU i)) (f (bU j)) = hSes J ((bU i : U) : Fin M → E) ((bU j : U) : Fin M → E)
    rw [hf, hf, hb, hb]
    exact hG i j
  have hiso : ∀ x y : U, hSes J (f x) (f y) = hSes J x y := fun x y =>
    DFunLike.congr_fun (DFunLike.congr_fun key x) y
  obtain ⟨g, hgiso, hgf⟩ :=
    witt_extension_theorem E (Fin M → E) (hSes J) (hSes_herm J hJ) (hSes_nondeg J hdet) U f hinj hiso
  let m : Matrix (Fin M) (Fin M) E := LinearMap.toMatrix' (g : (Fin M → E) →ₗ[E] (Fin M → E))
  let mi : Matrix (Fin M) (Fin M) E :=
    LinearMap.toMatrix' (g.symm : (Fin M → E) →ₗ[E] (Fin M → E))
  have hc1 : (g : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hc2 : (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hm1 : m * mi = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
  have hm2 : mi * m = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id]
  have hmv : ∀ v, m *ᵥ v = g v := fun v => by
    simp only [m]
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  refine ⟨⟨m, mi, hm1, hm2⟩, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd E) m * J * m = J
    ext i j
    have h := hgiso (Pi.single i 1) (Pi.single j 1)
    rw [hSes_apply, hSes_apply, ← hmv, ← hmv, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single,
      Formalism.UG.P.hform_single] at h
    exact h
  · intro i
    show m *ᵥ X0 i = X i
    rw [hmv, ← hb i]
    exact (hgf (bU i)).trans (hf i)

end General

theorem sigma_invol_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem witt_holds : Witt := by
  unfold Witt InCtx
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ hdet X hX
  letI : StarRing E := starOfInv (σ : E →+* E) (sigma_invol_cm σ hCM)
  have hs : starRingEnd E = (σ : E →+* E) := RingHom.ext fun _ => rfl
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := by
    rw [hs]; exact hJ.1
  have hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j) := by
    rw [hs]; exact fun i j => congrFun (congrFun hX i) j
  have hl0 : LinearIndependent E X0 :=
    linInd_of_gram J X0 (gramE σ J X0) (by rw [hs]; intro i j; rfl) hdet
  have hl1 : LinearIndependent E X :=
    linInd_of_gram J X (gramE σ J X) (by rw [hs]; intro i j; rfl) (hX ▸ hdet)
  obtain ⟨g, hg, hgX⟩ := witt_tuple J hJ' hJ.2 X0 X hl0 hl1 hG
  rw [hs] at hg
  exact ⟨g, hg, hgX⟩

end PI.VolStabS
