import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def hJ (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hJ_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hJ J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hJ_symm {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J) :
    (hJ J).IsSymm := by
  have hJij : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJh i) j
    simpa [Formalism.UG.cT] using this
  refine ⟨fun x y => ?_⟩
  change starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x
  simp only [Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_self_apply, hJij]
  ring

theorem hJ_single (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by
  rw [hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem hJ_nondeg {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) (x : Fin n → E)
    (hx : ∀ y, hJ J x y = 0) : x = 0 := by
  have h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0 := by
    funext j; rw [← hJ_single]; exact hx _
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  funext i
  have := congrFun h1 i
  simpa using this

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨conjO E r, algebraMap_conjO r⟩

theorem unimod_of_selfDual {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : SelfDual J L) : Formalism.HermitianLatticesTheory.IsUnimodular (hJ J) L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [hL x]
  constructor
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩

theorem selfDualMod_loc {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J)
    {L : Submodule (𝓞 E) (Fin n → E)} (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hL : SelfDual J L) {p : Ideal (𝓞 E)} (hp : p.IsMaximal) :
    IsSelfDualMod (locRing p) (hJ J) (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup := by
  have hu := (Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1
    (unimod_of_selfDual hL) p hp
  exact isSelfDualMod_loc ⟨hfg, hsp⟩ hp.isPrime hu

theorem gl_of_isom {J : Matrix (Fin n) (Fin n) E} (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ x y, hJ J (g x) (g y) = hJ J x y) :
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := by
  let A := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  let B := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  let γ : GL (Fin n) E := ⟨A, B, hAB, hBA⟩
  have hmul : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := fun w => by
    change A *ᵥ w = g w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨γ, ?_, hmul⟩
  change Formalism.UG.cT (starRingEnd E) A * J * A = J
  ext i j
  have e1 := hg (Pi.single i 1) (Pi.single j 1)
  have hsingle : ∀ k l, hJ J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    rw [hJ_single, Matrix.vecMul, dotProduct]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hsingle] at e1
  rw [← e1, hJ_apply, Formalism.UG.hform]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  have hcol : ∀ k l, A k l = g (Pi.single l 1) k := fun k l => by
    simp [A, LinearMap.toMatrix'_apply]
  simp only [hcol, Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
