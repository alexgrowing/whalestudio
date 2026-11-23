import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceR

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def levelTwo (K : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) :
    Subgroup (GL (Fin s) (Af E)) :=
  K.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (Slice2.lev2 (Af E) r s))

theorem mem_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)}
    {u : GL (Fin s) (Af E)} : u ∈ levelTwo K t ↔ t⁻¹ * lev (Af E) r s (1, u) * t ∈ K := by
  simp [levelTwo, MulAut.conj_apply, Slice2.lev2]

theorem isOpen_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))}
    (hK : IsOpen (K : Set (GL (Fin (r + s)) (Af E)))) (t : GL (Fin (r + s)) (Af E)) :
    IsOpen (levelTwo K t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun u : GL (Fin s) (Af E) => t⁻¹ * Slice2.lev2 (Af E) r s u * t :=
    (continuous_const.mul Slice2.continuous_lev2).mul continuous_const
  convert hK.preimage hc using 1
  ext u
  exact mem_levelTwo

def sliceMap (k : Kinf E (r + s)) : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Slice2.levK E r s κ * k

theorem lev_finGL_right (x : GA E r) (g : GA E s) (u : GL (Fin s) (Af E)) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t =
      lev (Ad E) r s (x, g) * cf (r + s) k t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
  have hY : finGL E (r + s) (lev (Af E) r s (1, u)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [Slice2.lev_mul_right, Slice2.lev_finGL_one, cf, mul_assoc (lev (Ad E) r s (x, g)),
    ← mul_assoc (finGL E (r + s) _), ← infGL_comm, mul_assoc (infGL E (r + s) _), hY]
  simp only [mul_assoc]

theorem lev_infGL_right (x : GA E r) (g : GA E s) (κ : Kinf E s) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t =
      (lev (Ad E) r s (x, g) * finGL E (r + s) t) *
        infGL E (r + s) (Unitary.toUnits (Slice2.levK E r s κ * k)) := by
  rw [Slice2.lev_mul_right, Slice2.lev_infGL_one, cf, map_mul Unitary.toUnits, Slice2.toUnits_levK,
    map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (x, g)) (finGL E (r + s) t), infGL_comm _ t]
  rw [mul_assoc (lev (Ad E) r s (x, g)) (infGL E (r + s) _), ← mul_assoc (infGL E (r + s) _) (finGL E (r + s) t),
    infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceR

theorem GlobalTheory.CompanionTheory.LimV.SliceR.slice_right : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  intro E _ _ _ r s k t K W hK hW
  refine ⟨SliceR.levelTwo K t, W.map (SliceR.sliceMap k), SliceR.isOpen_levelTwo hK t, inferInstance,
    fun f hf x => ⟨fun u hu g => ?_, fun g => ?_⟩⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t), ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

end
