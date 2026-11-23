import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceInd

open GlobalTheory.IdemSplit GlobalTheory.CongSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def epsOff (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : AL L :=
  ∏ v ∈ T, (1 - idemAt L v)

theorem compAt_epsOff_of_mem {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ∈ T) :
    compAt L w (epsOff L T) = 0 := by
  rw [epsOff, map_prod]
  exact Finset.prod_eq_zero hw (by rw [map_sub, map_one, compAt_idemAt_self, sub_self])

theorem epsOff_mem (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    epsOff L T ∈ ALint L :=
  Subring.prod_mem _ fun v _ => Subring.sub_mem _ (one_mem _) (idemAt_mem L v)

theorem epsOff_insert [DecidableEq (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))]
    {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hv : v ∉ T) :
    epsOff L (insert v T) = (1 - idemAt L v) * epsOff L T := by
  rw [epsOff, Finset.prod_insert hv, epsOff]

theorem epsOff_mono {T T' : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') :
    ∃ c ∈ ALint L, epsOff L T' = c * epsOff L T := by
  classical
  exact ⟨epsOff L (T' \ T), epsOff_mem L _, (Finset.prod_sdiff h).symm⟩

theorem exists_epsOff_mul_mem (z : AL L) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), epsOff L T * z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, h⟩ := GlobalTheory.FormInner.exists_int_off z
  refine ⟨S, ?_⟩
  have e : epsOff L S * z = epsOff L S * Y := by
    apply sub_eq_zero.1
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, map_mul]
    by_cases hw : w ∈ S
    · rw [compAt_epsOff_of_mem L hw]; ring
    · rw [h w hw]; ring
  rw [e]
  exact Subring.mul_mem _ (epsOff_mem L S) hY

theorem gaFold_split {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n)
    (he : idemAt L v * idemAt L v = idemAt L v) (hσ : conjAL L (idemAt L v) = idemAt L v)
    (he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v)
    (hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v) :
    g = gaFold he hσ g * gaFold he' hσ' g := by
  apply Subtype.ext; apply Units.ext
  show (g.1 : Matrix (Fin n) (Fin n) (AL L)) = fold (idemAt L v) _ * fold (1 - idemAt L v) _
  rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

theorem ind_epsOff (n N : ℕ) (p : GAf L n → Prop) (hC : ∀ κ, NG.Cong L n N κ → p κ)
    (hstep : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n),
      TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y))
    (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    ∀ g : GAf L n, (∀ i j, ∃ y ∈ ALint L, epsOff L T * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (N : AL L) * y) → p g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hg' : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y := by
      intro i j
      obtain ⟨y, hy, e⟩ := hg i j
      rw [epsOff, Finset.prod_empty, one_mul] at e
      exact ⟨y, hy, e⟩
    apply hC
    refine ⟨fun i j => ?_, hg'⟩
    obtain ⟨y, hy, e⟩ := hg' i j
    have h1 : (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * y := by rw [← e]; ring
    rw [h1]
    exact Subring.add_mem _ (one_apply_mem L i j) (Subring.mul_mem _ (natCast_mem _ _) hy)
  | @insert v T hv ih =>
    intro g hg
    have he : idemAt L v * idemAt L v = idemAt L v := idemAt_mul_self L v
    have he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v := by
      rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
    have hσ : conjAL L (idemAt L v) = idemAt L v := conjAL_idemAt L v
    have hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v := by rw [map_sub, map_one, hσ]
    have hx : TrivOutside {v} (gaFold he hσ g) := by
      intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_mul, map_sub, map_one,
        compAt_idemAt_ne L v hw', compAt_one_apply]
      simp
    have hy : TrivOutside {v}ᶜ (gaFold he' hσ' g) := by
      intro w hw
      have hw' : w = v := by simpa using hw
      rw [hw']
      ext i j
      simp only [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_sub, map_one,
        compAt_idemAt_self, compAt_one_apply]
      simp
    have hp : p (gaFold he' hσ' g) := by
      apply ih
      intro i j
      obtain ⟨y, hy, eq⟩ := hg i j
      refine ⟨y, hy, ?_⟩
      rw [epsOff_insert L hv] at eq
      rw [gaFold_val, fold_apply]
      linear_combination eq
    have := hstep v _ _ hx hy hp
    rwa [← gaFold_split L v g he hσ he' hσ'] at this

theorem induction_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  intro L _ _ _ n N hN p hC hstep g
  classical
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 :=
    ⟨algebraMap L (AL L) (N : L)⁻¹, by
      rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hN', map_one]⟩
  have hT : ∀ q : Fin n × Fin n, ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))),
      epsOff L T * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2 -
        (1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2)) ∈ ALint L :=
    fun q => exists_epsOff_mul_mem L _
  choose T hT using hT
  refine ind_epsOff L n N p hC hstep (Finset.univ.biUnion T) g fun i j => ?_
  obtain ⟨c, hc, e⟩ := epsOff_mono L (Finset.subset_biUnion_of_mem T (Finset.mem_univ (i, j)))
  refine ⟨c * (epsOff L (T (i, j)) * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))), Subring.mul_mem _ hc (hT (i, j)), ?_⟩
  rw [e]
  linear_combination (-(c * epsOff L (T (i, j)) * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))) * hu

end GlobalTheory.PlaceInd
