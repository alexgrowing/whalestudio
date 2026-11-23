import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Col2.RatFrPt
open GlobalTheory.Mem.Col2.PtExist

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def glEquiv (γ : GL (Fin n) E) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (γ : Matrix (Fin n) (Fin n) E)) (Matrix.toLin' ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem glEquiv_apply (γ : GL (Fin n) E) (x : Sp E n) : glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

theorem glEquiv_single (γ : GL (Fin n) E) (i j : Fin n) : glEquiv γ (Pi.single j 1) i = (γ : Matrix (Fin n) (Fin n) E) i j := by
  rw [glEquiv_apply, Matrix.mulVec_single_one]
  rfl

theorem adAt_inv {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (r s : Fin n) : adAt F P (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) r s) := by
  set M : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) with hM
  have hM' : M = (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) := Matrix.ext fun a b => h a b
  have h1 : ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) * M = 1 := by
    rw [hM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) * M = 1 := by
    rw [hM', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e := (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)
  exact congrFun (congrFun e r) s

variable [StarRing E]

theorem glEquiv_mem_iff {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (hN : Submodule.IsLattice E (Formalism.UG.CS.globLat g (stdLat E n)))
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (x : Sp E n) : glEquiv γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g (stdLat E n)) ↔ x ∈ stdAt E n P := by
  have hi := adAt_inv h
  constructor
  · intro hx
    rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
    intro i
    have h1 := valued_pullV_le g hx i
    have e : adAt F P (Formalism.L2.Col.pullV g (glEquiv γ x) i) = algebraMap E (P.adicCompletion E) (x i) := by
      have e2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ glEquiv γ x = x := by
        rw [glEquiv_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      conv_rhs => rw [← e2]
      simp only [Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, hi, adAt_inclE]
    rwa [e] at h1
  · intro hx
    obtain ⟨f, hf⟩ := CharValCompare.exists_isFr P hN
    have hy : f.symm (glEquiv γ x) ∈ stdAt E n P := by
      rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
      intro i
      set A : Matrix (Fin n) (Fin n) E := mat f.symm * (γ : Matrix (Fin n) (Fin n) E) with hA
      have hA1 : ∀ j, Valued.v (algebraMap E (P.adicCompletion E) (A i j)) ≤ 1 := by
        intro j
        have h2 := valued_symm_le (u := fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l j) hf
          ((carries_globLat g _).2 ((mem_latS_std _).2 fun l => ?_)) i
        · simp only [h, ← map_mul, ← map_sum] at h2
          rw [hA, Matrix.mul_apply]
          exact h2
        · simp only [Matrix.mulVec, dotProduct]
          rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
      have e3 : f.symm (glEquiv γ x) = A *ᵥ x := by
        funext i
        rw [← mat_mulVec, hA, ← Matrix.mulVec_mulVec, glEquiv_apply]
        rfl
      rw [e3]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul]
      exact mul_le_one' (hA1 j) ((GlobalTheory.Mem.ColAd.mem_stdAt_val.1 hx) j)
    have := (hf _).2 hy
    rwa [f.apply_symm_apply] at this
end

theorem exists_isPtOf_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g hg hQ
  choose! γ hγ using hQ
  obtain ⟨p₀, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p₀.deco.1.N := congrArg Deco.N hd
  have hlat : Submodule.IsLattice E (Formalism.UG.CS.globLat g (stdLat E n)) := hN ▸ p₀.deco.2.lat
  let p : DecoF E n ST SG Q := ⟨(p₀.deco, fun P => glEquiv (γ P.1)), fun P x => by
    show glEquiv (γ P.1) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p₀.deco.1.N ↔ _
    rw [← hN]
    exact glEquiv_mem_iff hlat (hγ P.1 P.2) x⟩
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.f P v)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.be P v i)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · show _ = algebraMap E _ (glEquiv (γ P.1) (Pi.single j 1) i)
    rw [glEquiv_single]
    exact hγ P.1 P.2 i j

end GlobalTheory.Mem.Col2.RatFrPt
