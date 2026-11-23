import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.BinfInv

private theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

private theorem algebraMap_mem_filtration_one_iff_mem_ker (l : ℕ) [Fact l.Prime] (a : Per.AinfP l) :
    algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 ↔ a ∈ Per.kerP l := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem, pow_one]

private theorem galoisAction_mem_filtration (l : ℕ) [Fact l.Prime] (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l)
    (hy : y ∈ Per.FilP l n) : Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have ha : aDp l (xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply]
  have hσ : Per.σDp g (aDp l (xi e)) ∈ Per.FilP l 1 := by
    rw [ha] at hξ ⊢
    rw [GlobalTheory.RingIface.sigDp_alg, algebraMap_mem_filtration_one_iff_mem_ker]
    exact GlobalTheory.RingBasics.ker_σ g ((algebraMap_mem_filtration_one_iff_mem_ker l _).1 hξ)
  have hd : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    simpa only [pow_one] using (hP 1 _).1 hσ
  refine (hP n _).2 ((pow_dvd_pow_of_dvd hd n).trans ?_)
  rw [← map_pow]
  exact map_dvd _ ((hP n _).1 hy)

theorem σDp_mem_FilP {l : ℕ} [Fact l.Prime] (g : Per.Gq l) (m : ℕ) {x : Per.BdRp l}
    (hx : x ∈ Per.FilP l m) : Per.σDp g x ∈ Per.FilP l m :=
  galoisAction_mem_filtration l g m x hx

theorem eq_of_forall_mem_FilP {l : ℕ} [Fact l.Prime] {x : Per.BdRp l}
    (hx : ∀ m, x ∈ Per.FilP l m) : x = 0 :=
  GlobalTheory.RingIface.ev_ext l x 0 fun m =>
    ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m x).1 (hx m)).trans (map_zero (Per.ev l m)).symm

theorem inv : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) → ∀ g : ↥(GK K), (F.ε g).map ((aDp l).comp WittVector.frobenius) * B.map (Per.σDp (g : GQ l)) = B := by
  intro l _ K bk N d ρ F B hB g
  ext i j
  rw [← sub_eq_zero]
  refine eq_of_forall_mem_FilP fun m => ?_
  obtain ⟨k, β, hβ, hb⟩ := hB m
  set σ := Per.σDp (g : GQ l) with hσ
  set Φ := (F.ε g).map ((aDp l).comp WittVector.frobenius) with hΦ
  set b : Matrix (Fin d) (Fin d) (Per.BdRp l) := β.map ((aDp l).comp bk.ev) with hbdef
  have h1 := ((GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1 _).2 (hβ.2 g i j)
  have h1' : (Φ * b.map σ - b) i j ∈ Per.FilP l m := by
    convert h1 using 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hΦ, hbdef, hσ,
      RingHom.comp_apply, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
  have h2 : ∀ x y, (l : Per.BdRp l) ^ k * B x y - b x y ∈ Per.FilP l m := fun x y => by
    have := (Ideal.neg_mem_iff _).2 (hb x y)
    simpa [hbdef, neg_sub] using this
  have key : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) =
      (Φ * b.map σ - b) i j + ∑ x, Φ i x * σ ((l : Per.BdRp l) ^ k * B x j - b x j) +
        (b i j - (l : Per.BdRp l) ^ k * B i j) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub, map_mul, map_pow, map_natCast,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have e : ∑ x, Φ i x * ((l : Per.BdRp l) ^ k * σ (B x j)) = ∑ x, (l : Per.BdRp l) ^ k * (Φ i x * σ (B x j)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    ring
  have h3 : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) ∈ Per.FilP l m := by
    rw [key]
    refine Ideal.add_mem _ (Ideal.add_mem _ h1' (Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_)) (by simpa [hbdef] using hb i j)
    exact σDp_mem_FilP _ m (h2 x j)
  obtain ⟨u, hu⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow k).exists_left_inv
  have := Ideal.mul_mem_left _ u h3
  rwa [← mul_assoc, hu, one_mul] at this

end GlobalTheory.BKLim.BinfInv
