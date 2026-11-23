import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Lemmas

variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

def chartVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (.inr ij.2) (fun i => .inl (i, ij.2)) ij.1

theorem chartVar_injective (e n : ℕ) : Function.Injective (chartVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;>
    simp_all [chartVar, Fin.cases_zero, Fin.cases_succ]

theorem parToFrac_algebraMap' (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by
  rw [parToFrac, IsLocalization.lift_eq]

theorem kToFrac_algebraMap (e n : ℕ) (a : 𝓞 K) :
    kToFrac K e n (algebraMap (𝓞 K) K a) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (C a) := by
  rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

theorem eval_specRest_chart (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    eval (fun j => parYF K e n (.inr j))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename (chartVar e n) g) := by
  have h : ((eval fun j => parYF K e n (.inr j)).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp (rename (chartVar e n)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [chartVar, parYF]
  exact congrArg (fun φ => φ g) h

theorem eval_specRest_lin (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by
  have h : ((eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp
        ((rename (Sum.inl : Fin e × Fin n → Par e n)).toRingHom.comp (bind₁ (specFirstVar u)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [specFirstVar, parYF, kToFrac_algebraMap]
  exact congrArg (fun φ => φ g) h

theorem secLin_eq_sum {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by
  simp only [secLin, linForm, map_sum, map_mul]
  rfl

theorem chart_sum_eq_one {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)}
    {y : Par e n → R} : ∑ j, algebraMap R (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  rw [← secLin_eq_sum]
  have hmem : chartForm y - 1 ∈ secIdeal Q y := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have h := Ideal.Quotient.eq.mpr hmem
  rw [map_one] at h
  exact h

end Lemmas

theorem NormIdentity.proof (hcn : ChowNormForm.Statement) (hfin : SecBFinite.Statement)
    (htf : SecBTorsionFree.Statement) (hgen : SecBGeneric.Statement)
    (hloc : NormFormLocalization.Statement) (hev : NormFormEval.Statement)
    (hai : ParAlgIndep.Statement) (hfr : ParFracIsFractionRing.Statement)
    (hdvr : ParDVRIsDVR.Statement) : NormIdentity.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  obtain ⟨φ, hφc, hφr, hφloc⟩ := hgen K n e I v hI
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I _ v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  let _iRF : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have hFR : IsFractionRing (ParDVR e n v) (ParFrac K e n) := hfr K e n v
  let _iKF : Algebra K (ParFrac K e n) := (kToFrac K e n).toAlgebra
  let _iBL : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have _t1 : IsScalarTower (ParDVR e n v) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) :=
    IsScalarTower.of_algebraMap_eq (R := ParDVR e n v) (S := SecB e I v)
      (A := SecAlg (idealF e I) (parYF K e n)) fun r => (hφr r).symm
  have hNL := hloc (ParDVR e n v) (ParFrac K e n) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) n
    (secCoord (modelR e I v) (parY e n v))
  have hxs : (fun j => algebraMap (SecB e I v) (SecAlg (idealF e I) (parYF K e n))
      (secCoord (modelR e I v) (parY e n v) j)) = secCoord (idealF e I) (parYF K e n) := funext hφc
  rw [hxs] at hNL
  obtain ⟨-, c, -, hcn'⟩ := hcn K (ParFrac K e n) n e I (g.map (algebraMap (𝓞 K) K)) (parYF K e n)
    (hai K e n) hI hf
  set P := normForm (R := ParDVR e n v) (SecB e I v) (secCoord (modelR e I v) (parY e n v)) with hP
  replace hcn' : specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n) =
      C c * P.map (algebraMap (ParDVR e n v) (ParFrac K e n)) := by
    rw [hNL]
    exact hcn'

  have hevP : ∀ z : Fin n → ParDVR e n v,
      eval (fun j => parToFrac e n v (z j)) (P.map (algebraMap (ParDVR e n v) (ParFrac K e n))) =
        parToFrac e n v (Algebra.norm (ParDVR e n v)
          (∑ j, algebraMap (ParDVR e n v) (SecB e I v) (z j) * secCoord (modelR e I v) (parY e n v) j)) := by
    intro z
    rw [eval_map, ← hev (ParDVR e n v) (SecB e I v) n _ z, ← hP]
    show eval₂ _ _ P = parToFrac e n v (eval₂ (RingHom.id _) z P)
    rw [hom_eval₂]
    rfl

  have hT := congrArg (eval fun j => parYF K e n (.inr j)) hcn'
  rw [eval_specRest_chart, map_mul, eval_C] at hT
  have hTpt : (fun j => parYF K e n (.inr j)) = fun j => parToFrac e n v (parY e n v (.inr j)) := by
    funext j
    rw [parY, parToFrac_algebraMap']
    rfl
  rw [hTpt, hevP, chart_sum_eq_one, map_one, map_one, mul_one] at hT

  have hU := congrArg (eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) hcn'
  rw [eval_specRest_lin, map_mul, eval_C] at hU
  have hUpt : (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) =
      fun j => parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) (u j)) := by
    funext j
    rw [kToFrac_algebraMap, IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), parToFrac_algebraMap']
    rfl
  rw [hUpt, hevP, ← secLin_eq_sum, ← hT, ← parToFrac_algebraMap', ← parToFrac_algebraMap', ← map_mul] at hU
  have hinj : Function.Injective (parToFrac e n v) := IsFractionRing.injective (ParDVR e n v) (ParFrac K e n)
  have hUR := hinj hU

  obtain ⟨m, hm⟩ := hprim
  have hnot : rename (chartVar e n) g ∈ (parPrime e n v).primeCompl := by
    intro hmem
    have hmem' : rename (chartVar e n) g ∈ Ideal.map C v.asIdeal := hmem
    rw [MvPolynomial.mem_map_C_iff] at hmem'
    have hmem := hmem'
    have := hmem (Finsupp.mapDomain (chartVar e n) m)
    rw [coeff_rename_mapDomain _ (chartVar_injective e n)] at this
    exact hm this
  have hunit : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (chartVar e n) g)) :=
    IsLocalization.map_units (ParDVR e n v) (⟨_, hnot⟩ : (parPrime e n v).primeCompl)
  exact ⟨hunit.unit, hUR⟩

end

end GroundTheory.Heights₂.Heights.Vertical
