import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemLoc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem algebraMap_adic_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (f : D.host.F) :
    algebraMap D.host.F (v.adicCompletion D.host.F) f = (f : v.adicCompletion D.host.F) := rfl

theorem isIntegral_star (x : 𝓞 D.host.E) : IsIntegral ℤ (star (x : D.host.E)) := (NumberField.RingOfIntegers.isIntegral_coe x).map (starRingEnd D.host.E).toIntAlgHom

def starO (x : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨star (x : D.host.E), isIntegral_star x⟩

theorem coe_starO (x : 𝓞 D.host.E) : ((starO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem fixed_int (y : 𝓞 D.host.E) (hy : star (y : D.host.E) = y) :
    ∃ f : 𝓞 D.host.F, algebraMap D.host.F D.host.E (f : D.host.F) = (y : D.host.E) := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hmem : (y : D.host.E) ∈ NumberField.maximalRealSubfield D.host.E := by
    rw [NumberField.mem_maximalRealSubfield_iff]
    intro φ
    have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ (y : D.host.E)
    have hs : (NumberField.IsCMField.complexConj D.host.E) (y : D.host.E) = y := hy
    rw [hs] at h
    exact h.symm
  have hint : IsIntegral ℤ (⟨(y : D.host.E), hmem⟩ : D.host.F) := by
    have h := NumberField.RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
      (IsScalarTower.toAlgHom ℤ D.host.F D.host.E : D.host.F →+* D.host.E).injective).mp h
  exact ⟨⟨⟨(y : D.host.E), hmem⟩, hint⟩, rfl⟩

theorem algebraMap_O (f : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (f : D.host.F) := rfl

theorem split_datum (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) :
    ∃ (b : 𝓞 D.host.E) (t N : 𝓞 D.host.F), b ∈ P.asIdeal ∧ starO b ∉ P.asIdeal ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = (b : D.host.E) + star (b : D.host.E) ∧
      algebraMap D.host.F D.host.E (N : D.host.F) = (b : D.host.E) * star (b : D.host.E) ∧
      t ∉ v.asIdeal ∧ N ∈ v.asIdeal := by
  have hnc : ∃ c ∈ P.asIdeal, starO c ∉ P.asIdeal := by
    by_contra hcon
    push_neg at hcon
    exact hP (fun c hc => ⟨starO c, hcon c hc, rfl⟩)
  obtain ⟨b, hbP, hbs⟩ := hnc
  obtain ⟨t, ht⟩ := fixed_int (b + starO b) (by simp [coe_starO, add_comm])
  obtain ⟨N, hN⟩ := fixed_int (b * starO b) (by simp [coe_starO, mul_comm])
  have htO : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = b + starO b :=
    NumberField.RingOfIntegers.ext (by rw [algebraMap_O, ht])
  have hNO : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) N = b * starO b :=
    NumberField.RingOfIntegers.ext (by rw [algebraMap_O, hN])
  refine ⟨b, t, N, hbP, hbs, ?_, ?_, ?_, ?_⟩
  · rw [ht]; simp [coe_starO]
  · rw [hN]; simp [coe_starO]
  · rw [← hv, Ideal.mem_comap, htO]
    intro hmem
    apply hbs
    have h2 := P.asIdeal.sub_mem hmem hbP
    simpa using h2
  · rw [← hv, Ideal.mem_comap, hNO]
    exact P.asIdeal.mul_mem_right _ hbP

instance finiteFE : Module.Finite D.host.F D.host.E :=
  Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)

set_option synthInstance.maxHeartbeats 200000 in

theorem emb_exists (v : HeightOneSpectrum (𝓞 D.host.F)) (b : D.host.E) (t N : D.host.F)
    (ht : algebraMap D.host.F D.host.E t = b + star b) (hN : algebraMap D.host.F D.host.E N = b * star b)
    (hb : star b ≠ b) (r₁ : v.adicCompletion D.host.F)
    (hr : r₁ ^ 2 - (t : v.adicCompletion D.host.F) * r₁ + (N : v.adicCompletion D.host.F) = 0) :
    ∃ ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F, ι b = r₁ ∧ Algebra.adjoin D.host.F {b} = ⊤ := by
  classical
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfix : ∀ x : D.host.E, star x = x → ∃ f : D.host.F, algebraMap D.host.F D.host.E f = x := by
    intro x hx
    have hmem : x ∈ NumberField.maximalRealSubfield D.host.E := by
      rw [NumberField.mem_maximalRealSubfield_iff]
      intro φ
      have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
      have hs : (NumberField.IsCMField.complexConj D.host.E) x = x := hx
      rw [hs] at h
      exact h.symm
    exact ⟨⟨x, hmem⟩, rfl⟩
  have hbb : b - star b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  let P : Polynomial D.host.F := X ^ 2 - C t * X + C N
  have hPm : P.Monic := by simp only [P]; monicity!
  have hPd : P.natDegree = 2 := by simp only [P]; compute_degree!
  have hPb : Polynomial.aeval b P = 0 := by
    simp only [P, map_add, map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, ht, hN]
    ring
  have hint : IsIntegral D.host.F b := ⟨P, hPm, hPb⟩
  have hsb : star b = algebraMap D.host.F D.host.E t - b := by rw [ht]; ring
  have htop : IntermediateField.adjoin D.host.F {b} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨f1, hf1⟩ := hfix (x + star x) (by rw [star_add, star_star, add_comm])
    obtain ⟨f2, hf2⟩ := hfix ((x - star x) / (b - star b)) (by
      rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub x, ← neg_sub b, neg_div_neg_eq])
    have hxe : x = (algebraMap D.host.F D.host.E f1 + algebraMap D.host.F D.host.E f2 * (b - star b)) / 2 := by
      rw [hf1, hf2]
      field_simp
      ring
    have hbm : b ∈ IntermediateField.adjoin D.host.F {b} := IntermediateField.mem_adjoin_simple_self _ b
    have hsbm : star b ∈ IntermediateField.adjoin D.host.F {b} := by
      rw [hsb]
      exact sub_mem (IntermediateField.algebraMap_mem _ t) hbm
    have h2 : (2 : D.host.E) ∈ IntermediateField.adjoin D.host.F {b} := by
      rw [show (2 : D.host.E) = 1 + 1 by norm_num]
      exact add_mem (one_mem _) (one_mem _)
    rw [hxe]
    exact div_mem (add_mem (IntermediateField.algebraMap_mem _ f1)
      (mul_mem (IntermediateField.algebraMap_mem _ f2) (sub_mem hbm hsbm))) h2
  have hnotF : b ∉ (algebraMap D.host.F D.host.E).range := by
    rintro ⟨f, hf⟩
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    apply hb
    apply φ.injective
    have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ b
    have h2 := (NumberField.mem_maximalRealSubfield_iff _).mp f.2 φ
    have hs : star b = (NumberField.IsCMField.complexConj D.host.E) b := rfl
    rw [hs, h, ← hf]
    exact h2
  have hmin : minpoly D.host.F b = P := by
    have hdvd : minpoly D.host.F b ∣ P := minpoly.dvd D.host.F b hPb
    have hdeg : 2 ≤ (minpoly D.host.F b).natDegree := by
      have h0 := minpoly.natDegree_pos hint
      have h1 : (minpoly D.host.F b).natDegree ≠ 1 := fun h => hnotF (minpoly.natDegree_eq_one_iff.mp h)
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm hdvd (by omega)).symm
  let pb := IntermediateField.adjoin.powerBasis hint
  have hr' : Polynomial.aeval r₁ (minpoly D.host.F pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin]
    simp only [P, map_add, map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hr
  let ι0 := pb.lift r₁ hr'
  refine ⟨ι0.comp ((IntermediateField.equivOfEq htop).symm.toAlgHom.comp
    (IntermediateField.topEquiv (F := D.host.F) (E := D.host.E)).symm.toAlgHom), ?_, ?_⟩
  · have hg : ((IntermediateField.equivOfEq htop).symm
        ((IntermediateField.topEquiv (F := D.host.F) (E := D.host.E)).symm b)) = pb.gen := by
      rw [IntermediateField.adjoin.powerBasis_gen]
      rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    erw [hg]
    exact pb.lift_gen r₁ hr'
  · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop, IntermediateField.top_toSubalgebra]

end Glob

section Elt

variable {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F))

def phiE (a : v.adicCompletion D.host.F) : AE D := algebraMap (AF D.host.F) (AE D) (sA v a)

theorem phiE_mul (a b : v.adicCompletion D.host.F) : phiE v (a * b) = phiE v a * phiE v b := by
  simp only [phiE, map_mul]

theorem phiE_add (a b : v.adicCompletion D.host.F) : phiE v (a + b) = phiE v a + phiE v b := by
  simp only [phiE, map_add]

theorem phiE_sub (a b : v.adicCompletion D.host.F) : phiE v (a - b) = phiE v a - phiE v b := by
  simp only [phiE, map_sub]

theorem phiE_zero : phiE v (0 : v.adicCompletion D.host.F) = 0 := by
  simp only [phiE, map_zero]

theorem phiE_smul (f : D.host.F) (a : v.adicCompletion D.host.F) :
    algebraMap D.host.F (AE D) f * phiE v a = phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f * a) := by
  unfold phiE
  rw [← sA_smul, map_mul, ← IsScalarTower.algebraMap_apply]

theorem cA_phiE (a : v.adicCompletion D.host.F) : cA D (phiE v a) = phiE v a := by
  unfold phiE cA
  first
    | exact AlgHom.commutes _ _
    | exact AlgEquiv.commutes _ _
    | simp [sigR]

theorem cA_incA (w : D.host.E) : cA D (incA D w) = incA D (star w) := by
  unfold cA incA
  simp [sigR, inclR]
  rfl

theorem incA_alg (f : D.host.F) : incA D (algebraMap D.host.F D.host.E f) = algebraMap D.host.F (AE D) f := by
  unfold incA
  first
    | exact AlgHom.commutes _ _
    | simp [inclR]

def compV (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) :
    Af D.host.F ⊗[D.host.F] D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F :=
  Algebra.TensorProduct.lift (evalV D.host.F v) ι (fun _ _ => Commute.all _ _)

theorem compV_phiE (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (a : v.adicCompletion D.host.F) :
    compV v ι (finPart D (phiE v a)) = a := by
  have h1 : algebraMap (AF D.host.F) (AE D) (sA v a) = sA v a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  simp only [compV, phiE, finPart, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  exact sglV_same v a

theorem compV_incA (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (w : D.host.E) :
    compV v ι (finPart D (incA D w)) = ι w := by
  unfold compV incA
  simp [inclR, finPart]

theorem val_emb_le (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (x : 𝓞 D.host.E) :
    Valued.v (ι (x : D.host.E)) ≤ 1 := by
  have hx : IsIntegral ℤ (ι (x : D.host.E)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) (ι : D.host.E →+* v.adicCompletion D.host.F)
      (RingHom.ext_int _ _) (NumberField.RingOfIntegers.isIntegral_coe x)
  have h2 : IsIntegral (v.adicCompletionIntegers D.host.F) (ι (x : D.host.E)) := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

theorem compV_int (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : Valued.v (compV v ι z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    simp only [compV, Algebra.TensorProduct.lift_tmul]
    rw [Valuation.map_mul]
    exact mul_le_one' (ha v) (val_emb_le v ι x)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le hy hz)
  | neg y _ hy => rwa [map_neg, Valuation.map_neg]

end Elt

end Formalism.IndefR.Fin

end
