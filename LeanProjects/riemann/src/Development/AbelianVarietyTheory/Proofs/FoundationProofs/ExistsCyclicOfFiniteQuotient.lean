import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open Set Filter Matrix Polynomial GlobalTheory.AdelicU NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.ClassParam (krylov exists_cyclic krylov_map)
open Formalism.UG (cT IsHerm cT_mul cT_one)
open scoped TensorProduct Topology Pointwise

noncomputable section

namespace GlobalTheory.Orb

section Integral

variable {O : Type} [CommRing O] {r : ℕ}

theorem exists_cyclic_of_finite_quotient (I : Ideal O) (hI : I ≤ (⊥ : Ideal O).jacobson) [Finite (O ⧸ I)]
    {g : Matrix (Fin r) (Fin r) O} (hg : IsRegSS g) : ∃ v, IsUnit (krylov g v).det := by
  obtain ⟨w, hw⟩ := exists_cyclic _ (hg.map (Ideal.Quotient.mk I))
  choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
  refine ⟨v, ?_⟩
  rw [show w = Ideal.Quotient.mk I ∘ v from funext fun i => (hv i).symm, ← krylov_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hw
  have := isLocalHom_of_le_jacobson_bot I hI
  exact (isUnit_map_iff _ _).1 hw

theorem exists_aeval_of_cyclic {M N : Matrix (Fin r) (Fin r) O} {v : Fin r → O} (hv : IsUnit (krylov M v).det)
    (h : Commute N M) : ∃ p : O[X], N = aeval M p := by
  let c := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : O[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ c = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [mul_krylov_of_commute h, mul_krylov_of_commute hc, hp]

theorem exists_unitary_conj_of_complete {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] [Finite (R ⧸ I)] [Algebra R O] [Module.Finite R O] {σ : O →+* O}
    (hk : ∀ c, σ (algebraMap R O c) = algebraMap R O c) (hσ : ∀ a, σ (σ a) = a) (hω : ∃ ω, IsUnit (ω - σ ω))
    {J : Matrix (Fin r) (Fin r) O} (hJ : IsHerm σ J) (hd : IsUnit J.det) {g h : Matrix (Fin r) (Fin r) O}
    (hg : cT σ g * J * g = J) (hh : cT σ h * J * h = J) (hs : IsRegSS g) (e : h.charpoly = g.charpoly) :
    ∃ u : GL (Fin r) O, cT σ u.1 * J * u.1 = J ∧ g * u = u * h := by
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I O
  have hjac := IsAdicComplete.le_jacobson_bot (I.map (algebraMap R O))
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_quotient _ hjac hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_quotient _ hjac (show IsRegSS h by rwa [IsRegSS, e])
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h := by
    have h1 := mul_krylov_eq g v
    have h2 := mul_krylov_eq h w
    rw [← ha] at h1
    rw [← hb, e] at h2
    rw [Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2,
      Units.inv_mul_cancel_left]
  generalize a * b⁻¹ = y at hy
  obtain ⟨s, hsJ⟩ : ∃ s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O, ∀ a, J * s a = cT σ a * J :=
    ⟨fun a => J⁻¹ * (cT σ a * J), fun a => mul_nonsing_inv_cancel_left _ _ hd⟩
  have hu := (isUnit_iff_isUnit_det _).2 hd
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => hu.mul_left_cancel (by
    rw [hsJ, ← mul_assoc, hsJ, mul_assoc, hsJ, cT_mul, mul_assoc])
  have hadd : ∀ a b, s (a + b) = s a + s b := fun a b => hu.mul_left_cancel (by
    rw [mul_add, hsJ, hsJ, hsJ, show cT σ (a + b) = cT σ a + cT σ b from Matrix.ext fun i j => map_add σ _ _, add_mul])
  have hcc : ∀ a : Matrix (Fin r) (Fin r) O, cT σ (cT σ a) = a := fun a => Matrix.ext fun i j => hσ _
  have hss : ∀ a, s (s a) = a := fun a => hu.mul_left_cancel (by
    have := congrArg (cT σ) (hsJ a)
    rwa [cT_mul, cT_mul, hcc, show cT σ J = J from hJ, ← hsJ] at this)
  have hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c) := fun c => hu.mul_left_cancel (by
    rw [hsJ, show cT σ (algebraMap O (Matrix (Fin r) (Fin r) O) c) = algebraMap O _ (σ c) from ?_, Algebra.commutes]
    ext i j
    simp only [cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]
    split_ifs <;> simp)
  have h1 : s 1 = 1 := by simpa using hsc 1
  have hU : ∀ u, cT σ u * J * u = J ↔ s u * u = 1 := fun u => by
    rw [← hsJ, mul_assoc, ← hu.mul_right_inj (b := s u * u), mul_one]
  rw [hU] at hg hh
  let C := Subalgebra.centralizer R ({h} : Set (Matrix (Fin r) (Fin r) O))
  have hC : ∀ {a}, a ∈ C ↔ a * h = h * a := by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]
  let _ : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun a b => Subtype.ext (by
        obtain ⟨p, hp⟩ := exists_aeval_of_cyclic hw (hC.1 a.2)
        obtain ⟨q, hq⟩ := exists_aeval_of_cyclic hw (hC.1 b.2)
        rw [C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }
  have : Module.Finite R (Matrix (Fin r) (Fin r) O) := inferInstanceAs (Module.Finite R (Fin r → Fin r → O))
  have : Module.Finite R C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I C
  have hsC : ∀ a ∈ C, s a ∈ C := fun a ha => hC.2 (by
    have h2 := congrArg s (hC.1 ha)
    rw [hm, hm] at h2
    calc s a * h = h * (s h * s a) * h := by rw [← mul_assoc, mul_eq_one_comm.1 hh, one_mul]
      _ = h * s a := by rw [h2, mul_assoc, mul_assoc, hh, mul_one])
  let t : C →+* C :=
    { toFun := fun a => ⟨s a, hsC _ a.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _)
      map_zero' := Subtype.ext (by simpa using hsc 0)
      map_add' := fun a b => Subtype.ext (hadd _ _) }
  let ι : O →+* C := (algebraMap O (Matrix (Fin r) (Fin r) O)).codRestrict C fun c => hC.2 (Algebra.commutes _ _)
  have hι : ∀ c, t (ι c) = ι (σ c) := fun c => Subtype.ext (hsc c)
  have hιR : ∀ c, algebraMap R C c = ι (algebraMap R O c) := fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply R O (Matrix (Fin r) (Fin r) O) c)
  have hl : s y * y ∈ C := hC.2 (by
    have h2 : s h * (s y * y) * h = s y * y := by
      rw [← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]
    conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])
  have hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1 := by
    rw [mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]
  have hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C := hC.2 (by
    have h2 := mul_eq_one_comm.1 hlu
    exact (Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨z, hz⟩ := GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap R C)) t (fun a => Subtype.ext (hss _))
    (fun x hx => (show I.map (algebraMap R C) ≤ (I.map (algebraMap R C)).comap t from Ideal.map_le_iff_le_comap.2
      fun c hc => by
        rw [Ideal.mem_comap, Ideal.mem_comap, hιR, hι, hk, ← hιR]
        exact Ideal.mem_map_of_mem _ hc) hx)
    ⟨ι ω, by rw [hι, ← map_sub]; exact hω.map ι⟩ ⟨_, hl'⟩ (Subtype.ext (by
      change s _ = _
      rw [hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))
  have hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O) := congrArg Subtype.val hz
  have h3 : (y * z.1) * s (y * z.1) = 1 := by
    rw [hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]
  refine ⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, (hU _).2 (mul_eq_one_comm.1 h3), ?_⟩
  change g * (y * z.1) = y * z.1 * h
  rw [← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]

end Integral

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (E) in
omit [NumberField E] in

def intLocMap (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F →+* intLoc F E v :=
  ((Algebra.TensorProduct.includeLeftRingHom (R := F) (B := E)).comp (v.adicCompletionIntegers F).subtype).codRestrict _
    fun a => tmul_mem_intLoc a.2 1

theorem finite_intLocMap (v : HeightOneSpectrum (𝓞 F)) : (intLocMap E v).Finite := by
  let _ := (intLocMap E v).toAlgebra
  let c := RingOfIntegers.basis E
  let b : _ → intLoc F E v := fun j => ⟨_, tmul_mem_intLoc (one_mem _) (c j)⟩
  refine ⟨⟨(Set.finite_range b).toFinset, eq_top_iff.2 fun y _ => ?_⟩⟩
  rw [Set.Finite.coe_toFinset]
  suffices h : ∃ z ∈ Submodule.span (v.adicCompletionIntegers F) (range b), z.1 = y.1 by
    obtain ⟨z, hz, e⟩ := h
    exact Subtype.ext e ▸ hz
  refine intLoc_induction (p := fun y => ∃ z ∈ Submodule.span (v.adicCompletionIntegers F) (range b), z.1 = y)
    (fun a ha x => ?_) ⟨0, zero_mem _, rfl⟩ ?_ ?_ y.2
  · refine ⟨∑ j, c.repr x j • (⟨a, ha⟩ : v.adicCompletionIntegers F) • b j,
      sum_mem fun j _ => zsmul_mem (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self j))) _, ?_⟩
    have e' : (x : E) = ∑ j, c.repr x j • (c j : E) := by
      conv_lhs => rw [← c.sum_repr x]
      simp
    rw [e', TensorProduct.tmul_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [AddSubgroupClass.coe_zsmul, TensorProduct.tmul_smul]
    congr 1
    change a ⊗ₜ[F] (1 : E) * (1 : Fv F v) ⊗ₜ[F] (c j : E) = _
    simp
  · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, neg_mem hy, rfl⟩

theorem eventually_exists_map_eq (p : E[X]) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∃ q : (intLoc F E v)[X], q.map (intLoc F E v).subtype = p.map (inclR (Fv F v)) := by
  filter_upwards [(eventually_all_finset p.support).2 fun i _ => eventually_one_tmul_mem_intLoc (F := F) (p.coeff i)]
    with v hv
  refine (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hv i hi⟩, rfl⟩
  · exact ⟨0, by rw [notMem_support_iff.1 hi, map_zero, map_zero]⟩

theorem eventually_conj_of_charpoly_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] {P : E[X]} (hP : P.Separable) :
    ∀ᶠ v in cofinite, ∀ g ∈ stabLoc σ J L v, ∀ g' ∈ stabLoc σ J L v,
      (matHom _ σ J g).1.charpoly = P.map (inclR (Fv F v)) → (matHom _ σ J g').1.charpoly = P.map (inclR (Fv F v)) →
      ∃ k ∈ stabLoc σ J L v, k⁻¹ * g * k = g' := by
  have := isLattice_stdLattice (E := E) (n := n)
  obtain ⟨a, b, hab⟩ := hP
  obtain ⟨ω, hω0, hω⟩ := exists_integer_conj_eq_neg h
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n), eventually_exists_map_eq (F := F) a,
    eventually_exists_map_eq (F := F) b, eventually_one_tmul_mem_intLoc (F := F) (2 * ω : E)⁻¹,
    eventually_one_tmul_mem_intLoc (F := F) J.det⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j)]
    with v hL ⟨a', ha⟩ ⟨b', hb⟩ hω' hdet hJv g hg g' hg' e e'
  rw [hL] at hg hg' ⊢
  let O := intLoc F E v
  let _ := (intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  let s : O →+* O := (sigR (Fv F v) σ).restrict O O fun _ => sigR_mem_intLoc σ
  have hinj : ∀ {M N : Matrix (Fin n) (Fin n) O}, M.map O.subtype = N.map O.subtype → M = N :=
    fun e => Matrix.map_injective Subtype.val_injective e
  have hU : ∀ M N : Matrix (Fin n) (Fin n) O, (cT s M * N * M).map O.subtype =
      cT (sigR (Fv F v) σ) (M.map O.subtype) * N.map O.subtype * M.map O.subtype := fun M N => by
    rw [Matrix.map_mul, Matrix.map_mul]; rfl
  let J' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hJv i j⟩
  let G : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, (mem_stabLoc_stdLattice_iff.1 hg).1 i j⟩
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, (mem_stabLoc_stdLattice_iff.1 hg').1 i j⟩
  have c1 : G.charpoly.map O.subtype = P.map (inclR (Fv F v)) := (charpoly_map _ _).symm.trans e
  have c2 : G'.charpoly.map O.subtype = P.map (inclR (Fv F v)) := (charpoly_map _ _).symm.trans e'
  have hp := Polynomial.map_injective O.subtype Subtype.val_injective
  obtain ⟨u, hu, hc⟩ : ∃ u : GL (Fin n) O, cT s u.1 * J' * u.1 = J' ∧ G * u = u * G' := by
    refine exists_unitary_conj_of_complete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (σ := s) (J := J') (g := G) (h := G') (fun c => Subtype.ext ?_) (fun y => Subtype.ext ?_)
      ⟨⟨_, tmul_mem_intLoc (one_mem _) ω⟩, IsUnit.of_mul_eq_one ⟨_, hω'⟩ (Subtype.ext ?_)⟩ (hinj ?_)
      (IsUnit.of_mul_eq_one ⟨_, hdet⟩ (Subtype.ext ?_)) (hinj ((hU G J').trans g.2)) (hinj ((hU G' J').trans g'.2))
      ⟨a', b', hp ?_⟩ (hp (c2.trans c1.symm))
    · change (c : Fv F v) ⊗ₜ[F] σ 1 = _
      rw [map_one]; rfl
    · change sigR _ σ (sigR _ σ y.1) = y.1
      induction y.1 with
      | zero => simp
      | tmul a b => simp [sigR, hσ]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    · change (inclR (Fv F v) (ω : E) - inclR (Fv F v) (σ ω)) * inclR (Fv F v) (2 * ω : E)⁻¹ = 1
      rw [← map_sub, ← map_mul, hω, sub_neg_eq_add, ← two_mul,
        mul_inv_cancel₀ (mul_ne_zero two_ne_zero (RingOfIntegers.coe_ne_zero_iff.2 hω0)), map_one]
    · ext i j
      exact congrArg ((1 : Fv F v) ⊗ₜ[F] ·) (hJ.1 i j)
    · change O.subtype J'.det * inclR (Fv F v) J.det⁻¹ = 1
      rw [RingHom.map_det, show O.subtype.mapMatrix J' = (inclR (Fv F v)).mapMatrix J from rfl, ← RingHom.map_det,
        ← map_mul, mul_inv_cancel₀ hJ.2, map_one]
    · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, c1, ha, hb, derivative_map,
        ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]
  let k : GLoc σ J v := ⟨Formalism.UG.bc O.subtype u, (hU u.1 J').symm.trans (congrArg (·.map O.subtype) hu)⟩
  refine ⟨k, mem_stabLoc_stdLattice_iff.2 ⟨fun i j => (u.1 i j).2, fun i j => (u⁻¹.1 i j).2⟩, ?_⟩
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  refine matHom_injective _ σ J (Units.ext ?_)
  have := congrArg (·.map O.subtype) hc
  simp only [Matrix.map_mul] at this
  exact this

theorem eventually_conj_mem_stabLoc (h : IsCMExt F E σ) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    ∀ᶠ v in cofinite, {x | x⁻¹ * proj σ J v (ratEmb σ J γ) * x ∈ stabLoc σ J L v} =
      (cent (proj σ J v (ratEmb σ J γ)) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)) := by
  filter_upwards [eventually_conj_of_charpoly_eq h hJ L hγ, eventually_proj_mem_stabLoc σ J L (ratEmb σ J γ)]
    with v hv hg
  have e : (matHom _ σ J (proj σ J v (ratEmb σ J γ))).1.charpoly = γ.1.1.charpoly.map (inclR (Fv F v)) := by
    rw [proj_ratEmb]; exact charpoly_map _ _
  generalize proj σ J v (ratEmb σ J γ) = g at hg e
  refine Set.ext fun x => ⟨fun hx => ?_, ?_⟩
  · obtain ⟨k, hk, hkx⟩ := hv g hg _ hx e (by rw [map_mul, map_mul, map_inv, charpoly_conj_GL, e])
    refine ⟨x * k⁻¹, mem_cent.2 ?_, k, hk, inv_mul_cancel_right x k⟩
    calc x * k⁻¹ * g = x * (k⁻¹ * g * k) * k⁻¹ := by group
      _ = _ := by rw [hkx]; group
  · rintro ⟨t, ht, k, hk, rfl⟩
    have : (t * k)⁻¹ * g * (t * k) = k⁻¹ * (t⁻¹ * (g * t)) * k := by group
    change (t * k)⁻¹ * g * (t * k) ∈ stabLoc σ J L v
    rw [this, ← mem_cent.1 ht, inv_mul_cancel_left]
    exact mul_mem (mul_mem (inv_mem hk) hg) hk

theorem eventually_forall_proj_mem (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {K : Set (GAd σ J)}
    (hK : IsCompact K) : ∀ᶠ v in cofinite, ∀ x ∈ K, proj σ J v x ∈ stabLoc σ J L v := by
  refine hK.induction_on (p := fun K => ∀ᶠ v in cofinite, ∀ x ∈ K, proj σ J v x ∈ stabLoc σ J L v) (by simp)
    (fun _ _ hs ht => ht.mono fun v hv x hx => hv x (hs hx))
    (fun _ _ hs ht => (hs.and ht).mono fun v hv x hx => hx.elim (hv.1 x) (hv.2 x)) fun x _ => ?_
  refine ⟨_, mem_nhdsWithin_of_mem_nhds (((restrGroup_GAd σ J L).isOpen_level.preimage
    (continuous_const_mul x⁻¹)).mem_nhds (by simp)), (eventually_proj_mem_stabLoc σ J L x).mono fun v hv y hy => ?_⟩
  simpa using mul_mem hv (hy v)

theorem isProperOrbit_GAd_of_local (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {γ : GAd σ J}
    (hK : ∀ᶠ v in cofinite, {x | x⁻¹ * proj σ J v γ * x ∈ stabLoc σ J L v} =
      (cent (proj σ J v γ) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)))
    (ha : ∀ w, IsProperOrbit (cent (projArch σ J w γ)) (projArch σ J w γ))
    (hf : ∀ v, IsProperOrbit (cent (proj σ J v γ)) (proj σ J v γ)) : IsProperOrbit (cent γ) γ := by
  intro K hc
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually (hK.and (eventually_forall_proj_mem L hc))
  choose A hA hA' using fun w => ha w _ (hc.image (continuous_projArch σ J w))
  choose B hB hB' using fun v => hf v _ (hc.image (continuous_proj σ J v))
  refine ⟨_, (isRestrGroup_GAd σ J L).isCompact_cyl S A B hA fun v _ => hB v, fun x hx => ?_⟩
  choose a ha1 ha2 using fun w => hA' w (projArch σ J w x) ⟨_, hx, by simp⟩
  have : ∀ v, ∃ t ∈ cent (proj σ J v γ), (v ∈ S → t * proj σ J v x ∈ B v) ∧
      (v ∉ S → t * proj σ J v x ∈ stabLoc σ J L v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨t, h1, h2⟩ := hB' v (proj σ J v x) ⟨_, hx, by simp⟩
      exact ⟨t, h1, fun _ => h2, fun h => absurd hv h⟩
    · obtain ⟨t, h1, k, hk, e⟩ := (Set.ext_iff.1 (hS v hv).1 (proj σ J v x)).1 (by simpa using (hS v hv).2 _ hx)
      exact ⟨t⁻¹, inv_mem h1, fun h => absurd h hv, fun _ => by rw [← e, inv_mul_cancel_left]; exact hk⟩
  choose b hb1 hb2 hb3 using this
  obtain ⟨t, h1, h2⟩ := (restrGroup_GAd σ J L).exists_eq a b (by
    filter_upwards [S.eventually_cofinite_notMem, eventually_proj_mem_stabLoc σ J L x] with v hv hxv
    exact (Subgroup.mul_mem_cancel_right _ hxv).1 (hb3 v hv))
  refine ⟨t, mem_cent.2 (GAd_ext σ J (fun w => ?_) fun v => ?_), fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · simpa only [map_mul, h1] using mem_cent.1 (ha1 w)
  · simpa only [map_mul, h2] using mem_cent.1 (hb1 v)
  · simpa only [map_mul, h1] using ha2 w
  · simpa only [map_mul, h2] using hb2 v hv
  · simpa only [map_mul, h2] using hb3 v hv

omit [NumberField E] in

theorem isRegSS_proj_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (v : HeightOneSpectrum (𝓞 F)) :
    IsRegSS (matHom _ σ J (proj σ J v (ratEmb σ J γ))).1 := by
  rw [proj_ratEmb]; exact hγ.map (inclR _)

omit [NumberField E] in

theorem isRegSS_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsRegSS (matHom _ σ J (projArch σ J w (ratEmb σ J γ))).1 := by
  rw [projArch_ratEmb]; exact hγ.map (inclR _)

theorem isProperOrbit_ratEmb (h : IsCMExt F E σ) (hJ : IsHermND σ J) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsProperOrbit (cent (ratEmb σ J γ)) (ratEmb σ J γ) :=
  have := isLattice_stdLattice (E := E) (n := n)
  isProperOrbit_GAd_of_local (stdLattice E n) (eventually_conj_mem_stabLoc h hJ _ hγ)
    (fun w => isProperOrbit_GArch h hJ (isRegSS_projArch_ratEmb hγ w))
    fun v => isProperOrbit_GLoc h hJ (isRegSS_proj_ratEmb hγ v)

theorem regular_semisimple_adelic (h : IsCMExt F E σ) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] (γ : GRat σ J) (hγ : IsRegSS γ.1.1) :
    (∀ᶠ v in cofinite, {x | x⁻¹ * proj σ J v (ratEmb σ J γ) * x ∈ stabLoc σ J L v} =
      (cent (proj σ J v (ratEmb σ J γ)) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))) ∧
    IsProperOrbit (cent (ratEmb σ J γ)) (ratEmb σ J γ) :=
  ⟨eventually_conj_mem_stabLoc h hJ L hγ, isProperOrbit_ratEmb h hJ hγ⟩

end Points

end GlobalTheory.Orb
