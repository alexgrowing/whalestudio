import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v (a * b) = GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b := by
  refine Prod.ext ?_ ?_
  · change (0 : Ainf F) = 0 * 0
    rw [mul_zero]
  · change GlobalTheory.AdelicU.singleFin v (a * b) = GlobalTheory.AdelicU.singleFin v a * GlobalTheory.AdelicU.singleFin v b
    exact GlobalTheory.AdelicU.singleFin_mul v a b

theorem liftV_one_mul (v : Pl F) (a : AF F) :
    GlobalTheory.LatVac.liftV v 1 * a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  refine Prod.ext ?_ ?_
  · change (0 : Ainf F) * a.1 = 0
    rw [zero_mul]
  · change GlobalTheory.AdelicU.singleFin v 1 * a.2 = GlobalTheory.AdelicU.singleFin v (evalV F v a.2)
    apply GlobalTheory.AdelicU.af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, zero_mul]

theorem evFin_one_sub (v : Pl F) : evFin F v (1 - GlobalTheory.LatVac.liftV v 1) = 0 := by
  rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]

theorem eq_liftV_of_at (v : Pl F) {a : AF F} (ha : At (evFin F v) a) :
    a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  have h := ha _ (evFin_one_sub v)
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero, liftV_one_mul] at h
  exact h

variable (E) in

def liftT (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id

theorem liftT_tmul (v : Pl F) (a : Fv F v) (e : E) :
    liftT E v (a ⊗ₜ[F] e) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] e := rfl

variable (E) in

def evT (v : Pl F) : AE F E →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)

theorem evT_liftT (v : Pl F) (y : Fv F v ⊗[F] E) : evT E v (liftT E v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [liftT_tmul]
    change evFin F v (GlobalTheory.LatVac.liftV v a) ⊗ₜ[F] e = a ⊗ₜ[F] e
    rw [GlobalTheory.LatVac.evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftT_injective (v : Pl F) : Function.Injective (liftT E v) :=
  Function.LeftInverse.injective (evT_liftT (E := E) v)

theorem liftV_one_smul (v : Pl F) (z : AE F E) : GlobalTheory.LatVac.liftV v 1 • z = liftT E v (evT E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    rfl
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

theorem at_liftT (v : Pl F) (y : Fv F v ⊗[F] E) : At (evFin F v) (liftT E v y) := by
  intro u hu
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [liftT_tmul, TensorProduct.smul_tmul', smul_eq_mul, eq_liftV_of_at v (GlobalTheory.LatVac.at_liftV v a),
      ← liftV_one_mul, ← mul_assoc, mul_comm u, liftV_one_mul, hu, map_zero, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem at_iff (v : Pl F) (z : AE F E) : At (evFin F v) z ↔ ∃ y, liftT E v y = z := by
  refine ⟨fun hz => ⟨evT E v z, ?_⟩, fun ⟨y, hy⟩ => hy ▸ at_liftT v y⟩
  have h := hz _ (evFin_one_sub v)
  rw [sub_smul, one_smul, sub_eq_zero, liftV_one_smul] at h
  exact h.symm

theorem liftT_mul (v : Pl F) (y y' : Fv F v ⊗[F] E) : liftT E v (y * y') = liftT E v y * liftT E v y' := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul a e =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => rw [mul_add, map_add, hx, hz, map_add, mul_add]
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, liftT_tmul, liftT_tmul, liftT_tmul, liftV_mul,
        Algebra.TensorProduct.tmul_mul_tmul]

theorem liftT_sigR (σ : E →ₐ[F] E) (v : Pl F) (y : Fv F v ⊗[F] E) :
    liftT E v (sigR (Fv F v) σ y) = cA σ (liftT E v y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end GlobalTheory.InertLocField

namespace GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul_base {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem liftV_mul_algebraMap (v : Pl F) (t : Fv F v) (r : F) :
    GlobalTheory.LatVac.liftV v t * algebraMap F (AF F) r = GlobalTheory.LatVac.liftV v (algebraMap F (Fv F v) r * t) := by
  rw [← Algebra.smul_def, LinearMap.map_smul, Algebra.smul_def, mul_comm]

theorem trace_liftT (v : Pl F) (y : Fv F v ⊗[F] E) :
    Algebra.trace (AF F) (AE F E) (liftT E v y) =
      GlobalTheory.LatVac.liftV v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [liftT_tmul, trace_tmul_base, trace_tmul_base, liftV_mul_algebraMap, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem trace_mem_of_mem_intLoc (v : Pl F) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F :=
  intLoc_induction (p := fun y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F)
    (fun a ha o => by
      rw [trace_tmul_base]
      refine mul_mem ha ?_
      have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem (⟨_, hi⟩ : 𝓞 F) v)
    (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
    (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem odd_absNorm_of_two_notMem (P : HeightOneSpectrum (𝓞 F)) (h : (2 : 𝓞 F) ∉ P.asIdeal) :
    Odd (Ideal.absNorm P.asIdeal) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  haveI := P.isPrime
  haveI : Finite (𝓞 F ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h2
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 F ⧸ P.asIdeal) 2 h2
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact absurd hx (by norm_num)
  have h1 : (2 : 𝓞 F ⧸ P.asIdeal) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, two_nsmul] at this
    rw [two_mul, this]
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact h (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_ofNat]; exact h3))
  · exact h0 h3

theorem half_mem (v : Pl F) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F := by
  have hval : Valued.v (algebraMap F (Fv F v) ((2 : 𝓞 F) : F)) = v.valuation F ((2 : 𝓞 F) : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have h1 : v.valuation F ((2 : 𝓞 F) : F) = 1 :=
    le_antisymm (v.valuation_le_one _) (not_lt.1 (mt (v.valuation_lt_one_iff_mem _).1 h))
  have h2 : ((2 : 𝓞 F) : F) = 2 := rfl
  rw [h2] at hval h1
  change Valued.v (algebraMap F (Fv F v) 2⁻¹) ≤ 1
  rw [map_inv₀, map_inv₀, hval, h1, inv_one]

end GlobalTheory.InertLocField

namespace GlobalTheory.InertLocField

open InertChart

theorem field_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
      (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧ (Valued.v δ = 1 ∧ σL δ = -δ) ∧
      (∀ x ∈ Formalism.UG.intL L, σL x = x → ψL x = 1) ∧ (∃ x ∈ Formalism.UG.intL L, σL x = x ∧ ψL (ϖ⁻¹ * x) ≠ 1) ∧
      Function.Injective ι ∧ (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) ∧
      (∀ x y, ι (x * y) = ι x * ι y) ∧ (∀ x, ι (σL x) = cA σ (ι x)) ∧
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) ∧
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) := by
  intro F E _ _ _ _ _ σ B hB v w hw
  have hσ := hB.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ', hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨h2v, -, hψ⟩ := hB.inert v w hw
  set L := w.adicCompletion E
  have hval : ∀ a : E, Valued.v (algebraMap E L a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _

  obtain ⟨s, hs, hs2⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.map_le_iff_le_comap.2 (not_map_le_sq hw))
  have hs1 : algebraMap (𝓞 F) (𝓞 E) s ∈ w.asIdeal := hw ▸ Ideal.mem_map_of_mem _ hs
  set ϖv : Fv F v := algebraMap F (Fv F v) (s : F) with hϖv
  set ϖ : L := complMap h ϖv with hϖ
  have hϖE : ϖ = algebraMap E L (algebraMap (𝓞 F) (𝓞 E) s : E) := complMap_algebraMap h (s : F)
  have hϖc : c ϖ = ϖ := by
    rw [hϖE, conj_algebraMap hc]
    exact congrArg _ (σ.commutes (s : F))
  have hϖval : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖE, hval, HeightOneSpectrum.valuation_of_algebraMap]
    have a := (w.intValuation_le_pow_iff_mem _ 1).2 (by rwa [pow_one])
    have b := not_le.1 (mt (w.intValuation_le_pow_iff_mem _ 2).1 hs2)
    have h0 : w.intValuation (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 := b.ne_bot
    rw [← WithZero.exp_log h0] at a b ⊢
    rw [WithZero.exp_le_exp] at a
    rw [WithZero.exp_lt_exp] at b
    congr 1
    omega
  have hU' : Formalism.UG.IsUnramInv ϖ c (Formalism.UG.qV F v) :=
    ⟨hU.1, hU.2.1, hϖc, hϖval, hU.2.2.2.2.1, hU.2.2.2.2.2.1, hU.2.2.2.2.2.2⟩
  obtain ⟨x0, -, hx0⟩ := hU.2.2.2.2.1

  let e := complEquiv hw h
  have he : ∀ y, e y = toCompl h y := fun _ => rfl
  let ι : L →+ AE F E := (liftT E v).toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hι : ∀ x, ι x = liftT E v (e.symm x) := fun _ => rfl
  let ψL : AddChar L ℂ := B.ψ.compAddMonoidHom
    ((AddMonoidHom.mulRight (algebraMap F (AF F) 2⁻¹)).comp ((Algebra.trace (AF F) (AE F E)).toAddMonoidHom.comp ι))
  have hψL : ∀ x, ψL x = B.ψ (Algebra.trace (AF F) (AE F E) (ι x) * algebraMap F (AF F) 2⁻¹) := fun _ => rfl
  have hψloc : ∀ t : Fv F v, B.ψ (GlobalTheory.LatVac.liftV v t) = psiLoc B.ψ v t := fun _ => rfl
  have hsymm : ∀ x, toCompl h (e.symm x) = x := fun x => e.apply_symm_apply x
  have hconj : ∀ x, e.symm (c x) = sigR (Fv F v) σ (e.symm x) := fun x => by
    conv_lhs => rw [← hsymm x]
    rw [hc, ← he, e.symm_apply_apply]
  have hcompl : ∀ t : Fv F v, e.symm (complMap h t) = t ⊗ₜ[F] (1 : E) := fun t => by
    rw [← e.symm_apply_apply (t ⊗ₜ[F] (1 : E)), he, toCompl_tmul, map_one, mul_one]
  have hψc : ∀ t : Fv F v, ψL (complMap h t) = psiLoc B.ψ v t := fun t => by
    rw [hψL, hι, hcompl, trace_liftT, trace_tmul_base, ← map_one (algebraMap F E), Algebra.trace_algebraMap,
      hσ.2.2.1, liftV_mul_algebraMap, hψloc]
    congr 1
    rw [nsmul_eq_mul, Nat.cast_ofNat, mul_one, mul_comm t, ← mul_assoc, ← map_mul, inv_mul_cancel₀ two_ne_zero,
      map_one, one_mul]
  have hint : ∀ x, x ∈ Formalism.UG.intL L ↔ e.symm x ∈ intLoc F E v := fun x => by
    rw [mem_intLoc_iff hw h, hsymm]
    exact Iff.rfl
  refine ⟨L, inferInstance, charZero_of_injective_algebraMap (algebraMap E L).injective, inferInstance, inferInstance,
    ϖ, c, Formalism.UG.qV F v, c x0 - x0, ψL, ι, hU', ?_, ⟨hx0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact odd_absNorm_of_two_notMem v h2v
  · rw [map_sub, hU.1, neg_sub]
  · intro x hx _
    rw [hψL, hι, trace_liftT, liftV_mul_algebraMap, hψloc]
    have hm := mul_mem (half_mem v h2v) (trace_mem_of_mem_intLoc v ((hint x).1 hx))
    simpa using (hψ _).2 hm 1 (one_mem _)
  · have hlt : Valued.v ϖv < 1 := by
      rw [hϖv, show Valued.v (algebraMap F (Fv F v) (s : F)) = v.valuation F (s : F) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _]
      exact (v.valuation_lt_one_iff_mem s).2 hs
    have hne : Valued.v ϖv ≠ 0 := fun h0 => by
      have h1 : ϖv = 0 := by simpa using h0
      have h2 := hϖval
      rw [hϖ, h1, map_zero, map_zero] at h2
      exact WithZero.exp_ne_zero h2.symm
    have hnot : ϖv⁻¹ ∉ v.adicCompletionIntegers F := fun hm => by
      have h1 : Valued.v ϖv⁻¹ ≤ 1 := hm
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hne)] at h1
      exact absurd hlt (not_lt.2 h1)
    obtain ⟨y, hyO, hyψ⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (ϖv⁻¹ * y) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ((hψ _).1 hcon)
    refine ⟨complMap h y, complMap_mem h hyO, ?_, ?_⟩
    · rw [← hsymm (complMap h y), hcompl, hc]
      show toCompl h (y ⊗ₜ[F] σ 1) = _
      rw [map_one]
    · rw [hϖ, ← map_inv₀, ← map_mul, hψc]
      exact hyψ
  · exact (liftT_injective v).comp e.symm.injective
  · intro z
    rw [at_iff]
    exact ⟨fun ⟨y, hy⟩ => ⟨e y, by rw [hι, e.symm_apply_apply, hy]⟩, fun ⟨x, hx⟩ => ⟨e.symm x, hx⟩⟩
  · intro x y
    rw [hι, hι, hι, map_mul, liftT_mul]
  · intro x
    rw [hι, hι, hconj, liftT_sigR]
  · intro x
    rw [hint, hι]
    have hincl : ∀ (a : AF F) (o : E), a • inclR (F := F) (AF F) o = a ⊗ₜ[F] o := fun a o => by
      rw [show inclR (F := F) (AF F) o = (1 : AF F) ⊗ₜ[F] o from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hS : {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)} =
        (liftT E v).toAddMonoidHom '' {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, z = a ⊗ₜ[F] (o : E)} := by
      ext z
      constructor
      · rintro ⟨a, ha, haO, o, rfl⟩
        refine ⟨evFin F v a ⊗ₜ[F] (o : E), ⟨_, haO, o, rfl⟩, ?_⟩
        rw [LinearMap.toAddMonoidHom_coe, liftT_tmul, ← eq_liftV_of_at v ha, hincl]
      · rintro ⟨y, ⟨a, haO, o, rfl⟩, rfl⟩
        refine ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rwa [GlobalTheory.LatVac.evFin_liftV], o, ?_⟩
        rw [LinearMap.toAddMonoidHom_coe, liftT_tmul, hincl]
    rw [hS, ← AddMonoidHom.map_closure]
    exact (AddSubgroup.mem_map_iff_mem (f := (liftT E v).toAddMonoidHom) (liftT_injective v)).symm
  · intro x
    have hcc : ∀ z, cA σ (cA σ z) = z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        change a ⊗ₜ[F] σ (σ b) = a ⊗ₜ[F] b
        rw [conj_conj hσ]
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    have htr : Algebra.trace (AF F) (AE F E) (ι (c x)) = Algebra.trace (AF F) (AE F E) (ι x) := by
      rw [hι, hconj, liftT_sigR, ← hι]
      exact Algebra.trace_eq_of_algEquiv cE (ι x)
    rw [hψL, map_add, map_add, htr]
    congr 1
    rw [← two_mul, mul_comm (2 : AF F), mul_assoc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul,
      mul_inv_cancel₀ two_ne_zero, map_one, mul_one]

end GlobalTheory.InertLocField
