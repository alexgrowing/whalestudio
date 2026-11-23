import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinQ

section Gen

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem coe_eq_algebraMap (z : K) : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

theorem valued_algebraMap (z : K) :
    Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z := by
  rw [← coe_eq_algebraMap]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

end Gen

theorem pOf_prime (v : Pl) : (pOf v).Prime := by
  rw [GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime]
  exact Fact.out

theorem coe_uniformizer (v : Pl) :
    ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = ((pOf v : ℕ) : Qv v) := by
  rw [GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime, DirichletHecke.uniformizer, IdeleGroup.coe_finiteProj_diagonal,
    RationalSymbol.coe_primeRat]
  rw [coe_eq_algebraMap, map_natCast]

theorem ord_pOf (v : Pl) : ord ((pOf v : ℕ) : Qv v) = 1 := by
  rw [← coe_uniformizer]
  exact GlobalTheory.CompanionTheory.HalfIntegral.ord_uniformizer_eq_one v

theorem residueCard_Qv (v : Pl) : residueCard (Qv v) = pOf v :=
  residueCard_adicCompletion

theorem differentIdeal_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ) (𝒪 := 𝓞 ℚ),
    Rat.numberField_discr]
  rfl

theorem isStd_local (v : Pl) : IsStd (localAdelicChar ℚ v) := by
  refine ⟨continuous_localAdelicChar v, localAdelicChar_ne_one v, ?_⟩
  rw [addCharConductor_localAdelicChar, differentExp, differentIdeal_rat, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, neg_zero]

theorem isUnit1_localChar (c : HeckeCharacter ℚ) (v : Pl) : IsUnit1 (localChar c v) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c v, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem pOf_injective : Function.Injective pOf := by
  intro v w h
  rw [GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime, GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime] at h
  exact HeightOneSpectrum.ext (by rw [DirichletHecke.asIdeal_eq_span v, DirichletHecke.asIdeal_eq_span w, h])

theorem pOf_surjective (p : ℕ) (hp : p.Prime) : ∃ v, pOf v = p :=
  ⟨RationalSymbol.placeOf ⟨p, hp⟩, by
    rw [GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime]; exact RationalSymbol.prime_placeOf ⟨p, hp⟩⟩

theorem natCast_mem_asIdeal (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pOf v ∣ n := by
  rw [DirichletHecke.asIdeal_eq_span, Ideal.mem_span_singleton, GlobalTheory.CompanionTheory.HalfIntegral.pOf_eq_prime,
    ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast, map_natCast, Int.natCast_dvd_natCast]

theorem ord_natCast_of_not_dvd (v : Pl) {m : ℕ} (h : ¬ pOf v ∣ m) : ord ((m : ℕ) : Qv v) = 0 := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at h
  have e : Valued.v ((m : ℕ) : Qv v) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) := by
    rw [← valued_algebraMap, map_natCast (algebraMap (𝓞 ℚ) ℚ)]
    exact congrArg _ (map_natCast _ m).symm
  have h0 : ((m : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [← valued_eq_one_iff_ord h0, e,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff,
    natCast_mem_asIdeal]
  exact h

theorem ord_pow_natCast (v : Pl) (p a : ℕ) (hp : p ≠ 0) :
    ord (((p : ℕ) : Qv v) ^ a) = a * ord ((p : ℕ) : Qv v) := by
  have h0 : ((p : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hp
  induction a with
  | zero => simp [ord]
  | succ n ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih]
    push_cast
    ring

theorem ord_natCast (v : Pl) (n : ℕ) (hn : n ≠ 0) :
    ord ((n : ℕ) : Qv v) = n.factorization (pOf v) := by
  have hp := pOf_prime v
  have hc : ordCompl[pOf v] n ≠ 0 := (Nat.ordCompl_pos _ hn).ne'
  have h0 : ((ordCompl[pOf v] n : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hc
  have h1 : ((pOf v : ℕ) : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n (pOf v)]
  rw [Nat.cast_mul, Nat.cast_pow, ord_mul (pow_ne_zero _ h1) h0, ord_pow_natCast v _ _ hp.ne_zero,
    ord_pOf, ord_natCast_of_not_dvd v (Nat.not_dvd_ordCompl hp hn)]
  simp

theorem finite_not_integral (g : G2) : {v : Pl | finAt v g ∉ integralGL (Qv v) 2}.Finite :=
  Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL ℚ 2 g)

theorem adelic_GL2_ext_of_local_components (g g' : G2) (h : ∀ v, finAt v g = finAt v g') (h' : ∀ w, infAt w g = infAt w g') : g = g' :=
  GroundTheory.Automorphic.Reduction.adelicGL_ext h' h

def ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1) : G2 :=
  (AdelicGLn.restrictedProductEquiv ℚ 2).symm (1, ⟨f, by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    exact hv (by rw [hf v hvS]; exact one_mem _)⟩)

theorem finAt_ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1) (v : Pl) :
    finAt v (ofFinSupp S f hf) = f v := by
  simp [finAt, ofFinSupp]

theorem infAt_ofFinSupp (S : Finset Pl) (f : ∀ v : Pl, GL (Fin 2) (Qv v)) (hf : ∀ v ∉ S, f v = 1)
    (w : InfinitePlace ℚ) : infAt w (ofFinSupp S f hf) = 1 := by
  simp [infAt, ofFinSupp]

theorem exists_isLoc2 (v : Pl) (x : GL (Fin 2) (Qv v)) : ∃ h, IsLoc2 v x h := by
  let f : ∀ u : Pl, GL (Fin 2) (Qv u) := fun u => if e : u = v then e ▸ x else 1
  have hf : ∀ u ∉ ({v} : Finset Pl), f u = 1 := fun u hu => dif_neg (by simpa using hu)
  refine ⟨ofFinSupp {v} f hf, ?_, fun u hu => ?_, fun w => infAt_ofFinSupp _ _ _ w⟩
  · rw [finAt_ofFinSupp]
    exact dif_pos rfl
  · rw [finAt_ofFinSupp]
    exact dif_neg hu

theorem exists_isUn (S : Finset Pl) (x : ∀ v : S, Qv v.1) : ∃ h, IsUn S x h := by
  let f : ∀ u : Pl, GL (Fin 2) (Qv u) := fun u => if e : u ∈ S then uni2 (x ⟨u, e⟩) else 1
  have hf : ∀ u ∉ S, f u = 1 := fun u hu => dif_neg hu
  refine ⟨ofFinSupp S f hf, fun v => ?_, fun u hu => ?_, fun w => infAt_ofFinSupp _ _ _ w⟩
  · rw [finAt_ofFinSupp]
    exact dif_pos v.2
  · rw [finAt_ofFinSupp]
    exact hf u hu

instance compactSpace_integralGL (v : Pl) : CompactSpace (integralGL (Qv v) 2) :=
  isCompact_iff_compactSpace.1 (GLnLocal.isCompact_integralGL (Qv v) 2)

theorem exists_isK : ∃ m, IsK m := by
  refine ⟨fun v => Measure.haarMeasure ⊤, fun v => ⟨inferInstance, ⟨?_⟩⟩⟩
  exact Measure.haarMeasure_self

theorem isLoc2_uni (v : Pl) (x : Qv v) : IsLoc2 v (uni2 x) (uni2 (finitePlaceIncl v x)) := by
  refine ⟨?_, fun u hu => ?_, fun w => ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply, finiteAdeleSingleAdd_apply_of_ne hu] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, finitePlaceIncl_apply] <;> rfl

theorem isLoc2_dg (v : Pl) (a d : (Qv v)ˣ) :
    IsLoc2 v (dg2 a d) (dg2 (IdeleGroup.finiteEmbedding v a) (IdeleGroup.finiteEmbedding v d)) := by
  refine ⟨?_, fun u hu => ?_, fun w => ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, IdeleGroup.finiteAdeleSingle_apply_of_ne hu] <;> rfl
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl

theorem exists_local_data (v : Pl) (x : Qv v) (a d : (Qv v)ˣ) :
    ∃ (x' : 𝔸[ℚ]) (a' d' : Jd), IsLoc2 v (uni2 x) (uni2 x') ∧ IsLoc2 v (dg2 a d) (dg2 a' d') ∧
      adelicChar ℚ x' = localAdelicChar ℚ v x ∧ (a = d → a' = d') ∧
      ∀ c : HeckeCharacter ℚ, (c.toIdele a' : ℂ) = localChar c v a ∧ (c.toIdele d' : ℂ) = localChar c v d :=
  ⟨finitePlaceIncl v x, IdeleGroup.finiteEmbedding v a, IdeleGroup.finiteEmbedding v d, isLoc2_uni v x,
    isLoc2_dg v a d, rfl, fun h => by rw [h], fun _ => ⟨rfl, rfl⟩⟩

theorem b0 : B0 :=
  ⟨fun v => ⟨isStd_local v, residueCard_Qv v, pOf_prime v, ord_pOf v, ord_natCast v, exists_isLoc2 v,
      fun c => isUnit1_localChar c v⟩,
    pOf_injective, pOf_surjective, adelic_GL2_ext_of_local_components, exists_isUn, exists_isK, finite_not_integral, exists_local_data⟩

end GlobalTheory.CompanionTheory.RankinQ
end
