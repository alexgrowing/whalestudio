import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TotPosSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embReal_algebraMap {w : InfinitePlace F} (hw : w.IsReal) (t : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion t) =
      InfinitePlace.embedding_of_isReal hw t := by
  have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm t)
  simpa using this

theorem eta_inf_eq_one [Algebra.IsQuadraticExtension F E] {w : InfinitePlace F} (hw : w.IsReal) (t : Fˣ)
    (ht : 0 < InfinitePlace.embedding_of_isReal hw (t : F)) :
    GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
  rw [GlobalTheory.QuadSymbol.eta_eq_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff]
  set g := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set a : w.Completion := algebraMap F w.Completion (t : F)
  have hga : g a = InfinitePlace.embedding_of_isReal hw (t : F) := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, embReal_algebraMap]
  refine ⟨algebraMap w.Completion (w.Completion ⊗[F] E) (g.symm (Real.sqrt (g a))), ?_⟩
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E,
    ← map_pow, Real.sq_sqrt (hga ▸ ht.le), RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  change (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v x) =
    (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v y)
  rw [h]

theorem valued_eq_exp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem eta_inert [Algebra.IsQuadraticExtension F E] {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F) x = (-1) ^ ordL (x : v.adicCompletion F) := by
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let χ : (v.adicCompletion F)ˣ →* ℤˣ :=
    MonoidHom.mk' (GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F)) ((GlobalTheory.QuadSymbol.localCharacters F E).1 v)
  set π := atFin v (unif v)
  set k := ordL (x : v.adicCompletion F)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec v
  set u := x * π ^ (-k)
  have hu1 : IsUnitAt v u := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, valued_eq_exp x.ne_zero,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [k]
  have hx : x = u * π ^ k := by simp [u]
  have e1 : χ u = 1 := GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hu1)
  have e2 : χ π = -1 := GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
    (GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hv hu (unif_spec v))
  change χ x = _
  rw [hx, map_mul, map_zpow, e1, e2, one_mul]

end Loc

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSplit_under {w : Pl E} (h : IsSplitAt w) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  obtain ⟨u, hne, hu⟩ := h
  exact GlobalTheory.LFun.isSplit_iff.2 ⟨u, w, hne, hu, rfl⟩

theorem not_isSplit_under {w : Pl E} (h : ¬ IsSplitAt w) : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  rintro hs
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  by_cases haw : a = w
  · subst haw
    exact h ⟨b, hab.symm, hb⟩
  · exact h ⟨a, haw, ha⟩

theorem isUnram_of_unr (hU : Unr E) (v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
  GlobalTheory.LFun.isUnram_iff.2 fun P _ => by
    haveI := hU P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem neg_one_zpow_cast (k : ℤ) : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp

theorem term_eq (hU : Unr E) (w : Pl E) (t : Units ↥(maximalRealSubfield E)) :
    (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) (algebraMap ↥(maximalRealSubfield E) E t))) =
      ((GlobalTheory.QuadSymbol.eta ↥(maximalRealSubfield E) E ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))
        (GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E)))) : ℤ) : ℂ) := by
  have h2 : Module.finrank ↥(maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ↥(maximalRealSubfield E) E
  split_ifs with hs
  · rw [GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isSplit h2 (isSplit_under hs) _)]
    simp
  · rw [eta_inert (not_isSplit_under hs) (isUnram_of_unr hU _), neg_one_zpow_cast]
    congr 1
    refine ordL_congr ?_
    have hx : ((GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E))) : (w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))) =
        algebraMap ↥(maximalRealSubfield E) _ (t : ↥(maximalRealSubfield E)) := rfl
    have e := GlobalTheory.LFun.valued_complMap (F := ↥(maximalRealSubfield E)) (E := E) (w := w) rfl
      (a := algebraMap ↥(maximalRealSubfield E) ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E)) (t : ↥(maximalRealSubfield E))) (by simp)
    rw [GlobalTheory.LFun.isUnram_iff.1 (isUnram_of_unr hU _) w rfl, pow_one, GlobalTheory.LFun.complMap_algebraMap] at e
    rw [hx, e]

theorem bijOn_under {S : Set (Pl E)} (hS : IsSection S) :
    Set.BijOn (fun w : Pl E => w.under (𝓞 ↥(maximalRealSubfield E))) S Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun v _ => ?_⟩
  · obtain ⟨u, -, hu⟩ := hS a
    exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, hab.symm⟩).symm
  · obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over ↥(maximalRealSubfield E) E).2.1 v
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
    exact ⟨u, hu, hu'.trans hw⟩

end CM

end GlobalTheory.TotPosSign

namespace GlobalTheory.UnitaryClasses

open GlobalTheory.TotPosSign in

theorem signProd_totPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S →
    ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) →
    ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  intro E _ _ _ hU S hS d hd hpos
  have hmem : d ∈ maximalRealSubfield E := (mem_maximalRealSubfield_iff d).2 fun φ => by
    obtain ⟨r, -, hr⟩ := hpos φ
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  set t0 : ↥(maximalRealSubfield E) := ⟨d, hmem⟩
  have ht0 : algebraMap (↥(maximalRealSubfield E)) E t0 = d := rfl
  have ht0' : t0 ≠ 0 := fun h => hd (by rw [← ht0, h, map_zero])
  set t := Units.mk0 t0 ht0'
  have PF := GlobalTheory.QuadSymbol.productFormula (↥(maximalRealSubfield E)) E t
  have hinf : ∀ w : InfinitePlace ↥(maximalRealSubfield E),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E w.Completion (GlobalTheory.QuadSymbol.infDiag _ t w) = 1 := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    refine eta_inf_eq_one hw t ?_
    letI : Algebra (↥(maximalRealSubfield E)) ℂ := w.embedding.toAlgebra
    let τ : E →ₐ[↥(maximalRealSubfield E)] ℂ := IsAlgClosed.lift
    obtain ⟨r, hr, e⟩ := hpos τ.toRingHom
    have e2 : (InfinitePlace.embedding_of_isReal hw (t : ↥(maximalRealSubfield E)) : ℂ) = r := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← e]
      exact (τ.commutes t0).symm
    rw [Complex.ofReal_inj] at e2
    rw [e2]; exact hr
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v) = 1 := by
    have h := PF.2
    unfold GlobalTheory.QuadSymbol.etaProd at h
    rwa [Finset.prod_eq_one fun w _ => hinf w, mul_one] at h
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hd' : d = algebraMap (↥(maximalRealSubfield E)) E ((t : Units ↥(maximalRealSubfield E)) : ↥(maximalRealSubfield E)) := rfl
  rw [hd', finprod_mem_eq_of_bijOn _ (bijOn_under hS) (g := fun v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)) => cz
      (GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v))) fun w _ => term_eq hU w t,
    finprod_mem_univ, ← MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport PF.1), hfin, map_one]

end GlobalTheory.UnitaryClasses

end
