import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ellC_index (l : ℕ) [hl : Fact l.Prime] (M : Type) [CommGroup M] [Finite M] :
    ∃ n : ℕ, (ellC l M).index = l ^ n := by
  have hp : IsPGroup l (M ⧸ ellC l M) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl.out.ne_one
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h1 : orderOf (x ^ l ^ e) ∣ m := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← he, pow_orderOf_eq_one])
    exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  exact IsPGroup.iff_card.1 hp

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isUnit_iff_val (p : 𝒪[k]) : IsUnit p ↔ valuation k (p : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

private theorem unif_of_ord {x : kˣ} (hx : ord k x = 1) : IsUnif x := by
  have hv : valuation k (x : k) = uniformizer k := by
    obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact uniformizer_ne_zero hy.symm
    have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
    have h2 := ord_mul k (x * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right, hx, h1] at h2
    have h3 := ord_eq_zero_iff.1 (show ord k (x * (Units.mk0 y hy0)⁻¹) = 0 by omega)
    have h4 : (x : k) = ((x * (Units.mk0 y hy0)⁻¹ : kˣ) : k) * y := by simp [hy0]
    rw [h4, map_mul, h3, one_mul, hy]
  have hlt : valuation k (x : k) < 1 := hv ▸ uniformizer_lt_one
  refine ⟨⟨x, hlt.le⟩, ⟨fun h => hlt.ne ((isUnit_iff_val _).1 h), fun a b hab => ?_⟩, rfl⟩
  by_contra hn
  rw [not_or, isUnit_iff_val, isUnit_iff_val] at hn
  have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 hn.1
  have hb : valuation k (b : k) ≤ uniformizer k := le_uniformizer_iff.2 (lt_of_le_of_ne b.2 hn.2)
  have h5 : valuation k (x : k) = valuation k (a : k) * valuation k (b : k) := by
    rw [← map_mul]; exact congrArg (fun z : 𝒪[k] => valuation k (z : k)) hab
  have h6 : valuation k (a : k) * valuation k (b : k) < 1 * uniformizer k :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hb zero_le' (zero_lt_iff.2 uniformizer_ne_zero)
  rw [← h5, hv, one_mul] at h6
  exact lt_irrefl _ h6

private theorem exists_lift {H : Type} [Group H] [TopologicalSpace H] (f : H →* kˣ) (hf : Continuous f)
    (h1 : ∀ s, valuation k (f s : k) = 1) :
    ∃ g : H →* 𝒪[k]ˣ, (∀ s, Units.map (algebraMap 𝒪[k] k).toMonoidHom (g s) = f s) ∧
      IsOpen (((Units.map (residue 𝒪[k]).toMonoidHom).comp g).ker : Set H) := by
  let g0 : H →* 𝒪[k] :=
    { toFun := fun s => ⟨f s, (h1 s).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  refine ⟨g0.toHomUnits, fun s => Units.ext rfl, ?_⟩
  have e : (((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker : Set H) =
      (fun s => (f s : k) - 1) ⁻¹' {x : k | valuation k x < 1} := by
    ext s
    have e1 : (s ∈ ((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker) ↔ residue 𝒪[k] (g0 s - 1) = 0 := by
      rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]; rfl
    rw [SetLike.mem_coe, e1, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_val]
    exact ⟨fun h => lt_of_le_of_ne (g0 s - 1).2 h, fun h => ne_of_lt h⟩
  rw [e]
  refine IsOpen.preimage ((Units.continuous_val.comp hf).sub continuous_const) ?_
  simpa using IsValuativeTopology.isOpen_ball (R := k) 1

end Loc

theorem UpperTheory.V.Pa.Lev.artinEl :
    GlobalTheory.Published.TameLocal → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ), IsLocalArtin hB a → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ (h1 : fr ∈ Weil hB) (h2 : τ ∈ Weil hB), IsUnif (a ⟨fr, h1⟩) ∧ IsGenMod _ (ellC l _) (a ⟨τ, h2⟩) ∧ (∀ (σ : G E Ω) (h3 : σ ∈ Weil hB), σ ∈ GlobalTheory.TameQuot.ineKer E Bq l → a ⟨σ, h3⟩ ∈ unitsC _ (ellC l _)) ∧ (τ ^ normV w)⁻¹ * (fr⁻¹ * τ * fr) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
  intro hT l _ E Ω _ _ _ _ _ Bq w hB hl a ha fr τ hfr hF hτ
  have h0 : fr⁻¹ ∈ Weil hB := mem_Weil_of_isFrob hB hF
  have h1 : fr ∈ Weil hB := (inv_mem_iff (H := Weil hB)).1 h0
  have hval : ∀ s : Ine (F := E) Bq,
      valuation (w.adicCompletion E) ((a.comp (ineIncl hB) s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := fun s => by
    refine ord_eq_zero_iff.1 ?_
    rw [MonoidHom.comp_apply, ha.ord_eq, deg_eq_zero_iff.2 s.2, neg_zero]
  obtain ⟨g, hg, hop⟩ := exists_lift (a.comp (ineIncl hB)) ha.cont hval
  set r := (Units.map (residue 𝒪[w.adicCompletion E]).toMonoidHom).comp g with hr
  have hrs : Function.Surjective r := fun y => by
    obtain ⟨d, rfl⟩ := surjective_units_map_of_local_ringHom (residue 𝒪[w.adicCompletion E]) residue_surjective
      inferInstance y
    obtain ⟨s, hs⟩ := ha.surj (Units.map (algebraMap 𝒪[w.adicCompletion E] (w.adicCompletion E)).toMonoidHom d)
    have hs0 : deg s = 0 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_zero ((isUnit_iff_val _).1 d.isUnit)] at this
      omega
    refine ⟨⟨s, deg_eq_zero_iff.1 hs0⟩, ?_⟩
    have h5 := (hg ⟨s, deg_eq_zero_iff.1 hs0⟩).trans hs
    have h6 : g ⟨s, deg_eq_zero_iff.1 hs0⟩ = d := Units.ext (Subtype.ext (congrArg Units.val h5))
    rw [hr, MonoidHom.comp_apply, h6]
  have hopen : ∀ C : Subgroup 𝓀[w.adicCompletion E]ˣ, IsOpen ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) :=
    fun C => Subgroup.isOpen_mono (fun s hs => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hs]; exact C.one_mem) hop
  have hker : GlobalTheory.TameQuot.proKer l (Ine (F := E) Bq) ≤ (ellC l _).comap r := fun s hs =>
    GlobalTheory.TameQuot.mem_proKer.1 hs _ inferInstance (hopen _) (by
      rw [Subgroup.index_comap_of_surjective _ hrs]; exact ellC_index l _)
  refine ⟨resCard_eq_normV _, h1, Ine_le_Weil hB hτ.1, unif_of_ord ?_, ⟨g ⟨τ, hτ.1⟩, hg _, ?_⟩, fun σ h3 hσ => ?_, ?_⟩
  · have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
    rw [ha.ord_eq, ← deg_inv, h2]
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, rfl⟩ := hrs y
    set C := Subgroup.zpowers (r ⟨τ, hτ.1⟩) ⊔ ellC l _ with hC
    have hle : Subgroup.zpowers τ ⊔ GlobalTheory.TameQuot.ineKer E Bq l ≤ (C.comap r).map (Ine (F := E) Bq).subtype := by
      refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨τ, hτ.1⟩, ?_, rfl⟩) (Subgroup.map_mono (hker.trans ?_))
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.comap_mono le_sup_right
    have h4 : (s : G E Ω) ∈ closure (Subtype.val '' ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq))) :=
      closure_mono (fun z hz => hle hz) (hτ.2 s.2)
    have h5 : s ∈ closure ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) := closure_subtype.2 h4
    rw [(Subgroup.isClosed_of_isOpen _ (hopen C)).closure_eq] at h5
    exact h5
  · obtain ⟨s, hs, rfl⟩ := hσ
    exact ⟨g s, hker hs, hg s⟩
  · have hτd : τ ∈ Dec (F := E) Bq := Weil_le_Dec hB (Ine_le_Weil hB hτ.1)
    have := ((hT.1 E Ω l Bq w hB hl).2.2.2.2.2 ⟨fr⁻¹, inv_mem hfr⟩ ⟨τ, hτd⟩ hF hτ).2.1
    simpa using this
