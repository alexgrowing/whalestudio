import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) (hr : φ.range = ⊤)
    {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    (κ : H →* Eˣ) (hκ : Continuous fun g => (κ g : E)) (h0 : ∃ g, κ g ≠ 1) (h2 : ∃ g, κ g ≠ cycA l l E (φ g)) :
    finrank E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) = 2 := by
  have hρ : ∀ g x, chRep κ g x = (κ g : E) * x := fun g x => by simp [chRep]
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨f1, -, e1, e2⟩ := tateRat hP (l := l) φ hφ (chRep κ) hc
  obtain ⟨g, hg⟩ := h0
  have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
    intro m hm
    have h1 : ((κ g : E) - 1) * m = 0 := by
      rw [sub_mul, one_mul, ← hρ, hm]
    exact (mul_eq_zero.1 h1).resolve_left fun h => hg (Units.val_eq_one.1 (sub_eq_zero.1 h))
  have hH0 : ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ :=
    eq_bot_iff.2 fun m hm => hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
  have hB : finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    unfold ReciprocityTheory.Gal.B1
    rw [LinearMap.finrank_range_of_inj, finrank_self]
    rw [injective_iff_map_eq_zero]
    exact fun m hm => hz m (congrFun hm g)
  have hD : H0dual ((cycA l l E).comp φ) (chRep κ) = ⊥ := by
    obtain ⟨s, hs⟩ := h2
    refine eq_bot_iff.2 fun F hF => LinearMap.ext fun x => ?_
    have h1 := hF s x
    rw [hρ, ← smul_eq_mul, map_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left fun h => hs (Units.ext (sub_eq_zero.1 h))
  have hBZ : ReciprocityTheory.Gal.B1 (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · show Continuous fun g => chRep κ g m - m
      simp only [hρ]
      exact (hκ.mul continuous_const).sub continuous_const
    · simp only [amitsur_d0_apply, hρ, map_mul κ, Units.val_mul]
      ring
  have eB := Submodule.comapSubtypeEquivOfLe hBZ
  rw [hD, finrank_bot] at e2
  rw [hH0, finrank_bot, e2, if_pos rfl, hr, Subgroup.index_top, finrank_self] at e1
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := finite_of_finrank_pos (by omega)
  haveI := Module.Finite.equiv eB.symm
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) :=
    Module.Finite.of_submodule_quotient ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  have e3 := Submodule.finrank_quotient_add_finrank
    ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  rw [eB.finrank_eq, hB, e1] at e3
  omega

private theorem dec_iso {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ φ : ↥(Dec (F := ℚ) A) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧ φ.range = ⊤ ∧
      ∀ g, cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω) := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).1 A w hAw hw
  obtain ⟨-, φ, h1, -, h3, -, h5, -⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j
  exact ⟨φ, h1, eq_top_iff.2 fun σ _ => (h3 σ).2 fun x => by simp, h5 l⟩

theorem UpperTheory.exists_finrank_two_cocycles_char_ratio :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (a b : Fin 4), a < b → ∃ T : Submodule E (D.Gp l → E), (∀ z, z ∈ T ↔ QCont l z ∧ ∀ g h : D.Gp l, z (g * h) = z g + algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) * z h) ∧ finrank E ↥T = 2 := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ a b hab
  obtain ⟨-, F2, -, F4, -, -, F7, -, -, -, LargeParameterEstimates, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  obtain ⟨φ, hφ, hr, hcy⟩ := dec_iso l (D.pl l) (hD.pl_over l Fact.out)
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hinj : Function.Injective (algebraMap c.O E) := IsFractionRing.injective _ _
  let f : (c.O)ˣ →* Eˣ := Units.map (algebraMap c.O E : c.O →* E)
  have hf : Function.Injective f := Units.map_injective hinj
  let κ : D.Gp l →* Eˣ := f.comp ((D.ps a * (D.ps b)⁻¹).comp (D.Gp l).subtype)
  have hκ : ∀ g : D.Gp l, κ g = f (D.ps a g * (D.ps b g)⁻¹) := fun _ => rfl
  have hps : ∀ i, Continuous fun g : G ℚ Ω => algebraMap c.O E (D.ps i g : c.O) := fun i =>
    (ptCont (l := l) (O := c.O) c.O E (Algebra.ofId c.O E)).1 _ _ (LargeParameterEstimates i)
  have hκc : Continuous fun g => (κ g : E) := by
    have : (fun g => (κ g : E)) = fun g : D.Gp l =>
        algebraMap c.O E (D.ps a g : c.O) * algebraMap c.O E (D.ps b (g : G ℚ Ω)⁻¹ : c.O) := funext fun g => by
      rw [hκ, map_inv (D.ps b), ← map_mul]
      rfl
    rw [this]
    exact ((hps a).comp continuous_subtype_val).mul ((hps b).comp (continuous_subtype_val.inv))
  have hce : ∀ g : D.Gp l, cycA l l E (φ g) = f (chiO ℚ Ω l c.O g) := fun g => Units.ext (by
    show algebraMap ℤ_[l] E (cyc l l (φ g) : ℤ_[l]ˣ) = algebraMap c.O E (algebraMap ℤ_[l] c.O (cycZ ℚ Ω l g : ℤ_[l]ˣ))
    rw [hcy, ← IsScalarTower.algebraMap_apply])
  have hord : ¬ IsOfFinOrder (chiO ℚ Ω l c.O D.s0) := by
    have hi : Function.Injective (algebraMap ℤ_[l] c.O) := by
      refine Function.Injective.of_comp (f := algebraMap c.O E) ?_
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    exact fun h => hD.decompSigma_ord ((Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hi).isOfFinOrder_iff.1 h)
  refine ⟨ReciprocityTheory.Gal.Z1 (chRep κ), fun z => Iff.rfl, finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc hP φ hφ hr κ hκc ⟨D.s0, fun h => ?_⟩ ?_⟩
  · rw [hκ, map_eq_one_iff f hf, mul_inv_eq_one] at h
    exact hab.ne (F7 (congrArg Units.val h))
  · by_cases hl : lamW a = lamW b
    · refine ⟨D.s0, fun h => ?_⟩
      rw [hκ, hce] at h
      have h1 := hf h
      rw [F4 a _ hD.decompSigma_mem, F4 b _ hD.decompSigma_mem, mul_inv_eq_iff_eq_mul, ← pow_succ'] at h1
      have h2 := injective_pow_iff_not_isOfFinOrder.2 hord h1
      have := hD.two_le
      fin_cases a <;> fin_cases b <;> simp [lamW, Raw.wts4] at hab hl h2 <;> omega
    · obtain ⟨h1, -, h3⟩ := F2 l (Finset.mem_insert_self _ _)
      refine ⟨⟨D.sg l, h1⟩, fun h => h3 a b hl ?_⟩
      rw [hκ, hce] at h
      have h4 : D.ps a (D.sg l) * (D.ps b (D.sg l))⁻¹ = 1 := (hf h).trans (by
        show Units.map _ (cycZ ℚ Ω l (D.sg l)) = 1
        rw [hD.sg_cyc, map_one])
      rw [mul_inv_eq_one] at h4
      exact congrArg (fun x : c.Oˣ => residue c.O (x : c.O)) h4
