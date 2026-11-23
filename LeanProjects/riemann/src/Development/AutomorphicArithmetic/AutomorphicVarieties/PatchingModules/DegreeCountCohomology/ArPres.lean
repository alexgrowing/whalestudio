import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumDegF
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DecSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CcAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

private theorem l_not_mem_base_prime (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    exact Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private def plF (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) : Vl l L ⊕ s.St ⊕ Option (Fin q) → Plc (Lp L)
  | .inl u => u.1
  | .inr (.inl u) => u.1
  | .inr (.inr none) => s.v0
  | .inr (.inr (some j)) => v j

private theorem plF_l (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hn : ∀ j, v j ∉ s.S) (w) :
    ((l : ℕ) : 𝓞 (Lp L)) ∈ (plF s v w).asIdeal ↔ ∃ u, w = .inl u := by
  rcases w with u | u | _ | j
  · exact iff_of_true u.2 ⟨u, rfl⟩
  · exact iff_of_false (s.St_l u.1 u.2) (by simp)
  · exact iff_of_false (l_not_mem_base_prime s) (by simp)
  · exact iff_of_false (fun h => hn j (Or.inl h)) (by simp)

private theorem plF_inj (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hi : Function.Injective v)
    (hn : ∀ j, v j ∉ s.S) : Function.Injective (plF s v) := by
  have key : ∀ (u : Vl l L) w, plF s v (.inl u) = plF s v (.inr w) → False := fun u w h => by
    have := (plF_l s v hn (.inr w)).1 (h ▸ u.2)
    simp at this
  rintro (a | a) (b | b) h
  · exact congrArg _ (Subtype.ext h)
  · exact (key _ _ h).elim
  · exact (key _ _ h.symm).elim
  · rcases a with a | _ | a <;> rcases b with b | _ | b <;> simp only [plF] at h
    · rw [Subtype.ext h]
    · exact (s.v0_St (h ▸ a.2)).elim
    · exact (hn b (h ▸ Or.inr (Or.inl a.2))).elim
    · exact (s.v0_St (h ▸ b.2)).elim
    · rfl
    · exact (hn b (Or.inr (Or.inr h.symm))).elim
    · exact (hn a (h ▸ Or.inr (Or.inl b.2))).elim
    · exact (hn a (Or.inr (Or.inr h))).elim
    · rw [hi h]

private theorem plF_range (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) :
    Set.range (plF s v) = s.S ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨u | u | _ | j, rfl⟩
    · exact Or.inl (Or.inl u.2)
    · exact Or.inl (Or.inr (Or.inl u.2))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr ⟨j, rfl⟩
  · rintro ((h | h | h) | ⟨j, h⟩)
    · exact ⟨.inl ⟨x, h⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨x, h⟩), rfl⟩
    · exact ⟨.inr (.inr none), h.symm⟩
    · exact ⟨.inr (.inr (some j)), h⟩

private def vaF (s : HidaSetting l L Ω) {q : ℕ} (B : Fin q → ValuationSubring Ω) :
    Vl l L ⊕ s.St ⊕ Option (Fin q) → ValuationSubring Ω
  | .inl u => s.A u.1
  | .inr (.inl u) => s.A u.1
  | .inr (.inr o) => o.elim (s.A s.v0) B

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.arPres :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T), V0.S' = s.S → ∀ N, ∃ (a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L))) (_ : ArPres a (Lp L) Ω), (∀ v : Vl l L, a.dv v = locDeg v.1) ∧ (((T.h N).p₀).comp (a.φq none)).range = V0.frame.D0 ∧ ∀ j, T.ph N j ∈ (a.φq (some j)).range ∧ T.ta N j ∈ (a.φq (some j)).range := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P _ N
  classical
  obtain ⟨hex, hcc⟩ := ccEx l L Ω
  choose c hc using hex
  have hc' : ∀ w, ∃ j : Ω →+* ℂ, ∀ x, j (c w x) = starRingEnd ℂ (j x) := fun w => by
    obtain ⟨j, h, -⟩ := hc w
    exact ⟨j, h⟩
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let ip : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  have hε : ∀ g, (T.GN N).ε ((P.e N).p (toGS Ω (P.V N).S' g)) = cycZ (Lp L) Ω l g := fun g =>
    ((P.e N).ε _).trans (DFunLike.congr_fun (P.V N).hε g)
  let a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L)) :=
    { Dq := fun o => Dec (F := L) (vaF s (P.B N) (.inr (.inr o)))
      cpt := fun o => isCompact_iff_compactSpace.1 (isClosed_Dec (F := L) _).isCompact
      φq := fun o => (P.e N).p₀.comp ((P.V N).pr.comp (Dec (F := L) _).subtype)
      φq_cont := fun o => ((P.e N).cont.comp
        (((continuous_toGS Ω _).comp continuous_resP).comp continuous_subtype_val)).subtype_mk _
      cw := fun i => (P.e N).p (toGS Ω (P.V N).S' (c (ip i)))
      cw_sq := fun i => (map_mul (P.e N).p _ _).symm.trans
        ((congrArg (P.e N).p ((map_mul (toGS Ω (P.V N).S') _ _).symm.trans
          (by rw [(hcc _ (hc' _)).1, map_one]; rfl))).trans (map_one (P.e N).p))
      cw_η := fun i => ((P.e N).η _).trans
        ((Int.units_eq_one_or _).resolve_left fun h => (hcc _ (hc' _)).2.1 (((P.V N).hη _).1 h))
      cw_ε := fun i => (hε _).trans (hcc _ (hc' _)).2.2
      c_ε := by
        rw [← (P.e N).c]
        exact (hε s.c).trans (hcc _ s.hc).2.2
      dv := fun v => locDeg (Subtype.val v)
      sum_dv := by
        rw [← finsum_eq_sum_of_fintype]
        exact sumDegF l (Lp L) }
  have hsp : ∀ w, Dec (F := Lp L) (vaF s (P.B N) w) ≤ (resP L Ω).range := by
    rintro (u | u | _ | j)
    · exact s.split _ (Or.inl u.2)
    · exact s.split _ (Or.inr (Or.inl u.2))
    · exact s.split _ (Or.inr (Or.inr rfl))
    · exact P.split N j
  choose α hα using fun w => decSplit L Ω _ (hsp w)
  let e0 := MulEquiv.ofBijective (P.e N).p ⟨P.e_inj N, (P.e N).surj⟩
  have ec : Continuous e0.toEquiv := (P.e N).cont
  let e : GS Ω (P.V N).S' ≃ₜ* (T.GN N).Γ :=
    { e0 with
      continuous_toFun := (P.e N).cont
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 ec).symm.continuous }
  let pl : ArData.W (locOf r) T.q ≃ (P.V N).S' :=
    (Equiv.ofInjective _ (plF_inj s (P.v N) (P.v_inj N) (P.v_not N))).trans
      (Equiv.setCongr ((plF_range s _).trans (P.S_eq N).symm))
  refine ⟨a,
    { S := (P.V N).S'
      above := fun v hv => (P.V N).sub (Or.inl hv)
      e := e
      e_ε := hε
      pl := pl
      pl_l := fun w => plF_l s (P.v N) (P.v_not N) w
      A := vaF s (P.B N)
      isOver := ?_
      α := fun w => match w with
        | .inl u => α (.inl u)
        | .inr (.inl u) => α (.inr (.inl u))
        | .inr (.inr o) => α (.inr (.inr o))
      ι_eq := ?_
      dv_eq := fun v => rfl
      ip := ip
      c := fun i => c (ip i)
      cc := fun i => hc _
      cw_eq := fun i => rfl }, fun v => rfl, ?_, fun j => ⟨⟨⟨P.fr N j, P.fr_dec N j⟩, (P.ph N j).symm⟩, ?_⟩⟩
  · rintro (u | u | _ | j)
    · exact s.hA _
    · exact s.hA _
    · exact s.hA _
    · exact P.B_v N j
  · rintro (u | u | o) g
    · exact ((P.e N).φ u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inl u) g).symm)
    · exact ((P.e N).φu u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inl u)) g).symm)
    · exact congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inr o)) g).symm
  · have : ((T.h N).p₀).comp (a.φq none) = V0.pr.comp (Dec (F := L) (s.A s.v0)).subtype :=
      MonoidHom.ext fun g => Subtype.ext (P.e_h N _)
    rw [this]
    exact (MonoidHom.range_comp _ _).trans (congrArg (Subgroup.map V0.pr) (Subgroup.range_subtype _))
  · exact ⟨⟨P.τ N j, Ine_le_Dec _ (P.τ_gen N j).1⟩, (P.ta N j).symm⟩
