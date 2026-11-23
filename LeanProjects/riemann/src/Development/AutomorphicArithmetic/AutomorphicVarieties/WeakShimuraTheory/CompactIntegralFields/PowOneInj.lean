import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem charP_res (c : Coef l) : CharP (ResidueField c.O) l := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, hloc, -, -, he, -, hval, -⟩ := dvrFacts l c.O
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hmem : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : IsDiscreteValuationRing.addVal c.O (l : c.O) = 0 :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hu
    exact he (hval.trans h0)
  have := (residue_eq_zero_iff ((l : ℕ) : c.O)).2 hmem
  simpa using this

private theorem pow_inj {x y : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = y ^ l ^ j) : x = y := by
  haveI := charP_res c
  haveI : ExpChar (ResidueField c.O) l := ExpChar.prime Fact.out
  induction j with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply frobenius_inj (ResidueField c.O) l
    simpa [frobenius_def, pow_succ, pow_mul] using h

private theorem pow_one_inj {x : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = 1) : x = 1 := by
  exact pow_inj j (by simpa using h)

private theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => g.commutes ⟨x, hx⟩

private theorem dec_resLe {F F' : IntermediateField ℚ Ω} (h : F ≤ F') (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A := Iff.rfl

private theorem ine_resLe {F F' : IntermediateField ℚ Ω} [NumberField F] [NumberField F'] (h : F ≤ F')
    (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A := Iff.rfl

variable {T T' : Tower D}

private theorem up (h : T.Le T') : ∃ j : ℕ, ∀ g : G T.F Ω, ∃ g' : G T'.F Ω, resLe h.le g' = g ^ l ^ j := by
  obtain ⟨j, hj⟩ := h.pow
  refine ⟨j, fun g => ?_⟩
  have hm := hj _ (resQ_mem T.F g)
  refine ⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, hm⟩, ?_⟩
  ext x
  simp [resLe, IntermediateField.fixingSubgroupEquiv, map_pow]

private theorem rb_resLe (h : T.Le T') (w : ℤ × ℤ) (g : G T'.F Ω) : T'.rb w g = T.rb w (resLe h.le g) := by
  simp only [Tower.rb, Tower.fr, Fr.rt, h.pr]
  rfl

private theorem rb_pow (w : ℤ × ℤ) (g : G T.F Ω) (n : ℕ) : T.rb w (g ^ n) = T.rb w g ^ n := by
  simp only [Tower.rb, map_pow, Units.val_pow_eq_pow_val]

private theorem bar_pow (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar γ (g ^ n) = Raw.bar γ g ^ n := by
  simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]

private theorem galL_resLe (h : T.Le T') (g : G T'.F Ω) : resLe h.le g ∈ T.GalL ↔ g ∈ T'.GalL := by
  simp only [Tower.GalL, Subgroup.mem_comap, h.K]
  rfl

private theorem g3'_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) (η : T'.GalL →* (ResidueField c.O)ˣ) (h2 : η ^ 2 = 1)
    (hom : ∀ g : T'.GalL, D.om (resQ T'.F g) = 1 → η g = 1)
    (hperm : ∀ i, ∃ j, ∀ g : T'.GalL, η g * Raw.bar (chi D T'.pr i) (resQ T'.F g) =
      Raw.bar (chi D T'.pr j) (resQ T'.F g)) : η = 1 := by
  obtain ⟨k, hk⟩ := up h
  have L : ∀ u : (ResidueField c.O)ˣ, u ^ l ^ k = 1 → u = 1 := fun u hu =>
    Units.ext (pow_one_inj k (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]))
  let φ : Fin 4 → T.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T.F).comp T.GalL.subtype))
  let φ' : Fin 4 → T'.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T'.F).comp T'.GalL.subtype))
  have hφ : ∀ m (g : T'.GalL), φ m ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩ = φ' m g := fun _ _ => rfl
  have hperm' : ∀ i, ∃ j, ∀ g : T'.GalL, η g * φ' i g = φ' j g := by
    intro i
    obtain ⟨j, hj⟩ := hperm i
    refine ⟨j, fun g => Units.ext ?_⟩
    have hj' := hj g
    rw [h.pr] at hj'
    simpa [φ', Raw.bar] using hj'
  have lift : ∀ g : T.GalL, ∃ g' : T'.GalL, ∀ m, φ m g ^ l ^ k = φ' m g' ∧
      (D.om (resQ T.F g) = 1 → D.om (resQ T'.F g') = 1) := by
    intro g
    obtain ⟨g', hg'⟩ := hk g
    have hm : g' ∈ T'.GalL := (galL_resLe h g').1 (by rw [hg']; exact pow_mem g.2 _)
    refine ⟨⟨g', hm⟩, fun m => ⟨?_, fun h1 => ?_⟩⟩
    · rw [← map_pow, ← hφ]
      congr 1
      exact Subtype.ext (by simp [hg'])
    · show D.om (resQ T.F (resLe h.le g')) = 1
      rw [hg', map_pow, map_pow, h1, one_pow]
  obtain ⟨j, hj⟩ := hperm' 0
  have hη : ∀ g : T'.GalL, η g = φ' j g / φ' 0 g := fun g => eq_div_iff_mul_eq'.2 (hj g)
  let η₀ : T.GalL →* (ResidueField c.O)ˣ := φ j / φ 0
  have hη₀ : ∀ g, η₀ g = φ j g / φ 0 g := fun _ => rfl
  have C : ∀ (g : T.GalL) (g' : T'.GalL), (∀ m, φ m g ^ l ^ k = φ' m g') → η₀ g ^ l ^ k = η g' := by
    intro g g' hm
    rw [hη g', ← hm j, ← hm 0, hη₀, div_pow]
  have h0 : η₀ = 1 := by
    refine ho.g3' η₀ ?_ ?_ ?_
    · refine MonoidHom.ext fun g => ?_
      obtain ⟨g', hg'⟩ := lift g
      rw [MonoidHom.one_apply, MonoidHom.pow_apply]
      apply L
      rw [← pow_mul, mul_comm, pow_mul, C g g' (fun m => (hg' m).1), ← MonoidHom.pow_apply, h2,
        MonoidHom.one_apply]
    · intro g hg
      obtain ⟨g', hg'⟩ := lift g
      apply L
      rw [C g g' (fun m => (hg' m).1)]
      exact hom g' ((hg' 0).2 hg)
    · intro i
      obtain ⟨i', hi'⟩ := hperm' i
      refine ⟨i', fun g => ?_⟩
      have key : η₀ g * φ i g = φ i' g := by
        obtain ⟨g', hg'⟩ := lift g
        have hu : η₀ g * φ i g / φ i' g = 1 := by
          apply L
          rw [div_pow, mul_pow, C g g' (fun m => (hg' m).1), (hg' i).1, (hg' i').1, hi' g', div_self']
        exact div_eq_one.1 hu
      have := congrArg Units.val key
      simpa [φ, Raw.bar] using this
  refine MonoidHom.ext fun g => ?_
  rw [hη g, MonoidHom.one_apply, div_eq_one, ← hφ, ← hφ]
  have := congrArg (fun f : T.GalL →* (ResidueField c.O)ˣ => f ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩) h0
  simp only [hη₀, MonoidHom.one_apply, div_eq_one] at this
  exact this

private theorem ok_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) : T'.Ok := by
  obtain ⟨k, hk⟩ := up h
  have L1 : ∀ x : ResidueField c.O, x ^ l ^ k = 1 → x = 1 := fun x hx => pow_one_inj k hx
  have liftL : ∀ g ∈ T.GalL, ∃ g' ∈ T'.GalL, resLe h.le g' = g ^ l ^ k := fun g hg => by
    obtain ⟨g', hg'⟩ := hk g
    exact ⟨g', (galL_resLe h g').1 (by rw [hg']; exact pow_mem hg _), hg'⟩
  refine
    { lab := ?_, even := ?_, unr := ?_, split := ?_, g2 := ?_, g3 := ?_, g3' := ?_, ord := ?_,
      kb := ?_, kc := ?_, ineL := ?_, dist := ?_, locL := ?_ }
  · rw [h.pr]
    exact ho.lab
  · obtain ⟨n, hn⟩ := IntermediateField.finrank_dvd_of_le_right h.le
    show Even (Module.finrank ℚ T'.F)
    rw [hn]
    exact (show Even (Module.finrank ℚ T.F) from ho.even).mul_right n
  · intro A g hg
    exact (galL_resLe h g).1 (ho.unr A ((ine_resLe h.le A g).2 hg))
  · intro p hp A hA
    rw [h.K]
    exact ho.split p hp A hA
  · intro w
    obtain ⟨g, hg, hne⟩ := ho.g2 w
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (pow_inj k ?_)⟩
    rw [← rb_pow, ← bar_pow, ← map_pow (resQ T.F), ← hg', ← rb_resLe h]
    exact heq
  · intro w hw
    obtain ⟨g, hg, hne⟩ := ho.g3 w hw
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    exact ⟨g', hm, fun heq => hne (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))⟩
  · exact fun η h2 hom hperm => g3'_up hl h ho η h2 hom hperm
  · obtain ⟨w, hw, hord⟩ := ho.ord
    refine ⟨w, hw, fun n hn0 hn4 => ?_⟩
    obtain ⟨g, hg, hne⟩ := hord n hn0 hn4
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (L1 _ ?_)⟩
    rw [← pow_mul, mul_comm, pow_mul, ← rb_pow, ← hg', ← rb_resLe h]
    exact heq
  · intro A hA g hg h1
    exact ho.kb A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg) h1
  · obtain ⟨m, hm, hψ⟩ := ho.kc
    exact ⟨m, hm, fun g hg => hψ (resLe h.le g) hg⟩
  · intro A hA g hg
    exact ho.ineL A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg)
  · intro i j hij heq
    apply ho.dist i j hij
    obtain ⟨k', hk'⟩ := h.g0
    apply pow_inj k'
    rw [← bar_pow, ← bar_pow, ← hk']
    rw [h.pr] at heq
    exact heq
  · intro A hA
    rcases ho.locL A hA with ⟨g, hg, hne⟩ | ⟨g, hg, h1, h2, h3⟩
    · obtain ⟨g', hg'⟩ := hk g
      left
      refine ⟨g', (ine_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), fun heq => hne (L1 _ ?_)⟩
      rw [← bar_pow, ← map_pow (resQ T.F), ← hg']
      exact heq
    · obtain ⟨g', hg'⟩ := hk g
      right
      refine ⟨g', (dec_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), ?_, ?_, ?_⟩
      · rw [show resQ T'.F g' = resQ T.F (resLe h.le g') from rfl, hg', map_pow, bar_pow, h1, one_pow]
      · rw [rb_resLe h, hg', rb_pow, h2, one_pow]
      · exact fun heq => h3 (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))

private theorem two_up (h : T.Le T') (ht : T.Two) : T'.Two := by
  obtain ⟨j, hj⟩ := up h
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ?_, ht.ord, ht.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [rb_resLe h]
    exact ht.sq _
  · rw [rb_resLe h]
    exact ht.unr A _ hg
  · rw [rb_resLe h]
    exact ht.atL A hA _ hg
  · obtain ⟨k₀, h1, h2, h3, h4⟩ := ht.quad
    refine ⟨k₀, h1, h2, h3, fun g => ?_⟩
    rw [rb_resLe h]
    exact h4 _
  · obtain ⟨g, hg, hne⟩ := ht.bigL A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (dec_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he
  · obtain ⟨g, hg, hne⟩ := ht.big2 A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (ine_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he

private theorem three_up (h : T.Le T') (ht : T.Three) : T'.Three :=
  ⟨ht.five, ht.sb, ht.psi, fun g => by rw [rb_resLe h, rb_resLe h]; exact ht.sq _⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.leFit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T T' : Tower D, T.Le T' → (T.Ok → T'.Ok) ∧ (T.Two → T'.Two) ∧ (T.Three → T'.Three) ∧ (T.Deep → T'.Deep) ∧ (T.Fit → T'.Fit) ∧
      T.Le T ∧ ∀ T'' : Tower D, T'.Le T'' → T.Le T'' := by
  intro Ω _ _ _ l _ c D hD T T' h
  refine ⟨ok_up hD.l_odd h, two_up h, three_up h, ?_, ?_, ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩,
    fun T'' h' => ⟨h'.pr.trans h.pr, h'.K.trans h.K, h.le.trans h'.le, ?_, ?_⟩⟩
  · rintro ⟨m, hm, hk⟩
    exact ⟨m, hm, fun g => hk (resLe h.le g)⟩
  · rintro ⟨ho, hc⟩
    exact ⟨ok_up hD.l_odd h ho, hc.imp (fun a => ⟨a.1, two_up h a.2⟩) fun a => ⟨a.1, a.2.five, a.2.sb, a.2.psi⟩⟩
  · obtain ⟨j, hj⟩ := h.pow
    obtain ⟨k, hk⟩ := h'.pow
    exact ⟨j + k, fun g hg => by rw [pow_add, pow_mul]; exact hk _ (hj g hg)⟩
  · obtain ⟨j, hj⟩ := h.g0
    obtain ⟨k, hk⟩ := h'.g0
    exact ⟨j + k, by rw [hk, hj, pow_add, pow_mul]⟩
