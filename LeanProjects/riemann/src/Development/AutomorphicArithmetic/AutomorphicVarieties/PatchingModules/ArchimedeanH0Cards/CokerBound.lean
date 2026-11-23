import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles

open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ]
  {P : Pl Γ} {D0 D D' : Dat A P}

private def Defect (k : D0.Hom D) (r : D.Hom D') (p : D'.C2) (c : ∀ w, Z2 (D0.Q w).ρ) : Prop :=
  ∃ q : D.C2, q.1 ∈ Z2 D.M.ρ ∧ (∀ w, Continuous (q.2 w)) ∧ r.c2 q = p ∧
    ∀ w g h, k.fq w ((c w).1 (g, h)) = D.π w (q.1 (P.φ w g, P.φ w h)) - d1 (D.Q w).ρ (q.2 w) (g, h)

private theorem defect_sub {k : D0.Hom D} {r : D.Hom D'} {p p' : D'.C2} {c c' : ∀ w, Z2 (D0.Q w).ρ}
    (h : Defect k r p c) (h' : Defect k r p' c') : Defect k r (p - p') (c - c') := by
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h
  obtain ⟨q', hq1', hq2', hq3', hq4'⟩ := h'
  refine ⟨q - q', Submodule.sub_mem _ hq1 hq1', fun w => (hq2 w).sub (hq2' w),
    by rw [map_sub, hq3, hq3'], fun w g h => ?_⟩
  have e1 := hq4 w g h
  have e2 := hq4' w g h
  simp only [Pi.sub_apply, Submodule.coe_sub, AddSubgroupClass.coe_sub, Prod.fst_sub,
    Prod.snd_sub, map_sub] at e1 e2 ⊢
  rw [e1, e2]
  abel

private theorem lift_two_cocycle_surjection [IsTopologicalGroup Γ] (r : D.Hom D') (hs : Function.Surjective r.f)
    (h2 : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv))
    (z' : Z2 D'.M.ρ) : ∃ z ∈ Z2 D.M.ρ, ∀ s, r.f (z s) = z'.1 s := by
  obtain ⟨y, hy⟩ := h2 (Submodule.Quotient.mk z')
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mapH2, Submodule.mapQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    Submodule.coe_subtype, separated_dvr_second_cohomology_mem] at hy
  obtain ⟨b', hb'c, hb'⟩ := hy
  choose σ hσ using hs
  let b : Γ → D.M.X := fun g => σ (b' g)
  have hbc : Continuous b := (continuous_of_discreteTopology (f := σ)).comp hb'c
  refine ⟨z0.1 - d1 D.M.ρ b, ?_, fun s => ?_⟩
  · exact Submodule.sub_mem _ z0.2 (coboundaries2_le_cocycles2 _ D.M.cont ((separated_dvr_second_cohomology_mem _ _).2 ⟨b, hbc, rfl⟩))
  · obtain ⟨g, h⟩ := s
    have e := congrFun hb' (g, h)
    rw [d1_apply] at e
    change _ = r.f (z0.1 (g, h)) - z'.1 (g, h) at e
    simp only [b, Pi.sub_apply, map_sub, map_add, d1_apply, r.equiv, hσ]
    rw [e]
    abel

private theorem defect_ex [IsTopologicalGroup Γ] {k : D0.Hom D} {r : D.Hom D'} (S : Dat.SES k r)
    (h2 : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv))
    (p : D'.selmerSecondCocycles) : ∃ c, Defect k r p.1 c := by
  obtain ⟨hp1, hp2⟩ := p.2
  obtain ⟨z, hz, hzr⟩ := lift_two_cocycle_surjection r S.surj h2 ⟨p.1.1, hp1⟩
  have hfq : ∀ w, Function.Surjective (r.fq w) := by
    intro w y
    obtain ⟨m', rfl⟩ := D'.surj w y
    obtain ⟨m, rfl⟩ := S.surj m'
    exact ⟨D.π w m, r.comm w m⟩
  choose σ hσ using hfq
  let q : D.C2 := (z, fun w g => σ w (p.1.2 w g))
  have hqc : ∀ w, Continuous (q.2 w) := fun w =>
    (continuous_of_discreteTopology (f := σ w)).comp (hp2 w).1
  let e : ∀ w, P.G w × P.G w → (D.Q w).X := fun w s =>
    D.π w (z (P.φ w s.1, P.φ w s.2)) - d1 (D.Q w).ρ (q.2 w) s
  have he : ∀ w s, r.fq w (e w s) = 0 := by
    intro w s
    obtain ⟨g, h⟩ := s
    simp only [e, q, map_sub, map_add, d1_apply, r.comm, hzr, r.equivq, hσ]
    rw [(hp2 w).2 g h, d1_apply, sub_self]
  have hex : ∀ w s, ∃ x, k.fq w x = e w s := fun w s => (S.exq w (e w s)).mp (he w s)
  let τ : ∀ w, (D.Q w).X → (D0.Q w).X := fun w => Function.invFun (k.fq w)
  have hτ : ∀ w s, k.fq w (τ w (e w s)) = e w s := fun w s => Function.invFun_eq (hex w s)
  have hec : ∀ w, Continuous (e w) := by
    intro w
    have hd : ∀ s : P.G w × P.G w, d1 (D.Q w).ρ (q.2 w) s
        = (D.Q w).ρ s.1 (q.2 w s.2) - q.2 w (s.1 * s.2) + q.2 w s.1 := fun s => d1_apply _ _ s.1 s.2
    have h1 : Continuous fun s : P.G w × P.G w => D.π w (z (P.φ w s.1, P.φ w s.2)) :=
      (continuous_of_discreteTopology (f := D.π w)).comp
        (hz.1.comp (((P.cont w).comp continuous_fst).prodMk ((P.cont w).comp continuous_snd)))
    have h2' : Continuous fun s : P.G w × P.G w => d1 (D.Q w).ρ (q.2 w) s := by
      simp only [hd]
      exact (((D.Q w).cont.comp (continuous_fst.prodMk ((hqc w).comp continuous_snd))).sub
        ((hqc w).comp continuous_mul)).add ((hqc w).comp continuous_fst)
    exact h1.sub h2'
  have hE : ∀ w (g h t : P.G w), (D.Q w).ρ g (e w (h, t)) - e w (g * h, t) + e w (g, h * t)
      - e w (g, h) = 0 := by
    intro w g h t
    have key := congrArg (D.π w) (hz.2 (P.φ w g) (P.φ w h) (P.φ w t))
    simp only [map_sub, map_add, map_zero, D.equiv] at key
    simp only [e, d1_apply, map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]
    refine (sub_eq_zero.mp ?_).trans key
    abel
  let c : ∀ w, Z2 (D0.Q w).ρ := fun w =>
    ⟨fun s => τ w (e w s), (continuous_of_discreteTopology (f := τ w)).comp (hec w), by
      intro g h t
      apply S.injq w
      simp only [map_sub, map_add, map_zero, k.equivq, hτ]
      exact hE w g h t⟩
  refine ⟨c, q, hz, hqc, ?_, fun w g h => hτ w (g, h)⟩
  refine Prod.ext ?_ ?_
  · funext s
    exact hzr s
  · funext w g
    exact hσ w _

private theorem defect_zero {k : D0.Hom D} {r : D.Hom D'} (S : Dat.SES k r) (p : D'.selmerSecondCocycles)
    {c : ∀ w, Z2 (D0.Q w).ρ} (h : Defect k r p.1 c)
    (hc : (fun w => (Submodule.Quotient.mk (c w) : H2 (D0.Q w).ρ)) ∈ LinearMap.range D0.loc2) :
    (Submodule.Quotient.mk p : D'.H2LocalConditions) ∈ LinearMap.range r.h2 := by
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h
  obtain ⟨y, hy⟩ := hc
  obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hw : ∀ w, ∃ b : P.G w → (D0.Q w).X, Continuous b ∧ ∀ g h,
      (c w).1 (g, h) = D0.π w (y0.1 (P.φ w g, P.φ w h)) - d1 (D0.Q w).ρ b (g, h) := by
    intro w
    have e := congrFun hy w
    simp only [Dat.loc2, LinearMap.pi_apply, compatiblePairH2, Submodule.mapQ_apply] at e
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, separated_dvr_second_cohomology_mem] at e
    obtain ⟨b, hb, hbe⟩ := e
    refine ⟨b, hb, fun g h => ?_⟩
    have e2 := congrFun hbe (g, h)
    change _ = D0.π w (y0.1 (P.φ w g, P.φ w h)) - (c w).1 (g, h) at e2
    rw [e2]
    abel
  choose b hbc hbe using hw
  have hZ : (q.1 - fun s => k.f (y0.1 s), fun w g => q.2 w g - k.fq w (b w g)) ∈ D.selmerSecondCocycles := by
    refine ⟨Submodule.sub_mem _ hq1
      (cocycles2Map D0.M.ρ D.M.ρ k.f continuous_of_discreteTopology k.equiv y0).2,
      fun w => ⟨?_, fun g h => ?_⟩⟩
    · exact (hq2 w).sub ((continuous_of_discreteTopology (f := k.fq w)).comp (hbc w))
    · have e1 := hq4 w g h
      rw [hbe w g h] at e1
      simp only [Pi.sub_apply, map_sub, map_add, d1_apply, k.comm, k.equivq] at e1 ⊢
      refine sub_eq_zero.mp (Eq.trans ?_ (sub_eq_zero.mpr e1.symm))
      abel
  refine ⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩
  rw [Dat.Hom.h2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change r.c2 _ = p.1
  rw [← hq3]
  refine Prod.ext ?_ ?_
  · funext s
    change r.f (q.1 s - k.f (y0.1 s)) = r.f (q.1 s)
    rw [map_sub, (S.ex _).mpr ⟨_, rfl⟩, sub_zero]
  · funext w g
    change r.fq w (q.2 w g - k.fq w (b w g)) = r.fq w (q.2 w g)
    rw [map_sub, (S.exq w _).mpr ⟨_, rfl⟩, sub_zero]

end

theorem UpperTheory.V.Pa.B2.cokerBound :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D0 D D' : Dat A P) (k : D0.Hom D) (r : D.Hom D'), Dat.SES k r → Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv) → Finite D0.Ck2 → Finite (D'.H2LocalConditions ⧸ LinearMap.range r.h2) ∧ Nat.card (D'.H2LocalConditions ⧸ LinearMap.range r.h2) ≤ Nat.card D0.Ck2 := by
  intro A Γ _ _ _ _ P D0 D D' k r S h2 hfin
  have hp : ∀ a : D'.H2LocalConditions ⧸ LinearMap.range r.h2, ∃ p : D'.selmerSecondCocycles,
      Submodule.Quotient.mk (Submodule.Quotient.mk p : D'.H2LocalConditions) = a := fun a => by
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact ⟨p, rfl⟩
  choose p hp using hp
  choose c hc using defect_ex S h2
  have hinj : Function.Injective fun a : D'.H2LocalConditions ⧸ LinearMap.range r.h2 =>
      (Submodule.Quotient.mk (fun w => (Submodule.Quotient.mk (c (p a) w) : H2 (D0.Q w).ρ)) : D0.Ck2) := by
    intro a b hab
    have h1 := (Submodule.Quotient.eq _).1 hab
    have h3 := defect_zero S (p a - p b) (defect_sub (hc (p a)) (hc (p b))) h1
    rw [← hp a, ← hp b]
    exact (Submodule.Quotient.eq _).2 h3
  exact ⟨Finite.of_injective _ hinj, Nat.card_le_card_of_injective _ hinj⟩
