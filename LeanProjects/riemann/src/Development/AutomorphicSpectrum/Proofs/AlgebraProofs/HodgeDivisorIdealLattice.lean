import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembership
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOfTestIdeal
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowSpanLocFreeBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSecondGoodness
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHolds
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem ideal_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (A B : AddSubgroup Ω) (hB : LocFree R 1 B) (hA : ∀ a ∈ A, a ∈ R) (hm : ∃ m : ℕ, (p : Ω) ^ m ∈ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (algebraMap Ω C '' A) = spanOver RC (algebraMap Ω C '' B)) :
    A ≤ B := by
  intro v hv
  obtain ⟨m, hm⟩ := hm
  refine GlobalTheory.CompanionTheory.Ar.Num.HaTest.mem_of_test_ideal R p hp hp0 hN hF hI B hB v ⟨m, ?_⟩ ?_
  · have := hB.1 v (hA v hv) _ hm
    rwa [smul_eq_mul, mul_comm] at this
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

theorem lattice_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    {k N : ℕ} (L A B : AddSubgroup (Fin k → Ω)) (hB : LocFree R N B) (hA : A ≤ L)
    (hm : mulLat (p : Ω) L ≤ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (bcMap Ω C (Fin k) '' A) = spanOver RC (bcMap Ω C (Fin k) '' B)) :
    A ≤ B := by
  intro v hv
  refine GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI N B hB v ⟨1, ?_⟩ ?_
  · rw [pow_one]
    exact hm ⟨v, hA hv, rfl⟩
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

omit [Algebra o Ω] in
theorem map_snd_span {C : Type} [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C) {k : ℕ}
    (G : AddSubgroup (Ω × (Fin k → Ω))) :
    (spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin k)) '' G)).map (AddMonoidHom.snd _ _) =
      spanOver RC (bcMap Ω C (Fin k) '' (G.map (AddMonoidHom.snd _ _))) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨g.2, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
  {D : LieLatticeData Ω F n Sg r s} {R : Subalgebra o Ω} {p : ℕ} {w : Ω} {χ : Sg → F → Ω}

theorem xId_le (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∀ c ∈ D.xId (χ τ) i, c ∈ R := by
  intro c hc'
  have h : (c • fun x : Fin n → F => χ τ (x i)) ∈
    D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup := hc'
  obtain ⟨g, hg, v, hv, e⟩ := AddSubgroup.mem_sup.1 h
  have hx : (Pi.single i (1 : F) : Fin n → F) ∈
      {x : Fin n → F | ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0} := by
    intro j hj
    have : j ≠ i := by
      rintro rfl
      omega
    exact Pi.single_eq_of_ne this _
  have hv0 : v (Pi.single i 1) = 0 := hv _ hx
  have hgR : g (Pi.single i 1) ∈ R := hb.M_le hg _ (Set.mem_univ _)
  have e1 := congrFun e (Pi.single i 1)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, hv0, add_zero, smul_eq_mul,
    (hc.2.2.2.2 τ).2.1, mul_one] at e1
  rwa [← e1]

theorem pow_smul_mem (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, ((p : Ω) ^ m • fun x : Fin n → F => χ τ (x i)) ∈ D.M := by
  obtain ⟨m, hm⟩ := hb.le_M
  exact ⟨m, hm ⟨fun x => χ τ (x i), fun x _ => (hc.2.2.2.2 τ).2.2 _, rfl⟩⟩

theorem pow_mem_xId (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.xId (χ τ) i := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  exact ⟨m, AddSubgroup.mem_sup_left hm⟩

theorem pow_mem_dId (hc : CharData R p w χ) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.dId R p (χ τ) i := by
  refine ⟨1, (p : Ω) • Pi.single i 1, ⟨?_, ?_⟩, ?_⟩
  · show linMap n (χ τ) ((p : Ω) • Pi.single i 1) ∈ D.l1 R p
    rw [map_smul]
    refine AddSubgroup.mem_sup_right ⟨linMap n (χ τ) (Pi.single i 1), fun x _ => ?_, rfl⟩
    show linMap n (χ τ) (Pi.single i 1) x ∈ R
    simp only [linMap, Fintype.linearCombination_apply_single, one_smul]
    exact (hc.2.2.2.2 τ).2.2 _
  · intro j hj
    have : j ≠ i := by
      rintro rfl
      exact Nat.lt_irrefl _ hj
    show ((p : Ω) • Pi.single i (1 : Ω) : Fin n → Ω) j = 0
    simp [Pi.single_eq_of_ne this]
  · simp

omit [One F] in
theorem kk_le (hb : D.Base R p w) (τ : Sg) (i : ℕ) : D.kk τ i ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨g, m⟩, ⟨h, -⟩, rfl⟩
  exact ((hb.th τ).2.1 m).1 ⟨g, h⟩

omit [One F] in
theorem le_kk (hb : D.Base R p w) (τ : Sg) (i : ℕ) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ D.kk τ i := by
  intro m hm
  exact ⟨(0, m), ⟨((hb.th τ).2.2 m).2 hm, zero_mem _, trivial⟩, rfl⟩

omit [One F] in
theorem step_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨c, m⟩, h, rfl⟩
  have h' : ((c • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨-, hv⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h2 : m2 = 0 := hv
  have h1 : m1 + m2 = m := congrArg Prod.snd e
  rw [h2, add_zero] at h1
  subst h1
  exact ((hb.th τ).2.1 m1).1 ⟨g, hg⟩

omit [One F] in
theorem le_step (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) := by
  intro m hm
  refine ⟨(0, m), ?_, rfl⟩
  show (((0 : Ω) • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  rw [zero_smul]
  exact AddSubgroup.mem_sup_left (((hb.th τ).2.2 m).2 hm)

omit [One F] in
theorem ker_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).comap (AddMonoidHom.inl _ _) ≤ D.xId ψ i := by
  intro c h
  have h' : ((c • fun x : Fin n → F => ψ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨hv, -⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h1 : g + v = c • fun x : Fin n → F => ψ (x i) := congrArg Prod.fst e
  show (c • fun x : Fin n → F => ψ (x i)) ∈ D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup
  rw [← h1]
  exact AddSubgroup.add_mem_sup (((hb.th τ).1 g).1 ⟨m1, hg⟩).1 hv

theorem pow_mem_ker (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  obtain ⟨u, hu⟩ := ((hb.th τ).1 _).2 ⟨hm, by simp [(hc.2.2.2.2 τ).1]⟩
  have h1 := (hb.stable τ (p : Ω) (natCast_mem R p)).2.2 _ hu
  have h2 := ((hb.th τ).2.2 ((p : Ω) • u)).2 ⟨u, ((hb.th τ).2.1 u).1 ⟨_, hu⟩, rfl⟩
  have h3 := sub_mem h1 h2
  refine ⟨m + 1, ?_⟩
  show (((p : Ω) ^ (m + 1) • fun x : Fin n → F => χ τ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  refine AddSubgroup.mem_sup_left ?_
  rw [Prod.smul_mk, Prod.mk_sub_mk, sub_zero, sub_self, smul_smul, ← pow_succ'] at h3
  exact h3

theorem powSpan_le (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : ∀ c ∈ X, c ∈ R) :
    ∀ c ∈ powSpan R p X, c ∈ R := by
  have : powSpan R p X ≤ R.toSubring.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact R.mul_mem ha (R.pow_mem (hX x hx) p)
  exact fun c hc => this hc

end GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices

open GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices in

theorem GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2
  obtain ⟨hf1, hbc1⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hb hG
  have hk := GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change D R p w χ hc hb hG
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main D R p w χ hc hb hG hG2
    (GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice D R p w χ hc hb hp hN hF hI φ hT hG)
  have hp0 := hc.1
  refine ⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_⟩
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) =
          spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 τ).2 i).1, ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).dx τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf1 τ).2.2.2 i) ?_ (pow_mem_xId hc hb τ i) h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 τ).2 i).1 (xId_le hc hb τ i) (pow_mem_dId hc τ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rintro _ ⟨l, ⟨hl, -⟩, rfl⟩
    exact (hf1 τ).2.2.1 hl i (Set.mem_univ _)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (bcMap Ω C (Fin (r τ)) '' (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) =
          spanOver RC (bcMap Ω C (Fin (r τ)) '' D.kk τ i) := by
      intro C _ _ _ _ RC hRC
      rw [← map_snd_span, ← (hk C RC hRC.2.2.2 τ).2 i, ← (hk C RC hRC.2.2.2 τ).1 i]
      exact (hT C RC hRC).onto τ i
    exact le_antisymm
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.kk τ i) (step_le hb τ _ i) (le_kk hb τ i) h)
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.step τ i) (kk_le hb τ i) (le_step hb τ _ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C ''
            (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _)) =
          spanOver RC (algebraMap Ω C '' powSpan R p (D.xId (χ τ) i)) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 (φ τ)).2 i).2,
        ← (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange R RC hRC.2.2.2 p _ ((hf1 τ).2.2.2 i)).2,
        ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).inj τ i
    obtain ⟨m, hm⟩ := pow_mem_xId hc hb τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _
        (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange (C := Ω) R R (fun _ ha => ha) p _ ((hf1 τ).2.2.2 i)).1
        (fun a ha => xId_le hc hb (φ τ) i a (ker_le hb _ _ i ha)) ⟨m * p, ?_⟩ h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 (φ τ)).2 i).2
        (powSpan_le R p _ (xId_le hc hb τ i)) (pow_mem_ker hc hb (φ τ) i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rw [pow_mul]
    exact mem_span R ⟨_, hm, rfl⟩
