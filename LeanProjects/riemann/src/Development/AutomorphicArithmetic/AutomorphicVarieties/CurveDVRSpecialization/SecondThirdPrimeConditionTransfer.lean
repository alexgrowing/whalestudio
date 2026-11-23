import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PointEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StableOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ThickOf

private theorem chain_nat {α : Type} {r : α → α → Prop} {p q : α} (H : Relation.ReflTransGen r p q) :
    ∃ (h : ℕ) (c : ℕ → α), c 0 = p ∧ c h = q ∧ ∀ i < h, r (c i) (c (i + 1)) := by
  induction H with
  | refl => exact ⟨0, fun _ => p, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b d _ hbd ih =>
    obtain ⟨h, c, h0, hh, hs⟩ := ih
    refine ⟨h + 1, fun i => if i ≤ h then c i else d, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hih : i < h
      · have h1 : i ≤ h := le_of_lt hih
        have h2 : i + 1 ≤ h := hih
        simp only [h1, h2, if_true]
        exact hs i hih
      · have hie : i = h := by omega
        subst hie
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) from by omega, if_false, hh]
        exact hbd

theorem UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3), T.SecondThirdPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F T Φ hΦ hN4 J hJ x L p q hp hTE hch hPex P' hP' hP'q hP'TI
  haveI := L.co
  obtain ⟨P, hP, hPp, hPTI, hJP⟩ := hPex
  obtain ⟨h, c, hc0, hch', hs⟩ := chain_nat hch
  have back_le : ∀ (A : Ideal L.R) [A.IsPrime] (w : UpperTheory.V.W.Point T.r)
      (k : L.R →ₐ[O] w.A), A ≤ RingHom.ker k →
      (T.back Φ L A).asIdeal ≤ RingHom.ker (k.comp (T.phi Φ L)) := by
    intro A _ w k hA z hz
    have h2 : (T.phi Φ L) z ∈ RingHom.ker k := hA hz
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  have hN : ∀ i, i ≤ h → UpperTheory.V.Pr.Nice L.ρ (c i) ∧ L.ρ.TE (c i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ⟨(hs i hlt).1, (hs i hlt).2.1⟩
    · rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hc0]
        exact ⟨hp, hTE⟩
      · have hl := hs (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at hl
        exact ⟨hl.2.2.1, hl.2.2.2.1⟩
  have hpt : ∀ i : Fin (h + 1), ∃ (w : UpperTheory.V.W.Point T.r) (k : L.R →ₐ[O] w.A),
      RingHom.ker k = c i ∧ IsLocalHom k ∧
      UpperTheory.V.W.mat w.ρ = T.K.tw (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧
      w.ψ = T.K.twψ (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧ T.B.IsPt w (k.comp (T.phi Φ L)) := by
    intro i
    have hi := (hN i (Nat.lt_succ_iff.mp i.isLt)).1
    exact UpperTheory.V.Pr.pointEx l O F 3 T Φ hΦ x L (c i) hi.prime hi.dim hi.char
  choose y j hker hloc hmat hψ hIsPt using hpt
  have hNE : ∀ i, (y i).NiceE := by
    intro i
    have hi := hN i (Nat.lt_succ_iff.mp i.isLt)
    have hn : UpperTheory.V.Pr.Nice L.ρ (RingHom.ker (j i)) := by rw [hker]; exact hi.1
    have ht : L.ρ.TE (RingHom.ker (j i)) := by rw [hker]; exact hi.2
    obtain ⟨h1, h3, _, hE⟩ := UpperTheory.V.Pr.niceOf l O F 3 T x L (y i) (j i) (hloc i) hn (hmat i) (hψ i)
    exact ⟨h1, hE ht, h3, hN4 (y i)⟩
  have hlink : ∀ i : Fin h, ∃ E : Ideal L.R, E.IsPrime ∧ UpperTheory.V.Fr.Thick L.ρ E ∧ E ≤ c i ∧ E ≤ c (i + 1) :=
    fun i => (hs i i.isLt).2.2.2.2
  choose E hEp hEt hE1 hE2 using hlink
  let e : Fin h → PrimeSpectrum T.B.B := fun i => @UpperTheory.V.Pr.Setup.back _ _ _ _ _ _ _ _ _ _ T Φ _ L (E i) (hEp i)
  have key := hJ h y (fun i => (j i).comp (T.phi Φ L)) e hNE hIsPt (by
      intro i
      haveI := hEp i
      refine ⟨UpperTheory.V.Pr.thickOf l O F T Φ hΦ x L (E i) (hEt i), ?_, ?_⟩
      · apply back_le
        rw [hker]
        simpa using hE1 i
      · apply back_le
        rw [hker]
        simpa using hE2 i)
    (by
      haveI := hP
      refine ⟨T.back Φ L P, UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P hPTI, ?_, ?_⟩
      · intro z hz
        exact (Ideal.map_le_iff_le_comap.mp hJP) hz
      · apply back_le
        rw [hker]
        simpa [hc0] using hPp)
  haveI := hP'
  have hfin := key (T.back Φ L P') (by
      apply back_le
      rw [hker]
      simpa [hch'] using hP'q)
    (Or.inl (UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P' hP'TI))
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  exact hfin hz
