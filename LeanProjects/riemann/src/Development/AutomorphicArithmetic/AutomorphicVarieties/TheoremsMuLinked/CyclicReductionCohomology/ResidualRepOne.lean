import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneLevelO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PsiCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ExistsCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualNO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.TwistedCocycleApplyOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_inv_le {A M Γ : Type} [CommRing A] [AddCommGroup M] [Module A M] [Finite M] [Group Γ]
    (r : Representation A Γ M) (S : Set M)
    (h : ∀ y : M, (∀ g, r g y = y) → y ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective (fun y : r.invariants => (⟨y.1, h y.1 y.2⟩ : S))
    fun a b e => Subtype.ext (congrArg (fun z : S => z.1) e)

private theorem cancel_pow {s K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ K ^ (w + u)) : s ≤ K ^ w := by
  rw [pow_add] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * ((n + ν) * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

private theorem residual_rep_one {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) : y.ρ0 m 1 = 1 := by
  simp [Pt.ρ0, red, mat]

private theorem residual_rep_mul {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) (g h : G0.G₀) :
    y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := by
  simp [Pt.ρ0, red, mat, Matrix.map_mul]

theorem UpperTheory.V.Th.b1absO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : Sys T d D0), l ≠ 2 → PhiCond G0.Γ l → (∀ v, ∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → y.N4 D0 → Eig y T al → DetO y (Set.range T.sg) → B1 y T (n * d + n * T.q) := by
  intro l _ L G0 T O _ _ _ _ _ n y al d D0 S hl hΦ hε hPL hN4 hE hD
  classical
  have hloc : ∀ v : L.Vl, LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) (S.dv v) := fun v => by
    have h1 := (S.counts 0).locV v
    rw [S.dv_eq 0] at h1
    have h2 : (T.GN 0).ε.comp ((S.a 0).ι (.inl v)) = G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v)) := by
      refine MonoidHom.ext fun g => ?_
      show (T.GN 0).ε ((T.GN 0).φ v g) = G0.ε (G0.φ v g)
      rw [← (T.h 0).φ v g, (T.h 0).ε]
    exact h2 ▸ h1
  have hc : G0.ε G0.c = -1 := by rw [← (T.h 0).c, (T.h 0).ε]; exact (S.a 0).c_ε
  choose Cv hCv using fun v : L.Vl => locVO l L G0 O n y v (S.dv v) (hloc v) (hε v)
  obtain ⟨c₁, hc₁⟩ := h0GO l L G0 O n y hl
  obtain ⟨c₀, hc₀⟩ := h0v0O l L G0 O n y D0 hN4
  choose Cq hCq using fun j : Fin T.q => h0qO l L G0 O n y (T.sg j) (al j) (hE j).1 (hE j).2
  obtain ⟨c₂, hc₂⟩ := dualNO l L G0 T O n y hl hc hΦ hPL hD
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEqO l L G0 T O n y m hΦ hPL] with N hN hP
  haveI : Finite (Om O m) := ((omFacts l O).2 m).1
  have hK : 0 < Nat.card (ResidueField O) := by
    have h1 := ((omFacts l O).2 1)
    haveI := h1.1
    have h2 := h1.2.1
    rw [pow_one] at h2
    rw [← h2]
    exact Nat.card_pos
  obtain ⟨⟨rep, hr⟩, ⟨rep', hr'⟩, -⟩ := adExP l L (T.GN N) G0 (T.h N) O n y m
  have hm : ∀ g, y.ρm (T.h N) m g = y.ρ0 m ((T.h N).p₀ g) := fun _ => rfl
  have he : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    simp only [epsm, (T.h N).ε]
  have key := oneLevelO l L (T.GN N) G0 (T.h N) O n y m T.q d (S.a N) rep rep'
    (fun v => m * ((n + n.choose 2) * (1 + S.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (S.counts N) hr hr' (fun v => hCv v m) ?_ ?_ ?_
  · have h2 : ∑ v, S.dv v = d := by rw [← S.dv_eq N]; exact (S.a N).sum_dv
    have k2 := key.2
    rw [sum_exp m n (n.choose 2) d T.q c₁ c₂ c₀ S.dv Cv Cq h2] at k2
    exact ⟨key.1, cancel_pow hK k2⟩
  · rintro (_ | j)
    · refine le_trans (card_inv_le _ _ ?_) (hc₀ m)
      intro Y hy g hg
      rw [← S.d0 N] at hg
      obtain ⟨γ, rfl⟩ := hg
      have e1 := hr'.1 ((S.a N).φq none γ) Y
      have e2 : rep' ((S.a N).φq none γ : (T.GN N).G₀) Y = Y := hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      exact e1.symm
    · refine le_trans (card_inv_le _ _ ?_) (hCq j m)
      intro Y hy
      obtain ⟨γ, hγ⟩ := S.ph N j
      have e1 := hr'.1 (T.ph N j) Y
      have e2 : rep' (T.ph N j : (T.GN N).G₀) Y = Y := by rw [← hγ]; exact hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      have e3 : y.ρ0 m ((T.h N).p₀ (T.ph N j))⁻¹ = y.ρ0 m (T.sg j)⁻¹ := by
        have a1 := residual_rep_mul y m ((T.h N).p₀ (T.ph N j))⁻¹ ((T.h N).p₀ (T.ph N j))
        have a2 := residual_rep_mul y m (T.sg j) (T.sg j)⁻¹
        rw [inv_mul_cancel, residual_rep_one, (hP j).1] at a1
        rw [mul_inv_cancel, residual_rep_one] at a2
        exact left_inv_eq_right_inv a1.symm a2.symm
      rw [(hP j).1, (hP j).2.1, one_smul, e3] at e1
      exact e1.symm
  · refine le_trans (card_inv_le _ _ ?_) (hc₁ m)
    intro Y hy
    refine ⟨?_, fun g => ?_⟩
    · have e1 := hr.2 Y
      have e2 : rep (T.GN N).frame.c Y = Y := hy _
      rw [e2, one_smul] at e1
      exact e1
    · obtain ⟨γ, hγ⟩ := (T.h N).surj g
      have hγm : γ ∈ (T.GN N).η.ker := by
        rw [MonoidHom.mem_ker, ← (T.h N).η, hγ]; exact g.2
      have e0 : (T.h N).p₀ ⟨γ, hγm⟩ = g := Subtype.ext hγ
      have e1 := hr.1 ⟨γ, hγm⟩ Y
      have e2 : rep ((⟨γ, hγm⟩ : (T.GN N).G₀) : (T.GN N).Γ) Y = Y := hy _
      rw [e2, hm, hm, map_inv, e0, one_smul] at e1
      exact e1.symm
  · intro hF
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN rep' hr' hF)
    · rintro z ⟨h1, h2⟩
      refine ⟨h1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (h2 j)
      obtain ⟨γ, hγ⟩ := S.ph N j
      obtain ⟨δ, hδ⟩ := S.ta N j
      exact ⟨Y, by rw [← hγ]; exact hY γ, by rw [← hδ]; exact hY δ⟩
    · exact (Set.toFinite ((Zl rep' : Set _))).subset fun z hz => hz.1
