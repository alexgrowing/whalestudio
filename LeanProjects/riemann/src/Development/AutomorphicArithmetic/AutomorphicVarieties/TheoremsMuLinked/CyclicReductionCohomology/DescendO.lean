import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PlKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PolZCases

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def zeroSub {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) : Subgroup Γ where
  carrier := {g | y g = 0}
  one_mem' := by simpa using hy.2 1 1
  mul_mem' := by
    intro a b ha hb
    have ha' : y a = 0 := ha
    have hb' : y b = 0 := hb
    show y (a * b) = 0
    rw [hy.2, ha', hb', map_zero, add_zero]
  inv_mem' := by
    intro a ha
    have ha' : y a = 0 := ha
    have y1 : y 1 = 0 := by simpa using hy.2 1 1
    have h := hy.2 a⁻¹ a
    rw [inv_mul_cancel, y1, ha', map_zero, add_zero] at h
    exact h.symm

private theorem conj_zero {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) (t g : Γ) (ht : ρ t = 1)
    (h0 : y t = 0) : y (g * t * g⁻¹) = 0 := by
  have y1 : y 1 = 0 := by simpa using hy.2 1 1
  have h := hy.2 g g⁻¹
  rw [mul_inv_cancel, y1] at h
  rw [hy.2, hy.2, h0, map_zero, add_zero, map_mul, ht, mul_one]
  exact h.symm

private theorem factor_lc {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [T2Space Γ'] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)
    (y : Γ → M) (hy : y ∈ Zl ρ) (p : Γ →* Γ') (hc : Continuous p) (hs : Function.Surjective p)
    (hk : ∀ g ∈ p.ker, y g = 0) : ∃ Z : Γ' → M, IsLocallyConstant Z ∧ ∀ g, y g = Z (p g) := by
  have e : ∀ g, y g = y (Function.surjInv hs (p g)) := by
    intro g
    have : g⁻¹ * Function.surjInv hs (p g) ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel]
    have h := hy.2 g (g⁻¹ * Function.surjInv hs (p g))
    rw [hk _ this, map_zero, add_zero, mul_inv_cancel_left] at h
    exact h.symm
  refine ⟨fun γ => y (Function.surjInv hs γ), fun s => ?_, e⟩
  have hq : Topology.IsQuotientMap p := hc.isClosedMap.isQuotientMap hc hs
  rw [← hq.isOpen_preimage]
  convert hy.1 s using 1
  ext g
  simp only [Set.mem_preimage, ← e g]

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] (n m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.descendO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m N : ℕ) (rep' : Representation O (T.GN N).Γ (Mm O n m)), G0.ε G0.c = -1 → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → IsAd1 (T.h N) y m rep' → ∀ z' ∈ Zl rep', z' (T.GN N).c = 0 → (∀ j, z' (T.ta N j) = 0) → ∃ z ∈ Tw y m, ∀ g : (T.GN N).G₀, z' g = z ((T.h N).p₀ g) := by
  intro l _ L G0 T O _ _ _ _ _ n y m N rep' hεc hPL had z' hz hc hta
  have heps : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    unfold epsm
    rw [(T.h N).ε]
  have hcoc : ∀ g g' : (T.GN N).G₀, z' ((g * g' : (T.GN N).G₀) : (T.GN N).Γ) =
      z' g + epsm O (T.GN N) m g • (y.ρm (T.h N) m g * z' g' * y.ρm (T.h N) m g⁻¹) := fun g g' => by
    have e := hz.2 g g'
    rw [had.1 g] at e
    exact e
  have htriv : ∀ j, rep' (T.ta N j) = 1 := by
    intro j
    have h1 : (T.h N).p₀ (T.ta N j) = 1 := Subtype.ext (T.ta_ker N j)
    have h2 : y.ρm (T.h N) m (T.ta N j) = 1 := by
      unfold Pt.ρm
      rw [h1]
      simp [mat, red_one]
    have h3 : y.ρm (T.h N) m (T.ta N j)⁻¹ = 1 := by
      unfold Pt.ρm
      rw [map_inv, h1, inv_one]
      simp [mat, red_one]
    have h4 : epsm O (T.GN N) m (T.ta N j) = 1 := by
      rw [heps, T.ta_ker]
      simp [epsm]
    refine LinearMap.ext fun Z => (had.1 _ Z).trans ?_
    rw [h2, h3, h4, one_smul, one_mul, mul_one]
    rfl
  have hker : (T.h N).p.ker ≤ zeroSub rep' z' hz := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (hz.1.isClosed_fiber 0))
    · refine (Subgroup.closure_le _).2 fun a ha => ?_
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Group.mem_conjugatesOfSet_iff.1 ha
      obtain ⟨g, rfl⟩ := isConj_iff.1 hj
      exact conj_zero rep' z' hz _ g (htriv j) (hta j)
    · intro a ha
      have hη : a ∈ (T.GN N).η.ker := by
        have ha' := ha
        simp only [PL, Subgroup.mem_iInf] at ha'
        exact ha' ⟨⟨(T.GN N).η.ker, (T.GN N).η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
          ⟨0, by
            rw [pow_zero, pow_one]
            show (T.GN N).η h = 1
            rw [← (T.h N).η]
            exact T.H_η _ hh⟩
      exact (plKill l L G0 T O n y m (T.GN N) (T.h N) hPL (fun g => z' g)
        (hz.1.comp_continuous continuous_subtype_val) hcoc ⟨a, hη⟩ ha).1
  obtain ⟨Z, z1, z2⟩ := factor_lc rep' z' hz (T.h N).p (T.h N).cont (T.h N).surj fun g hg => hker hg
  have hs : ∀ g0 : G0.G₀, ∃ g : (T.GN N).G₀, (T.h N).p₀ g = g0 := by
    intro g0
    obtain ⟨g, hg⟩ := (T.h N).surj g0
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [MonoidHom.mem_ker, ← (T.h N).η, hg]
    exact g0.2
  have z3 : ∀ g : (T.GN N).G₀, Z ((T.h N).p₀ g : G0.G₀) = z' g := fun g => (z2 g).symm
  refine ⟨fun g0 => Z g0, ⟨z1.comp_continuous continuous_subtype_val, fun g0 h0 => ?_, fun g0 => ?_⟩,
    fun g => by rw [← z3]⟩
  · obtain ⟨g, rfl⟩ := hs g0
    obtain ⟨h, rfl⟩ := hs h0
    have e := hcoc g h
    rw [heps] at e
    simp only []
    rw [← map_mul, z3, z3, z3, ← map_inv]
    exact e
  · obtain ⟨g, rfl⟩ := hs g0
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      (Units.isUnit y.P).map (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix
    have e := ((polP l (T.GN N).frame O _ n _ _ _ rep' hP had).2 z' hz hc).1 g
    have e2 : G0.frame.conj ((T.h N).p₀ g) = (T.h N).p₀ ((T.GN N).frame.conj g) := by
      refine Subtype.ext ?_
      show G0.c * (T.h N).p g * G0.c⁻¹ = (T.h N).p ((T.GN N).c * g * (T.GN N).c⁻¹)
      rw [map_mul, map_mul, map_inv, (T.h N).c]
    have e3 : epsm O (T.GN N) m (T.GN N).c = -1 := by
      rw [heps, (T.h N).c]
      simp [epsm, hεc]
    simp only []
    rw [e2, z3, z3]
    refine e.trans ?_
    show -(epsm O (T.GN N) m (T.GN N).c • _) = _
    rw [e3, neg_smul, neg_neg, one_smul]
