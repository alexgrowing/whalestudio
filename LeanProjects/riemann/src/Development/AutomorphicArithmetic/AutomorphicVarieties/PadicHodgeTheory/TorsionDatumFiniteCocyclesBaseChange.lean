import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem multiplicity_one_positive {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ}
    (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B) (hT : T.Good π Ψ) :
    Positive (MonoidHom.id (GQ l)) (resCoef E T.M1) := by
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have w0 : wt1 (0 : Fin 3) = 1 := by decide
  have w1 : wt1 (1 : Fin 3) = 0 := by decide
  have w2 : wt1 (2 : Fin 3) = -1 := by decide
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  refine ⟨?_, ?_⟩
  · have hφ : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
    have hcH : ContAction ((resCoef E T.M1).comp H.subtype : Representation E H (B × B)) :=
      Continuous.comp (g := fun p : GQ l × B × B => resCoef E T.M1 p.1 p.2)
        (f := fun p : H × B × B => ((p.1 : GQ l), p.2)) hc (by fun_prop)
    rw [((isCrys_isDR_restrict_openSubgroup _ hid _ hc).2 H hD.isOpen).2]
    refine (isCrys_isDR_restrict_openSubgroup _ hφ _ hcH).1 (crUnr _ hφ _ hcH e fun g hg x => ?_)
    have hg' : (g : GQ l) ∈ Iq l := hg
    have hu : ∀ i, T.t g i = Units.map (algebraMap E B : E →* B) (Ψ g ^ wt1 i) := fun i =>
      Units.ext (hT.ine g hg' i)
    change T.M1 g x = ((cycA l l E g ^ (e : ℤ) : Eˣ) : E) • x
    rw [zpow_natCast, ← hD.ΨH g g.2 hg', Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    simp only [hu, w0, w1, w2, ← map_div]
    ext <;> simp [Algebra.smul_def]
  · let ε : GQ l →* Eˣ := (Units.map (Int.castRingHom E : ℤ →* E)).comp η
    have h2 : (2 : B) * algebraMap ℚ_[l] B (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap ℚ_[l] B) 2, ← map_mul]
      norm_num
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T.M1 _ ![((1 : B), (1 : B)), (1, -1)] ![ε * Ψ, Ψ] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨a, b⟩ -
      have : (a, b) = (algebraMap ℚ_[l] B (1 / 2) * (a + b)) • ((1 : B), (1 : B)) +
          (algebraMap ℚ_[l] B (1 / 2) * (a - b)) • ((1 : B), (-1 : B)) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination (-a) * h2
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination (-b) * h2
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · have he : (1 : ℤ) ≤ e := by exact_mod_cast hD.e_pos
      intro j
      refine ⟨e, he, H, hD.isOpen, fun g hg hI => ?_⟩
      have h1 := hD.ΨH g hg hI
      fin_cases j
      · simp [ε, hD.ηH g hg, h1]
      · simp [h1]
    · have key : ∀ v : B × B, π v.1 = 0 → π v.2 = 0 →
          v ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B (B × B)) := by
        rintro ⟨a, b⟩ ha hb
        have : (a, b) = a • ((1 : B), (0 : B)) + b • ((0 : B), (1 : B)) := by simp
        rw [this]
        exact add_mem (Submodule.smul_mem_smul ha trivial) (Submodule.smul_mem_smul hb trivial)
      intro g j
      have hu : ∀ i, Units.map (π : B →* E) (T.t g i) = Ψ g ^ wt1 i := fun i => Units.ext (hT.red g i)
      have ha : π ((T.t g 0 / T.t g 1 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 0 / T.t g 1) = Ψ g := by simp [map_div, hu, w0, w1]
        exact congrArg Units.val this
      have hb : π ((T.t g 1 / T.t g 2 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 1 / T.t g 2) = Ψ g := by simp [map_div, hu, w1, w2]
        exact congrArg Units.val this
      have hn : ((-1 : ℤˣ) = 1) = False := by decide
      rw [Tor.adjointSuperdiagRep_apply]
      generalize ((T.t g 0 / T.t g 1 : Bˣ) : B) = a at ha ⊢
      generalize ((T.t g 1 / T.t g 2 : Bˣ) : B) = b at hb ⊢
      apply key <;> rcases Int.units_eq_one_or (η g) with hg | hg <;> fin_cases j <;>
        simp [ε, hg, hn, ha, hb, Algebra.smul_def]

theorem UpperTheory.torsionDatum_finiteCocycles_baseChange :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1, ∃ β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1, ∀ g, p (β g).1 = (β' g).1 ∧ p (β g).2 = (β' g).2 := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' _ p hp T T' hT hT' ht β' hβ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have hc' : ContAction (resCoef E T'.M1) := T'.contAction_torus_module hD.ηlc hT'.cont hT'.cont_inv
  have hu : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B') := fun g i j => by
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (ht g i)
    rw [← h, ← h, ← map_div]
    rfl
  obtain ⟨β, hβ, hpβ⟩ := (posExact hP (MonoidHom.id (GQ l)) IsOpenEmbedding.id (resCoef E T.M1) (resCoef E T'.M1)
    hc hc' (multiplicity_one_positive hD π hπ T hT) (p.toLinearMap.prodMap p.toLinearMap) (fun g x => by
      change Prod.map p p (T.M1 g x) = T'.M1 g (Prod.map p p x)
      simp only [Tor.adjointSuperdiagRep_apply]
      split_ifs <;> simp only [Prod.map, map_mul, map_neg, hu])).1 (hp.prodMap hp) β'
    ((z1fMap (MonoidHom.id (GQ l)) T'.M1 (resCoef E T'.M1)).2 LinearMap.id (fun _ _ => rfl) β' hβ')
  refine ⟨β, (z1fMap (MonoidHom.id (GQ l)) (resCoef E T.M1) T.M1).2 LinearMap.id (fun _ _ => rfl) β hβ, fun g => ?_⟩
  rw [← hpβ]
  exact ⟨rfl, rfl⟩
