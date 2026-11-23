import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.torsionDatum_finiteCocycles_compare :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ δ' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T'.χ2), ∃ δ ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T.χ2), ∀ g, p (δ g) = δ' g := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp T T' hT hT'
    hTT δ' hδ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (chRep T.χ2) := contAction_chRep (T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv)
  have hc' : ContAction (chRep T'.χ2) := contAction_chRep (T'.continuous_χ2 hD.ηlc hT'.cont hT'.cont_inv)
  have hcE : ContAction (resCoef E (chRep T.χ2)) := hc
  have hcE' : ContAction (resCoef E (chRep T'.χ2)) := hc'
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  have hI : ∀ g ∈ H, g ∈ Iq l →
      T.χ2 g = Units.map (algebraMap E B : E →* B) (cycA l l E g ^ ((2 * e : ℕ) : ℤ)) := by
    intro g hg hgI
    have h := (hT.chars hD).ine ⟨g, hg⟩ hgI
    simp only [Tor.ch_apply, Subgroup.coe_subtype] at h
    change Units.map _ (η g) * (T.t g 0 / T.t g 2) = _
    rw [hD.ηH g hg, map_one, one_mul, h 0, h 2, map_zpow, algebraMap_cycA, div_eq_mul_inv, ← zpow_sub]
    congr 1
    simp [wt1]
    ring
  have hpos : Positive (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) := by
    refine ⟨?_, ?_⟩
    · refine (((isCrys_isDR_restrict_openSubgroup _ hid _ hcE).2 H hD.isOpen).2).2 ?_
      have hH : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
      have hcH : ContAction ((resCoef E (chRep T.χ2)).comp H.subtype : Representation E H B) :=
        (((T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv).comp continuous_subtype_val).comp continuous_fst).mul
          continuous_snd
      refine (isCrys_isDR_restrict_openSubgroup _ hH _ hcH).1 (crUnr _ hH _ hcH ((2 * e : ℕ) : ℤ) fun g hg x => ?_)
      change (T.χ2 g : B) * x = _
      rw [hI g g.2 hg, Algebra.smul_def]
      rfl
    · refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (fun _ : Unit => (1 : B))
        (fun _ => (Units.map (π : B →* E)).comp T.χ2) ?_ (fun _ => ?_) (fun g _ => ?_)
      · simp [Ideal.span_singleton_one]
      · refine ⟨((2 * e : ℕ) : ℤ), by have := hD.e_pos; omega, H, hD.isOpen, fun g hg hgI => ?_⟩
        apply Units.ext
        change π (T.χ2 g : B) = _
        rw [hI g hg hgI]
        exact π.commutes _
      · rw [Ideal.smul_eq_mul, Ideal.mul_top, RingHom.mem_ker]
        change π ((T.χ2 g : B) * 1 - π (T.χ2 g : B) • (1 : B)) = 0
        simp
  have hχ : ∀ g, p (T.χ2 g : B) = (T'.χ2 g : B') := by
    intro g
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (hTT g i)
    rw [Tor.χ2_apply, Tor.χ2_apply, map_mul, map_intCast, ← h 0, ← h 2, ← map_div]
    rfl
  obtain ⟨δ, hδ, hδp⟩ := (posExact hP _ hid _ _ hcE hcE' hpos p.toLinearMap (fun g x => by
      change p ((T.χ2 g : B) * x) = (T'.χ2 g : B') * p x
      rw [map_mul, hχ])).1 hp δ'
    ((z1fMap (MonoidHom.id (GQ l)) (chRep T'.χ2) (resCoef E (chRep T'.χ2))).2 LinearMap.id (fun _ _ => rfl) δ' hδ')
  exact ⟨δ, (z1fMap (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) (chRep T.χ2)).2 LinearMap.id (fun _ _ => rfl) δ hδ,
    fun g => congrFun hδp g⟩
