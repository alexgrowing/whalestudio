import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (M : ℕ)
    (hM : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S') (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : toGS Ω V.S' (W.resP L Ω g) = 1 := congrArg Subtype.val hg
  have hNS : W.resP L Ω g ∈ NS Ω V.S' := by
    unfold toGS at hg'
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg'
  let Kp : Subgroup (G (W.Lp L) Ω) := K.map (W.resP L Ω)
  have hKp : IsClosed (Kp : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hK.isCompact).image W.continuous_resP).isClosed
  have hX : ∀ v : W.Plc (W.Lp L), v ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∀ τ ∈ Ine (F := W.Lp L) A, τ ∈ Kp := by
    intro v hv A hA τ hτ
    obtain ⟨t, ht⟩ := s.unr A v hA hτ
    have hM' : ¬ A.valuation (M : Ω) < 1 := by
      rw [natCast_place hA]
      exact fun h => hv (hM v h)
    have htI : t ∈ Ine (F := L) A := by
      have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) A := by
        rw [ht]
        exact hτ
      exact h1
    exact ⟨t, hI A hM' htI, ht⟩
  have hNSle : NS Ω V.S' ≤ Kp := by
    letI : MulAction (G (W.Lp L) Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
    unfold NS
    apply Subgroup.topologicalClosure_minimal _ _ hKp
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hconj⟩ := hy
    simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, A, hA, hxA⟩ := hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    subst hc
    have hlift : IsLift (RingEquiv.refl (W.Lp L)) (c⁻¹).toRingEquiv := fun z => (c⁻¹).commutes z
    have hmem : ∀ z : Ω, (c⁻¹).toRingEquiv z ∈ A ↔ z ∈ c • A := by
      intro z
      exact (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := c) (S := A) (x := z)).symm
    have h1 := conjGal_mem_Ine hlift hmem hxA
    have heq : conjGal hlift x = c * x * c⁻¹ := AlgEquiv.ext fun z => rfl
    have hcA : ∀ z : Ω, c.toRingEquiv z ∈ c • A ↔ z ∈ A := by
      intro z
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := c) (S := A) (x := z)
    have hplace : IsPlaceOver (c • A) v := by
      intro z
      have hz : c.toRingEquiv ((algebraMap (W.Lp L) Ω) (z : W.Lp L)) = (algebraMap (W.Lp L) Ω) (z : W.Lp L) :=
        c.commutes _
      rw [← hz, val_lt_one hcA]
      exact hA z
    rw [← heq]
    exact hX v hv (c • A) hplace _ h1
  obtain ⟨g', hg'K, hg'eq⟩ := hNSle hNS
  have hgg : g' = g := by
    ext z
    exact DFunLike.congr_fun hg'eq z
  rw [← hgg]
  exact hg'K

private theorem coef_algebraMap_padicInt_eq (l : ℕ) [Fact l.Prime] (c₁ : Coef l) (z : ℤ_[l]) :
    ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O z) : c₁.O) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := by
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  change algebraMap ℤ_[l] (PadicAlgCl l) z = _
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem UpperTheory.frame_criterion_level_kernel :
    UpperTheory.V.Pr.CrKap := by
  unfold UpperTheory.V.Pr.CrKap
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS c₁ ι n ka hka hO
  have hcont : Continuous ka := hka.alg.1
  let f : G L Ω →* c₁.O :=
    { toFun := fun g => ⟨(ka g : Qbar l), hO g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  let ka0 : G L Ω →* (c₁.O)ˣ := f.toHomUnits
  have hMS : ∀ v : W.Plc (W.Lp L), ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → v ∈ V.S' := by
    intro v hv
    rw [hS]
    by_cases hl : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl hl
    · exact Or.inr (Or.inl ((x.St v).2 ⟨hv, hl⟩))
  have hKc : IsClosed (ka.ker : Set (G L Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hcont
  have hker : V.pr.ker ≤ ka.ker :=
    ker_pr_le V M hMS ka.ker hKc (fun A hA t ht => (MonoidHom.mem_ker).2 (hka.unr A hA t ht))
  have hker0 : V.pr.ker ≤ ka0.ker := by
    intro g hg
    have h1 : ka g = 1 := hker hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply Subtype.ext
    change (ka g : Qbar l) = ((1 : (Qbar l)ˣ) : Qbar l)
    rw [h1]
  have hsurj := pr_surj V
  let κ : V.frame.G₀ →* (c₁.O)ˣ :=
    V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨ka0, hker0⟩
  have hκ : ∀ g, κ (V.pr g) = ka0 g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  let φ : (c₁.O)ˣ →* (Qbar l)ˣ := Units.map (c₁.O.val : c₁.O →* Qbar l)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hab
  have hφka : ∀ g, φ (ka0 g) = ka g := fun g => Units.ext rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro g
    rw [hκ g]
    rfl
  · rw [(X.So.adicCont l c₁).2]
    haveI : IsClosed (NS Ω V.S' : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
    have hprc : Continuous V.pr := V.pr_cont W.continuous_resP
    have hq : Topology.IsQuotientMap V.pr := IsClosedMap.isQuotientMap hprc.isClosedMap hprc hsurj
    have hfun : (fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr =
        fun g => (⟨(ka g : Qbar l), hO g⟩ : c₁.O) := by
      funext g
      simp only [Function.comp_apply, hκ]
      rfl
    have hc2 : Continuous ((fun g : ↥V.η.ker => ((κ g : (c₁.O)ˣ) : c₁.O)) ∘ V.pr) := by
      rw [hfun]
      exact (Units.continuous_val.comp hcont).subtype_mk hO
    exact hq.continuous_iff.2 hc2
  · intro g0
    obtain ⟨g, rfl⟩ := hsurj g0
    have hr : V.η (toGS Ω V.S' (W.resP L Ω g)) = 1 := (V.hη _).2 ⟨g, rfl⟩
    have hτr : s.c * W.resP L Ω g * s.c⁻¹ ∈ (W.resP L Ω).range := by
      apply (V.hη _).1
      simp only [map_mul, map_inv, hr, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hτr
    have hconjpr : V.frame.conj (V.pr g) = V.pr g' := by
      apply Subtype.ext
      change toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω g) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
    have hσ : galEmb ℚ L Ω g' = σ * galEmb ℚ L Ω g * σ⁻¹ := by
      rw [← galEmb_resP g', ← galEmb_resP g, hg', map_mul, map_mul, map_inv, x.c]
    have hk := hka.conj g g' hσ
    have he : φ (V.frame.eps c₁.O c₁.O (V.pr g)) = cycBar L Ω l g := by
      apply Units.ext
      have hε : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
      change ((algebraMap c₁.O c₁.O (algebraMap ℤ_[l] c₁.O ((V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]))) : c₁.O) : Qbar l) =
        algebraMap ℚ_[l] (Qbar l) (((cycZ L Ω l g : ℤ_[l])) : ℚ_[l])
      rw [hε, coef_algebraMap_padicInt_eq]
    rw [hconjpr, hκ, hκ]
    apply hφ
    rw [map_mul, map_zpow, hφka, hφka, he]
    exact hk
