import Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs

noncomputable section

namespace Formalism.MainNotions.N.Ln34.GenPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

variable {l : ℕ} [Fact l.Prime]

theorem mem_or_inv_mem (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) :
    x ∈ OL LL ∨ x⁻¹ ∈ OL LL := by
  by_cases hx : x = 0
  · left; rw [hx]; exact zero_mem _
  rw [← P.v_O, ← P.v_O]
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hs : P.v LL x + P.v LL x⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h1)
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h2)
  rw [← ha, ← hc] at hs
  rw [← ha] at h1
  rw [← hc] at h2
  have h1' : a < 0 := by exact_mod_cast h1
  have h2' : c < 0 := by exact_mod_cast h2
  have hs' : a + c = 0 := by exact_mod_cast hs
  linarith

theorem valuationRing (P : LocPrime l) (LL : FinExt l) : ValuationRing ↥(OL LL) := by
  refine { cond' := fun a b => ?_ }
  by_cases ha : (a : ↥LL.1) = 0
  · refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    simp [ha]
  by_cases hb : (b : ↥LL.1) = 0
  · refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simp [hb]
  rcases mem_or_inv_mem P LL ((b : ↥LL.1) / a) with h | h
  · refine ⟨⟨_, h⟩, Or.inl ?_⟩
    apply Subtype.ext
    change (a : ↥LL.1) * ((b : ↥LL.1) / a) = b
    field_simp
  · refine ⟨⟨_, h⟩, Or.inr ?_⟩
    apply Subtype.ext
    change (b : ↥LL.1) * ((b : ↥LL.1) / a)⁻¹ = a
    rw [inv_div]
    field_simp

theorem not_isField (P : LocPrime l) (LL : FinExt l) : ¬ IsField ↥(OL LL) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  intro hF
  have hp : l.Prime := Fact.out
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h2 : ((l : ℕ) : ↥LL.1) = 0 := by
      have := congrArg (fun z : ↥(OL LL) => (z : ↥LL.1)) h
      simpa using this
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h2
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hl0
  have hyv : (y : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l])⁻¹) := by
    have h1 := congrArg (fun z : ↥(OL LL) => (z : ↥LL.1)) hy
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h1
    push_cast at h1
    rw [map_inv₀, map_natCast]
    exact eq_inv_of_mul_eq_one_right h1
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l])⁻¹)) := by
    rw [← hyv]
    unfold OL at y
    exact y.2
  have hint' : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have h1 : ‖((l : ℚ_[l])⁻¹)‖ ≤ 1 := by
    rw [← hz]
    exact PadicInt.norm_le_one z
  rw [norm_inv, Padic.norm_p] at h1
  have : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  rw [inv_inv] at h1
  linarith

theorem isDVR (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : ValuationRing ↥(OL LL) := valuationRing P LL
  haveI : IsNoetherianRing ↥(OL LL) := integralClosure.isNoetherianRing (A := ℤ_[l]) (K := ℚ_[l]) ↥LL.1
  exact ((IsDiscreteValuationRing.TFAE ↥(OL LL) (not_isField P LL)).out 1 0).mp (valuationRing P LL)

theorem isFractionRing (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  unfold OL
  exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] _

theorem natCard_emb (K LL : FinExt l) (hg : Good K 1 LL) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let Φ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun σ => LL.1.val.comp σ
  have hinj : Function.Injective Φ := by
    intro σ σ' h
    ext x
    have := congrArg (fun f : ↥K.1 →ₐ[ℚ_[l]] Om l => f x) h
    simpa [Φ] using this
  have hsurj : Function.Surjective Φ := by
    intro σ
    let ψ : Om l →ₐ[ℚ_[l]] Om l := σ.liftNormal (Om l)
    have hψ : ∀ x : ↥K.1, ψ (x : Om l) = σ x := fun x => σ.liftNormal_commutes (Om l) x
    have hmem : ∀ x : ↥K.1, σ x ∈ LL.1 := by
      intro x
      have hx : (x : Om l) ∈ Ks K 1 := hg.2.2.1 x.2
      have := hg.2.2.2 (ψ.comp (Ks K 1).val) ⟨x, hx⟩
      simpa [hψ] using this
    refine ⟨AlgHom.codRestrict σ LL.1.toSubalgebra hmem, ?_⟩
    ext x
    rfl
  rw [Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩, ← Field.finSepDegree_eq_of_isAlgClosed,
    Field.finSepDegree_eq_finrank_of_isSeparable]

theorem card_emb (K LL : FinExt l) (hg : Good K 1 LL) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) =
      finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 := by
  rw [Fintype.card_eq_nat_card, natCard_emb K LL hg, Module.finrank_mul_finrank]

theorem goodCoeffs (P : LocPrime l) (K LL : FinExt l) (hg : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    GoodCoeffs (K := ↥K.1) (Qp := ℚ_[l]) (LL := ↥LL.1) (O := ↥(OL LL)) (V := T.V) := by
  refine ⟨⟨LL.2, ?_⟩, inferInstance, inferInstance, isDVR P LL, isFractionRing LL⟩
  rw [Fintype.card_eq_nat_card, natCard_emb K LL hg]

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem coboundaries_le_bloch_kato (hc : ∀ x, Continuous fun g => ρ g x) (L : Lattice (O := O) ρ) :
    latticeCoboundaries L ≤ latticeFiniteCocycles PD L := by
  intro c hc'
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hc'
  have hcoc : cob ρ x ∈ continuousCocycles ρ := by
    show Continuous (cob ρ x) ∧ ∀ g h, cob ρ x (g * h) = cob ρ x g + ρ g (cob ρ x h)
    refine ⟨?_, fun g h => ?_⟩
    · have e : (cob ρ x : G → V) = fun g => ρ g x + -x := by
        funext g; simp [cob, sub_eq_add_neg]
      rw [e]
      exact (hc x).add continuous_const
    · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
        Module.End.mul_apply, map_sub]
      abel
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hcoc, ?_⟩, ?_⟩
  · rw [Submodule.mem_pi]
    intro g _
    show cob ρ x g ∈ L.T
    simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    exact L.T.sub_mem (L.stable g x hx) hx
  · show cob ρ x ∈ continuousCocycles ρ ∧ ∃ X : TensorProduct Qp V B, ∀ g, TensorProduct.tmul Qp (cob ρ x g) (1 : B) = actVB PD ρ g X - X
    refine ⟨hcoc, TensorProduct.tmul Qp x (1 : B), fun g => ?_⟩
    simp [cob, actVB, TensorProduct.sub_tmul]

theorem lift_gens (hc : ∀ x, Continuous fun g => ρ g x) (L : Lattice (O := O) ρ)
    (s : Finset (LatticeCohomology L)) (hs : Submodule.span O (s : Set (LatticeCohomology L)) = latticeFiniteCohomology PD L) :
    ∃ t : Finset (G → V), t.card ≤ s.card ∧
      Submodule.span O (t : Set (G → V)) ⊔ latticeCoboundaries L = latticeFiniteCocycles PD L := by
  classical
  set N := (latticeCoboundaries L).comap (latticeCocycles L).subtype
  let rep : LatticeCohomology L → ↥(latticeCocycles L) := fun q => (N.mkQ_surjective q).choose
  have hrep : ∀ q, N.mkQ (rep q) = q := fun q => (N.mkQ_surjective q).choose_spec
  set t : Finset (G → V) := s.image (fun q => ((rep q : ↥(latticeCocycles L)) : G → V)) with ht
  refine ⟨t, Finset.card_image_le, ?_⟩
  have hB := coboundaries_le_bloch_kato PD hc L
  have hmem : ∀ q ∈ s, ((rep q : ↥(latticeCocycles L)) : G → V) ∈ latticeFiniteCocycles PD L := by
    intro q hq
    have hq' : q ∈ latticeFiniteCohomology PD L := hs ▸ Submodule.subset_span hq
    obtain ⟨c, hc', hcq⟩ := hq'
    have h1 : N.mkQ (rep q) = N.mkQ c := by rw [hrep]; exact hcq.symm
    have h2 : rep q - c ∈ N := (Submodule.Quotient.eq N).mp h1
    have h3 : ((rep q : ↥(latticeCocycles L)) : G → V) - (c : G → V) ∈ latticeFiniteCocycles PD L := hB h2
    have h4 := (latticeFiniteCocycles PD L).add_mem h3 hc'
    simpa using h4
  apply le_antisymm
  · refine sup_le ?_ hB
    rw [Submodule.span_le]
    intro z hz
    simp only [ht, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact hmem q hq
  · intro p hp
    have hpZ : p ∈ latticeCocycles L := (Submodule.mem_inf.mp hp).1
    set W : Submodule O ↥(latticeCocycles L) :=
      (Submodule.span O (t : Set (G → V)) ⊔ latticeCoboundaries L).comap (latticeCocycles L).subtype with hW
    have hNW : N ≤ W := fun z hz => Submodule.mem_sup_right hz
    have hsW : (s : Set (LatticeCohomology L)) ⊆ W.map N.mkQ := by
      intro q hq
      refine ⟨rep q, ?_, hrep q⟩
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      simp only [ht, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨q, hq, rfl⟩
    have hspan : latticeFiniteCohomology PD L ≤ W.map N.mkQ := by
      rw [← hs, Submodule.span_le]; exact hsW
    have hpf : N.mkQ ⟨p, hpZ⟩ ∈ latticeFiniteCohomology PD L := ⟨⟨p, hpZ⟩, hp, rfl⟩
    have h1 : (⟨p, hpZ⟩ : ↥(latticeCocycles L)) ∈ (W.map N.mkQ).comap N.mkQ := hspan hpf
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hNW] at h1
    exact h1

end Gen

theorem arith {tc sc N r H0 : ℕ} {S : ℤ} (hts : tc ≤ sc) (hs : (sc : ℤ) ≤ H0 + r + S)
    (h0 : H0 ≤ r) (hS : S ≤ (N : ℤ) * r) : tc ≤ 2 * ((N + 1) * r) := by
  have h1 : (tc : ℤ) ≤ sc := by exact_mod_cast hts
  have h2 : (H0 : ℤ) ≤ r := by exact_mod_cast h0
  have h3 : (0 : ℤ) ≤ (N : ℤ) * r := by positivity
  zify
  nlinarith

set_option maxHeartbeats 800000 in
theorem gen_core (LT : LocTheory) (hgen : H1fGeneratorBoundAll LT) (hfon : FontaineRegularity LT) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ 2) (K LL : FinExt l) (hg : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (r : ℕ) (hc : IsCrys ((LT l).PD K) T.ρ) (hr : finrank ↥LL.1 T.V = r) :
    ∃ s : Finset (↥(GK K) → T.V),
      s.card ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      Submodule.span ↥(OL LL) (s : Set (↥(GK K) → T.V)) ⊔ latticeCoboundaries T.L = latticeFiniteCocycles ((LT l).PD K) T.L := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup ↥LL.1 T.V
  have H := hgen l hl K LL hg T
  obtain ⟨s, hspan, hcard⟩ := H (goodCoeffs (LT l) K LL hg T) hc T.cont
  obtain ⟨t, ht, heq⟩ := lift_gens ((LT l).PD K) T.cont T.L s hspan
  refine ⟨t, ?_, heq⟩
  have hsum : ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      ((finrank ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) : ℤ) - finrank ↥LL.1 ↥(FildR ((LT l).PD K) T.ρ τ 0))
      ≤ ∑ _τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (r : ℤ) := by
    apply Finset.sum_le_sum
    intro τ _
    have h1 := ((hfon l K LL T).2 τ).2
    rw [hr] at h1
    have h2 : (0 : ℤ) ≤ finrank ↥LL.1 ↥(FildR ((LT l).PD K) T.ρ τ 0) := Int.natCast_nonneg _
    have h3 : (finrank ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) : ℤ) ≤ r := by exact_mod_cast h1
    linarith
  have hS := hsum.trans (le_of_eq (by
    rw [Finset.sum_const, Finset.card_univ, card_emb K LL hg, nsmul_eq_mul]))
  have hV : (finrank ↥LL.1 T.V : ℤ) = r := by exact_mod_cast hr
  rw [hV] at hcard
  have h0' : finrank ↥LL.1 ↥(H0V T.ρ) ≤ r := hr ▸ Submodule.finrank_le _
  exact arith ht hcard h0' hS

end Formalism.MainNotions.N.Ln34.GenPf

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem generator_bound_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) : genR D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h7, h8, -, -⟩ := hA
  intro l _ hl K LL hg T₁ T₂ F' r S η m h up b hH
  exact GenPf.gen_core D.loc h7 h8 l hl K LL hg T₂ r hH.2.1 hH.2.2.2.1

end Formalism.MainNotions.N.Ln34

end
