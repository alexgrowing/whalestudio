import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma fixed_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ν : Measure α) (Q : E →L[ℂ] E) (f : α → E) (hf : ∀ m, Q (f m) = f m) : Q (∫ m, f m ∂ν) = ∫ m, f m ∂ν := by
  by_cases hi : Integrable f ν
  · rw [← Q.integral_comp_comm hi]
    exact integral_congr_ae (Eventually.of_forall hf)
  · rw [integral_undef hi, map_zero]

private lemma kills_irreducible {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : GroundTheory.Automorphic.UnitaryRep G H) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (P : H →L[ℂ] H) (v : H) (hv : v ∈ τ) (hv0 : v ≠ 0) (hall : ∀ g, P (π g v) = 0) (u : H) (hu : u ∈ τ) : P u = 0 := by
  let ρ : Submodule ℂ H :=
    { carrier := {x | x ∈ τ ∧ ∀ g, P (π g x) = 0}
      add_mem' := fun {a b} ha hb => ⟨τ.add_mem ha.1 hb.1, fun g => by rw [map_add, map_add, ha.2 g, hb.2 g, add_zero]⟩
      zero_mem' := ⟨τ.zero_mem, fun g => by rw [map_zero, map_zero]⟩
      smul_mem' := fun c x hx => ⟨τ.smul_mem c hx.1, fun g => by rw [map_smul, map_smul, hx.2 g, smul_zero]⟩ }
  have hmem : ∀ x, x ∈ ρ ↔ x ∈ τ ∧ ∀ g, P (π g x) = 0 := fun x => Iff.rfl
  have hclρ : IsClosed (ρ : Set H) := by
    have he : (ρ : Set H) = (τ : Set H) ∩ ⋂ g, {x | P (π g x) = 0} := by
      ext x
      simp only [SetLike.mem_coe, hmem, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [he]
    exact hcl.inter (isClosed_iInter fun g => isClosed_eq (P.continuous.comp (π g).continuous) continuous_const)
  have hinvρ : ∀ g, ∀ x ∈ ρ, π g x ∈ ρ := fun h x hx =>
    (hmem _).2 ⟨hinv h x ((hmem x).1 hx).1, fun g => by
      rw [← GroundTheory.Automorphic.UnitaryRep.map_mul_apply]; exact ((hmem x).1 hx).2 _⟩
  have hvρ : v ∈ ρ := (hmem v).2 ⟨hv, hall⟩
  rcases hirr ρ (fun x hx => ((hmem x).1 hx).1) hclρ hinvρ with h | h
  · exact absurd (by simpa [h] using hvρ) hv0
  · have hu' : u ∈ ρ := h ▸ hu
    have := ((hmem u).1 hu').2 1
    rwa [GroundTheory.Automorphic.UnitaryRep.map_one_apply] at this

private lemma occ_abs {G H A ι α : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [MeasurableSpace α] (π : GroundTheory.Automorphic.UnitaryRep G H) (ν : Measure α) (gl : ι → A → G)
    (un : ι → α → G) (t : ι → α → ℂ) (P : ι → H →L[ℂ] H) (τ Z : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hun : ∀ i m, ∃ a, un i m = gl i a) (hcomm : ∀ i j, i ≠ j → ∀ a b, Commute (gl i a) (gl j b))
    (hdec : ∀ i g, ∃ a h, g = gl i a * h ∧ ∀ b, Commute h (gl i b)) (hPP : ∀ i, P i ∘L P i = P i)
    (hPc : ∀ i h, (∀ b, Commute h (gl i b)) → Commute (P i) (π h))
    (hPint : ∀ i v, P i v = ∫ m, t i m • π (un i m) v ∂ν) (hZτ : Z ≤ τ) (hZ : Z ≠ ⊥)
    (hgl : ∀ i a, ∀ v ∈ Z, π (gl i a) v ∈ Z) (hPi : ∀ i, ∀ v ∈ Z, P i v ∈ Z) (hocc : ∀ i, ∃ v ∈ τ, P i v ≠ 0)
    (s : Finset ι) : ∃ v ∈ Z, v ≠ 0 ∧ ∀ i ∈ s, P i v = v := by
  have hsw : ∀ i h, (∀ b, Commute h (gl i b)) → ∀ x, P i (π h x) = π h (P i x) :=
    fun i h hc x => DFunLike.congr_fun (hPc i h hc).eq x
  have key : ∀ i, ∀ v ∈ τ, v ≠ 0 → ∃ a, P i (π (gl i a) v) ≠ 0 := by
    intro i v hv hv0
    by_contra hno
    push_neg at hno
    have hall : ∀ g, P i (π g v) = 0 := by
      intro g
      obtain ⟨a, h, rfl, hc⟩ := hdec i g
      rw [(hc a).eq.symm, GroundTheory.Automorphic.UnitaryRep.map_mul_apply, hsw i h hc, hno a, map_zero]
    obtain ⟨u, hu, hu0⟩ := hocc i
    exact hu0 (kills_irreducible π τ hcl hinv hirr (P i) v hv hv0 hall u hu)
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    exact ⟨v, hv, hv0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨v, hvZ, hv0, hvs⟩ := ih
    obtain ⟨a, ha⟩ := key i v (hZτ hvZ) hv0
    refine ⟨P i (π (gl i a) v), hPi _ _ (hgl _ _ _ hvZ), ha, ?_⟩
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact DFunLike.congr_fun (hPP j) _
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      have hw : P j (π (gl i a) v) = π (gl i a) v := by
        rw [hsw j _ (fun b => hcomm i j hne a b), hvs j hj]
      rw [hPint i]
      refine fixed_integral ν (P j) _ fun m => ?_
      obtain ⟨c, hc⟩ := hun i m
      rw [map_smul, hc, hsw j _ (fun b => hcomm i j hne c b), hw]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.occ :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ (Z : Submodule ℂ (LL μ)) (s : Finset ι) (n : ι → ℕ) (q : ι → ℤ), Z ≤ τ → Z ≠ ⊥ → (∀ i a, ∀ v ∈ Z, rightRegularRep (Gam K 2) μ (C.gl i a) v ∈ Z) →
      (∀ i n q, ∀ v ∈ Z, C.Pi μ i n q v ∈ Z) → (∀ i, ∃ v ∈ τ, C.Pi μ i (n i) (q i) v ≠ 0) → ∃ v ∈ Z, v ≠ 0 ∧ ∀ i ∈ s, C.Pi μ i (n i) (q i) v = v := by
  intro K _ _ _ ι _ C μ _ τ hτ Z s n q hZτ hZ hgl hPi hocc
  obtain ⟨-, -, hun, -, -, hcomm, -, hdec, -⟩ := coLaws K ι C
  have hP' : ∀ i, ∃ P : LL μ →L[ℂ] LL μ, (∀ v, P v = C.Pi μ i (n i) (q i) v) ∧ P ∘L P = P ∧
      ∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (rightRegularRep (Gam K 2) μ h) := fun i => by
    obtain ⟨P, h₁, -, h₂, -, h₃, -⟩ := (piLaws K ι C μ).1 i (n i) (q i)
    exact ⟨P, h₁, h₂, h₃⟩
  choose P hPv hPP hPc using hP'
  obtain ⟨v, hv, hv0, hvs⟩ := occ_abs (rightRegularRep (Gam K 2) μ) μK C.gl C.un (fun i => T (n i) (q i)) P τ Z hτ.closed hτ.inv hτ.irr
    (fun i m => ⟨_, hun i m⟩) hcomm hdec hPP hPc (fun i v => hPv i v) hZτ hZ hgl
    (fun i v hv => by rw [hPv]; exact hPi _ _ _ _ hv) (fun i => by
      obtain ⟨v, hv, h⟩ := hocc i
      exact ⟨v, hv, by rwa [hPv]⟩) s
  exact ⟨v, hv, hv0, fun i hi => by rw [← hPv]; exact hvs i hi⟩
