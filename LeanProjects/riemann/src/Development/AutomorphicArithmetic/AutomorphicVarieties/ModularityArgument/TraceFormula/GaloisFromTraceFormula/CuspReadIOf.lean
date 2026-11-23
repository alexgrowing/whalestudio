import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

private theorem readJ_or {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K W m₀}
    {X : Set (CuspSub E N)} {ι : Type} [Fintype ι] {P : ι → Sm E N → Prop} {Q : Sm E N → Prop}
    (h : ∀ i, ReadJ bad K W m₀ X (P i)) (hQ : ∀ φ, IsAutForm φ → Q φ → ∃ i, P i φ) : ReadJ bad K W m₀ X Q := by
  choose J i D C a b using h
  refine ⟨Σ i, J i, inferInstance, fun j => D j.1 j.2, fun j => C j.1 j.2, fun j => a j.1 j.2, fun φ m B h hm => ?_⟩
  choose c hc using fun k => hQ (φ k) (h k).1.aut (h k).2
  obtain ⟨i₀, h0⟩ := Finite.exists_infinite_fiber c
  have h1 : ∃ᶠ k in atTop, c k = i₀ := Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 h0)
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop h1
  obtain ⟨j, s, hs, hI, u⟩ := b i₀ (fun k => φ (σ k)) (fun k => m (σ k)) (fun k => B (σ k)) (fun k => ⟨(h _).1, e k ▸ hc _⟩)
    fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)
  exact ⟨⟨i₀, j⟩, fun k => σ (s k), hσ.comp hs, hI, u⟩

private theorem readJ_all (hC : CuspCaseJ) (hT : CtCaseJ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {bad : Set (UpperTheory.V.Cj.S.Pl E)} (hb : bad.Finite) (N : ℕ) : ∀ K (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)),
    Lev bad K → FiniteDimensional ℂ W → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
    ReadJ bad K W m₀ X (Excl X) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K W m₀ X hK hW hX
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨Unit, inferInstance, fun _ => CD.nil E, fun _ _ => 0, fun _ => ⟨fun π _ ⟨i, _⟩ => i.elim0,
      fun w _ => ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩⟩, fun φ m B h hm => ⟨(), id, strictMono_id, ?_, fun w hw i => ?_⟩⟩
    · have e0 : m₀ = fun _ => 0 := by
        funext τ
        obtain ⟨k, hk⟩ := (hm τ 1 one_pos).exists
        have hc := Multiset.card_eq_card_of_rel hk
        rw [((h k).1.cap τ).1] at hc
        exact Multiset.card_eq_zero.1 hc.symm
      rw [e0]
      exact fun _ => rfl
    · have e : ∀ k, B k w = 0 := fun k => Multiset.card_eq_zero.1 ((h k).1.sat w hw).2.2.1
      simp only [e]
      exact tendsto_const_nhds
  have ih' : ∀ M < N, ∀ K (W : Submodule ℂ (Kinf E M → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W →
      ReadJ (N := M) bad K W m₀ ∅ fun _ => True := fun M hM K W m₀ hK hW =>
    readJ_or (ι := Unit) (fun _ => ih M hM K W m₀ ∅ hK hW fun _ h => h.elim) fun _ _ _ => ⟨(), fun _ h => h.elim⟩
  refine readJ_or (ι := Option {r : Fin N // 0 < r.1})
    (P := fun o φ => o.elim (IsCuspForm φ ∧ Excl X φ) fun r => ∃ g, constantTerm r.1.1 φ.1 g ≠ 0) ?_ fun φ ha hx => ?_
  · rintro (_ | ⟨⟨r, hr⟩, h0⟩)
    · exact hC E N hN bad K W m₀ X hb hK hW hX
    · obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
      have h0' : 0 < r := h0
      exact hT E r s h0' (by omega) bad (ih' r hr) (ih' s (by omega)) K W m₀ X hK hW
  · by_cases hc : IsCuspForm φ
    · exact ⟨none, hc, hx⟩
    · have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
        hc ((UpperTheory.V.Cm.isCuspForm_iff φ).2 ⟨(UpperTheory.V.Cm.isAutForm_iff φ).1 ha, h2⟩)
      unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
      push Not at h1
      obtain ⟨r, h0, hr, hg⟩ := h1
      exact ⟨some ⟨⟨r, hr⟩, h0⟩, hg⟩

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspReadI_of :
    LevShrink → CuspCaseJ → CtCaseJ → CuspReadI := by
  intro hL hC hT E _ _ _ N K W bad m₀ X ho hW hb hl _ hX
  obtain ⟨K', hle, hK', -⟩ := hL E N bad K ho hl
  obtain ⟨J, i, D, C, a, b⟩ := readJ_all hC hT hb N K' W m₀ X hK' hW hX
  classical
  refine ⟨{j : J // (D j).Inf m₀}, inferInstance, fun j => D j.1, fun j => C j.1, fun j => a j.1, fun j => j.2,
    fun φ m B h hm => ?_⟩
  obtain ⟨j, s, hs, hI, u⟩ := b φ m B (fun k =>
    ⟨⟨(h k).1, (h k).2.1, ⟨fun u hu => (h k).2.2.1.1 u (hle hu), (h k).2.2.1.2⟩, (h k).2.2.2.1, (h k).2.2.2.2.1⟩,
      (h k).2.2.2.2.2⟩) hm
  exact ⟨⟨j, hI⟩, s, hs, u⟩
