import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_tr_indep {X W : Type} [AddCommGroup X] [AddCommMonoid W] (A L : AddSubgroup X) (T T' : Finset X)
    (hT : IsTr A L T) (hT' : IsTr A L T') (F : X → W) (hF : ∀ a, ∀ d ∈ L, F (a + d) = F a) :
    ∑ t ∈ T, F t = ∑ t ∈ T', F t := by
  classical
  have hσ : ∀ t ∈ T, ∃ s, s ∈ T' ∧ t - s ∈ L := fun t ht => (hT'.2 t (hT.1 t ht)).exists
  have hτ : ∀ s ∈ T', ∃ t, t ∈ T ∧ s - t ∈ L := fun s hs => (hT.2 s (hT'.1 s hs)).exists
  choose! σ hσT hσL using hσ
  choose! τ hτT hτL using hτ
  refine Finset.sum_nbij' σ τ hσT hτT ?_ ?_ ?_
  · intro t ht
    refine (hT.2 t (hT.1 t ht)).unique ⟨hτT _ (hσT t ht), ?_⟩ ⟨ht, by simp⟩
    have e : t - τ (σ t) = (t - σ t) + (σ t - τ (σ t)) := by abel
    rw [e]; exact L.add_mem (hσL t ht) (hτL _ (hσT t ht))
  · intro s hs
    refine (hT'.2 s (hT'.1 s hs)).unique ⟨hσT _ (hτT s hs), ?_⟩ ⟨hs, by simp⟩
    have e : s - σ (τ s) = (s - τ s) + (τ s - σ (τ s)) := by abel
    rw [e]; exact L.add_mem (hτL s hs) (hσL _ (hτT s hs))
  · intro t ht
    have := hF (σ t) _ (hσL t ht)
    rw [← this]; congr 1; abel

theorem isTr_filter {X : Type} [AddCommGroup X] (A A' H : AddSubgroup X) (hHA : H ≤ A) (U : Finset X)
    (hU : IsTr A' H U) (hAA : A ≤ A') [DecidablePred (· ∈ A)] : IsTr A H (U.filter (· ∈ A)) := by
  refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, fun a ha => ?_⟩
  obtain ⟨u, ⟨hu, hau⟩, huniq⟩ := hU.2 a (hAA ha)
  have huA : u ∈ A := by
    have e : u = a - (a - u) := by abel
    rw [e]; exact A.sub_mem ha (hHA hau)
  refine ⟨u, ⟨Finset.mem_filter.2 ⟨hu, huA⟩, hau⟩, fun t ⟨ht, hat⟩ => huniq t ⟨(Finset.mem_filter.1 ht).1, hat⟩⟩

theorem conj_circle_eq_one {z : Circle} (hz : z = 1) : starRingEnd ℂ (z : ℂ) = 1 := by simp [hz]

theorem sum_char {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {R : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (u : Fin (m + 1) → k) (hu : u ∈ A') [Decidable (u ∈ A)] :
    ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) = if u ∈ A then (R.card : ℂ) else 0 := by
  split_ifs with huA
  · rw [Finset.sum_congr rfl fun η hη => conj_circle_eq_one (hR.1 η hη u huA), Finset.sum_const, nsmul_eq_mul,
      mul_one]
  · obtain ⟨η₀, hη₀A, hη₀u⟩ := GlobalTheory.T.exists_character_separating_lattice k ψ hψ hψ1 (m + 1) A hA.1 hA.2 u huA
    set F : (Fin (m + 1) → k) → ℂ := fun η => starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) with hFdef
    have hF : ∀ a, ∀ d ∈ ann ψ A', F (a + d) = F a := by
      intro a d hd
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul, hd u hu, Circle.coe_one,
        map_one, mul_one]
    have e := sum_translate_transversal (ann ψ A) (ann ψ A') R hR.1 hR.2 F hF η₀ hη₀A
    have e2 : ∀ η, F (η + η₀) = F η * starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) := by
      intro η
      simp only [hFdef, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    simp only [e2, ← Finset.sum_mul] at e
    have hc : starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) ≠ 1 := by
      intro hc
      apply hη₀u
      have : ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) = 1 := by
        have := congrArg (starRingEnd ℂ) hc
        simpa using this
      exact Circle.coe_inj.1 (by simpa using this)
    have : (∑ η ∈ R, F η) * (starRingEnd ℂ ((ψ (η₀ ⬝ᵥ u) : Circle) : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hc)

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V}

theorem avg_decomp_pf (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') (hAA : A ≤ A') {R T : Finset (Fin (m + 1) → k)}
    (hR : IsTr (ann ψ A) (ann ψ A') R) (hT : IsTr A' A T) (v : V) :
    (R.card : ℂ) • avg ψ h π ξ A v = (T.card : ℂ) • ∑ η ∈ R, avg ψ h π (ξ + η) A' v := by
  classical
  obtain ⟨⟨H, S⟩, hHA, hHo, hHv, hHξ, hS1, hS2⟩ := avgData_exists ψ h π hψ hπ ξ A hA v
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_coset_reps_open_in_compact (Fin (m + 1) → k) A' H hA'.1 hHo (hHA.trans hAA)
  set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
    with hfdef

  have hav : avg ψ h π ξ A v = ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t :=
    PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ ξ hA v ⟨H, S⟩ ⟨hHA, hHo, hHv, hHξ, hS1, hS2⟩
  have hav' : ∀ η ∈ R, avg ψ h π (ξ + η) A' v =
      ((U.card : ℂ)⁻¹) • ∑ u ∈ U, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u := by
    intro η hη
    have hdat : AvgData ψ h π (ξ + η) A' v ⟨H, U⟩ := by
      refine ⟨hHA.trans hAA, hHo, hHv, fun a ha => ?_, hU1, hU2⟩
      rw [add_dotProduct, AddChar.map_add_eq_mul, hHξ a ha, hR.1 η hη a (hHA ha), one_mul]
    rw [PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_eq_of_data ψ h π hψ hπ (ξ + η) hA' v ⟨H, U⟩ hdat]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hfdef, smul_smul, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    ring_nf

  have hsum : ∑ η ∈ R, avg ψ h π (ξ + η) A' v = ((U.card : ℂ)⁻¹ * (R.card : ℂ)) • ∑ u ∈ U.filter (· ∈ A), f u := by
    rw [Finset.sum_congr rfl hav', ← Finset.smul_sum, Finset.sum_comm]
    have e1 : ∀ u ∈ U, ∑ η ∈ R, starRingEnd ℂ ((ψ (η ⬝ᵥ u) : Circle) : ℂ) • f u =
        (if u ∈ A then (R.card : ℂ) else 0) • f u := fun u hu => by
      rw [← Finset.sum_smul, sum_char hψ hψ1 hA hR u (hU1 u hu)]
    rw [Finset.sum_congr rfl e1, Finset.sum_filter, mul_smul]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp

  have hper : ∀ a, ∀ d ∈ H, f (a + d) = f a := by
    intro a d hd
    simp only [hfdef, dotProduct_add, AddChar.map_add_eq_mul, hHξ d hd, mul_one, colEl_add, map_mul,
      Module.End.mul_apply, hHv d hd]
  have hind : ∑ u ∈ U.filter (· ∈ A), f u = ∑ t ∈ S, f t :=
    sum_tr_indep A H _ S (isTr_filter A A' H hHA U ⟨hU1, hU2⟩ hAA) ⟨hS1, hS2⟩ f hper
  have cU : U.card = H.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' H U (hHA.trans hAA) hU1 hU2
  have cS : S.card = H.relIndex A := GlobalTheory.T.card_coset_reps_eq_relIndex _ A H S hHA hS1 hS2
  have cT : T.card = A.relIndex A' := GlobalTheory.T.card_coset_reps_eq_relIndex _ A' A T hAA hT.1 hT.2
  have cmul : U.card = S.card * T.card := by
    rw [cU, cS, cT, AddSubgroup.relIndex_mul_relIndex H A A' hHA hAA]
  have hS0 : (S.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hS2 0 A.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  have hT0 : (T.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hT.2 0 A'.zero_mem
    exact_mod_cast (Finset.card_pos.2 ⟨t, ht.1⟩).ne'
  rw [hsum, hind, hav, smul_smul, smul_smul, cmul]
  congr 1
  push_cast
  field_simp

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
