import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConditionsConjUnitaryKeepsStdLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLocalConditionConjIffFrameChangeTrivialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceClassMatchingCouplingCosetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

set_option maxHeartbeats 2000000 in
theorem match_idx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∃ (c0f : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → (I.stp u I.mu0 i).Cl) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) ∧ (a = I.mu0 → ∀ β, t β = 1) ∧ ∀ β, ∃ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) → (∀ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ → ∃ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr (c0f β).1 κ0) ∧ (∀ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ) := by
  intro B X I hI _hP l u a Q i hi h1 hm hQ
  by_cases ha : a = I.mu0
  · subst ha
    haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
    refine ⟨fun β => β.2.choose, fun _ => 1, fun _ => ⟨DecoF.base _ _ _ _ _, isPtOf_base _, rfl⟩,
      fun _ _ _ => map_one _, fun _ _ => rfl, fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec, fun s _ => ?_⟩⟩
    simp only [inv_one, one_mul, mul_one]
    exact ⟨fun κ hκ => ⟨κ, hκ, rfl⟩, fun κ0 hκ0 => ⟨κ0, hκ0⟩⟩
  · have key : ∀ β : Chart I u a i, ∃ (c0 : (I.stp u I.mu0 i).Cl) (t : GA B (B.R.N i)),
        (∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧
        (∀ (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
          bc (prV (E := B.host.E) v) t = 1) ∧
        ∃ c, chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
          (∀ κ, LocMv I u a i c (t⁻¹ * s * t) κ → ∃ κ0, LocMv I u I.mu0 i c0 s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧
          (∀ κ0, LocMv I u I.mu0 i c0 s κ0 → ∃ κ, LocMv I u a i c (t⁻¹ * s * t) κ) := by
      intro β
      obtain ⟨b0, x', hx1', hxg', hxc'⟩ := GlobalTheory.T.exists_conj_referenceChartIndex I hI l a i h1 hm (β.2.choose).1
      obtain ⟨c0, rfl, y, hy, hcos⟩ := GlobalTheory.T.exists_reference_class_matching_coupling_coset I hI l u a i h1 hm β.2.choose b0
      let x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal) := fun w => y w * x' w
      have hx1 : i + 1 = B.R.m → ∀ w, x w = y w := fun h w => by simp [x, hx1' h w]
      have hconj : ∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, (fun w => x w * g w * (x w)⁻¹) =
          y * (fun w => x' w * g w * (x' w)⁻¹ : GLG B.fields.E (B.R.N i) (B.primes X).vGs) * y⁻¹ := fun g => by
        funext w
        show y w * x' w * g w * (y w * x' w)⁻¹ = y w * (x' w * g w * (x' w)⁻¹) * (y w)⁻¹
        group
      have hxg : ∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp ↔
          (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp := fun g => by
        rw [hxg' g, hconj g]
        constructor
        · intro h
          exact mul_mem (mul_mem hy h) (inv_mem hy)
        · intro h
          have h2 := mul_mem (mul_mem (inv_mem hy) h) hy
          simpa [mul_assoc] using h2
      have hxc : ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp),
          (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
          (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr g0 := fun g g0 h => by
        have hm' := (hxg' g.1).1 g.2
        rw [hxc' g ⟨_, hm'⟩ (fun w => rfl)]
        have : g0 = ⟨y, hy⟩ * ⟨_, hm'⟩ * (⟨y, hy⟩)⁻¹ := Subtype.ext ((funext h).trans (hconj g.1))
        rw [this, map_mul, map_mul, map_inv, mul_comm (_ * _), ← mul_assoc, inv_mul_cancel, one_mul]
      obtain ⟨t, ht_std, ht_off, ht_res⟩ := GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions I hI l u (B.R.N i) x
      refine ⟨c0, t, ht_std, ht_off, β.2.choose, Subtype.ext β.2.choose_spec, fun s hs => ⟨?_, ?_⟩⟩
      · intro κ hκ
        obtain ⟨hg, hco, hC0, hCQ⟩ := (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u a i hi _ _ κ).1 hκ
        rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res] at hC0
        have hθ : κ.2.2 = 1 := Subtype.ext ((GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).1 hCQ)
        have hmem := (hxg κ.2.1.1).1 κ.2.1.2
        let κ0 : (I.stp u I.mu0 i).G c0.1 := (1, ⟨_, hmem⟩, 1)
        have hg0 : (I.stp u I.mu0 i).gam c0.1 κ0 = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        refine ⟨κ0, (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u I.mu0 i hi _ _ κ0).2 ⟨hg0, ?_, hC0, ?_⟩, ?_⟩
        · refine (hcos κ κ0 hg hg0 hθ fun h => ?_).1 hco
          intro w
          show x w * κ.2.1.1 w * (x w)⁻¹ = y w * κ.2.1.1 w * (y w)⁻¹
          rw [hx1 h w]
        · intro P
          have h0 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ColIn.twistPrimes_reference_tuple_eq_empty I ▸ P.2
          simp at h0
        · have ea : (I.stp u a i).chr (β.2.choose).1 κ = (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.1 *
              (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.2 := rfl
          have e0 : (I.stp u I.mu0 i).chr c0.1 κ0 = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr κ0.2.1 *
              (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr 1 := rfl
          refine ea.trans (Eq.trans ?_ e0.symm)
          rw [hθ, map_one, map_one, mul_one, mul_one]
          exact hxc κ.2.1 κ0.2.1 fun w => rfl
      · intro κ0 hκ0
        obtain ⟨hg, hco, hC0, -⟩ := (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u I.mu0 i hi _ _ κ0).1 hκ0
        have hmem : (fun w => (x w)⁻¹ * κ0.2.1.1 w * x w) ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp := by
          have e1 : (fun w => x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹) = κ0.2.1.1 := funext fun w => by group
          refine (hxg _).2 ?_
          rw [e1]
          exact κ0.2.1.2
        let κ : (I.stp u a i).G (β.2.choose).1 := (1, ⟨_, hmem⟩, 1)
        have hgk : (I.stp u a i).gam (β.2.choose).1 κ = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        have e : (fun w => x w * κ.2.1.1 w * (x w)⁻¹) = κ0.2.1.1 := by
          funext w
          show x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹ = κ0.2.1.1 w
          group
        refine ⟨κ, (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u a i hi _ _ κ).2 ⟨hgk, ?_, ?_, ?_⟩⟩
        · refine (hcos κ κ0 hgk hg rfl fun h => ?_).2 hco
          intro w
          show κ0.2.1.1 w = y w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (y w)⁻¹
          rw [hx1 h w]
          group
        · rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res, e]
          exact hC0
        · exact (GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).2 rfl
    exact ⟨fun β => (key β).choose, fun β => (key β).choose_spec.choose, fun β => (key β).choose_spec.choose_spec.1,
      fun β => (key β).choose_spec.choose_spec.2.1, fun h => absurd h ha, fun β => (key β).choose_spec.choose_spec.2.2⟩

end GlobalTheory.Mem.Col2.TC.ChTw.Match
