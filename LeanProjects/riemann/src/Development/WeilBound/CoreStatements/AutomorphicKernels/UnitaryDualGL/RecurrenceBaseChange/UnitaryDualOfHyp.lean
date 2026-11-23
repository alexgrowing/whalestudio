import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.RecurrenceBaseChange.RecSpehQuot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

noncomputable section

namespace PositivityTheory.UdReth

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cusp_reg {R : Ranks} {H : Host R} {n : ℕ} {V : Submodule ℂ (Sm H.E n)} (m : (H.E →+* ℂ) → Multiset ℂ)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hnd : ∀ τ, (m τ).Nodup)
    (hg : ∃ g : ℂ, ∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = g + k) {a d : ℕ} (hd : 1 ≤ d) (P : CuspSub H.E a)
    (h3 : ∀ τ m', HasInfCharGL V τ m' → ∃ m0, P.HasInfChar τ m0 ∧ m' = spehInf d m0) :
    (∀ τ : H.E →+* ℂ, ∃ m0 : Multiset ℂ, P.HasInfChar τ m0 ∧ m0.Nodup) ∧
      (∃ f : ℂ, ∀ τ m0, P.HasInfChar τ m0 → ∀ z ∈ m0, ∃ k : ℤ, z = f + k) := by
  obtain ⟨g, hg⟩ := hg
  have key : ∀ τ m0, P.HasInfChar τ m0 → m τ = spehInf d m0 := fun τ m0 h0 => by
    obtain ⟨m1, hm1, e⟩ := h3 τ (m τ) (hm τ)
    rw [e, CuspSub.HasInfChar.unique hm1 h0]
  have hle : ∀ m0 : Multiset ℂ, m0.map (· + (((d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ spehInf d m0 := fun m0 => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    unfold spehInf
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
    exact Multiset.le_add_right _ _
  refine ⟨fun τ => ?_, ⟨g - (((d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)), fun τ m0 h0 z hz => ?_⟩⟩
  · obtain ⟨m1, hm1, e⟩ := h3 τ (m τ) (hm τ)
    refine ⟨m1, hm1, ?_⟩
    have h5 : (spehInf d m1).Nodup := by rw [← e]; exact hnd τ
    exact (Multiset.nodup_of_le (hle m1) h5).of_map _
  · have hz' : z + (((d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ m τ := by
      rw [key τ m0 h0]
      exact Multiset.mem_of_le (hle m0) (Multiset.mem_map_of_mem _ hz)
    obtain ⟨k, hk⟩ := hg τ _ hz'
    exact ⟨k, by linear_combination hk⟩

theorem exists_part' {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (hMW : DiscreteSpectrum H.E) (hT : TempCsd H.E) (hS : RecSpehT rc) (hC : CuspRead rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : IsCsdGL V)
    (m : (H.E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hnd : ∀ τ, (m τ).Nodup)
    (hg : ∃ g : ℂ, ∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = g + k) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hd : 1 ≤ d := Nat.pos_of_mul_pos_left (had ▸ hn)
  obtain ⟨r1, r2⟩ := cusp_reg m hm hnd hg hd P h3
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha (h1 hc)
  refine ⟨⟨a, π, d⟩, ha, hd, c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, -, q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h σ σ' (hT a P ha (h1 hc) r1 r2 w σ l) q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m0, hm0, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m0 hm0]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_parts' {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (hNT : GlobalTheory.Published.BaseChangeDefiniteUnitary)
    (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hMW : DiscreteSpectrum H.E) (hT : TempCsd H.E)
    (hP : RecProd rc) (hS : RecSpehT rc) (hSat : RecSatake rc) (hC : CuspRead rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U)
    (hw : ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  have hnd : ∀ i τ, (m i τ).Nodup := fun i τ => by
    obtain ⟨lam, hl⟩ := hw τ
    have e := bc.weight τ lam hl
    have hle : m i τ ≤ ∑ j, m j τ :=
      Finset.single_le_sum (f := fun j => m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    exact Multiset.nodup_of_le hle (e ▸ nodup_infOfWeight lam)
  have hg : ∀ i, ∃ g : ℂ, ∀ τ, ∀ z ∈ m i τ, ∃ k : ℤ, z = g + k := fun i => by
    refine ⟨((n : ℂ) - 1) / 2, fun τ z hz => ?_⟩
    obtain ⟨lam, hl⟩ := hw τ
    have e := bc.weight τ lam hl
    have hle : m i τ ≤ ∑ j, m j τ :=
      Finset.single_le_sum (f := fun j => m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hz' : z ∈ infOfWeight lam := e ▸ Multiset.mem_of_le hle hz
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hz'
    exact ⟨lam.w k - (k : ℕ), by push_cast; ring⟩
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    exists_part' hMW hT hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (m i) (bc.inf i) (hnd i) (hg i)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd hB _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · change m i τ = m j τ
      rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

end PositivityTheory.UdReth

end
