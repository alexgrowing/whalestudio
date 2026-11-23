import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongrStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NestVan

section Generic

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] {R : ∀ i, Subgroup (H i)}
  (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i))

theorem niter_update (q : (∀ i, H i) → ℂ) (i : ι) (g : H i) :
    ∀ l : List ι, i ∉ l → ∀ h z, NIter ρ μ q l (Function.update h i g) z ↔ NIter ρ μ (fun x => q (Function.update x i g)) l h z
  | [], _, h, z => by simp only [NIter]
  | j :: l, hi, h, z => by
    have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self ..)
    have hil : i ∉ l := fun e => hi (List.mem_cons_of_mem _ e)
    simp only [NIter]
    constructor
    · rintro ⟨f, hf, hg⟩
      refine ⟨f, hf, fun g' => ?_⟩
      refine (niter_update q i g l hil _ _).1 ?_
      rw [← Function.update_comm hij]
      exact hg g'
    · rintro ⟨f, hf, hg⟩
      refine ⟨f, hf, fun g' => ?_⟩
      rw [Function.update_comm hij]
      exact (niter_update q i g l hil _ _).2 (hg g')

theorem niter_unique (q : (∀ i, H i) → ℂ) : ∀ l : List ι,
    (∀ i ∈ l, ∀ (f : H i → ℂ) (z z' : ℂ), IsQuotIntL1 (ρ i) (μ i) f z → IsQuotIntL1 (ρ i) (μ i) f z' → z = z') →
    ∀ h z z', NIter ρ μ q l h z → NIter ρ μ q l h z' → z = z'
  | [], _, h, z, z', h1, h2 => by simp only [NIter] at h1 h2; rw [h1, h2]
  | i :: l, hu, h, z, z', h1, h2 => by
    simp only [NIter] at h1 h2
    obtain ⟨f, hf, hg⟩ := h1
    obtain ⟨f', hf', hg'⟩ := h2
    have e : f = f' := funext fun g =>
      niter_unique q l (fun j hj => hu j (List.mem_cons_of_mem _ hj)) _ _ _ (hg g) (hg' g)
    subst e
    exact hu i (List.mem_cons_self ..) f z z' hf hf'

theorem niter_zero : ∀ (l : List ι) (h : ∀ i, H i), NIter ρ μ (fun _ => 0) l h 0
  | [], h => by simp only [NIter]
  | i :: l, h => by
    simp only [NIter]
    exact ⟨0, IsQuotIntL1.zero, fun g => niter_zero l _⟩

end Generic

theorem nested_vanish : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → (∀ i ∈ l, Split (A i) (B i) (R i) (K i)) → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)), (∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure) → ∀ (S : Finset (∀ i, H i)) (q : (∀ i, H i) → ℂ) (z : ℂ), (∀ b ∈ S, ∀ i, b i ∈ B i) → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ b ∈ S, InCells A R K l b h) → NIter ρ μ q l 1 z → (∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) → NIter ρ' μ' (fun b : ∀ i, B i => q fun i => a i * (b i).1) l 1 0) → z = 0 := by
  intro ι _ H _ _ _ _ _ _ _ _ A B R K l
  classical
  induction l with
  | nil =>
    intro _ _ ρ μ ρ' μ' _ S q z _ _ _ hN hB
    simp only [NIter] at hN
    have h0 := hB 1 (fun i => (A i).one_mem) (fun _ _ => rfl)
    simp only [NIter] at h0
    have e : (fun i => (1 : ∀ i, H i) i * (((1 : ∀ i, B i) i : B i) : H i)) = 1 := by funext i; simp
    rw [e] at h0
    rw [hN, ← h0]
  | cons i l ih =>
    intro hnd hsp ρ μ ρ' μ' hhaar S q z hSB hBi hsupp hN hB
    have hil : i ∉ l := (List.nodup_cons.1 hnd).1
    have hnd' := (List.nodup_cons.1 hnd).2
    have sp := hsp i (List.mem_cons_self ..)
    obtain ⟨hρ, hμ, hρ', hμ'⟩ := hhaar i (List.mem_cons_self ..)
    haveI := hρ; haveI := hμ; haveI := hρ'; haveI := hμ'
    haveI : (ρ i).IsInvInvariant := sp.uniR _ hρ
    haveI : (ρ' i).IsInvInvariant := sp.uniRB _ hρ'
    haveI : (μ' i).IsMulRightInvariant := sp.uniB _ hμ'
    haveI : LocallyCompactSpace (B i) := sp.clB.locallyCompactSpace
    have hRB : IsClosed (((R i).subgroupOf (B i) : Subgroup (B i)) : Set (B i)) := by
      rw [Subgroup.coe_subgroupOf]; exact sp.clR.preimage continuous_subtype_val
    have hKbc : IsCompact (((K i).subgroupOf (B i) : Subgroup (B i)) : Set (B i)) := by
      rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
      · exact sp.cpt
      · intro x hx; exact ⟨⟨x, sp.le hx⟩, rfl⟩
    have huH : ∀ j ∈ l, ∀ (f : H j → ℂ) (z z' : ℂ), IsQuotIntL1 (ρ j) (μ j) f z → IsQuotIntL1 (ρ j) (μ j) f z' → z = z' := by
      intro j hj f z z' h1 h2
      have spj := hsp j (List.mem_cons_of_mem _ hj)
      obtain ⟨a1, a2, -, -⟩ := hhaar j (List.mem_cons_of_mem _ hj)
      haveI := a1; haveI := a2; haveI : (ρ j).IsInvInvariant := spj.uniR _ a1
      exact IsQuotIntL1.unique spj.clR h1 h2
    have huB : ∀ j ∈ l, ∀ (f : B j → ℂ) (z z' : ℂ), IsQuotIntL1 (ρ' j) (μ' j) f z → IsQuotIntL1 (ρ' j) (μ' j) f z' → z = z' := by
      intro j hj f z z' h1 h2
      have spj := hsp j (List.mem_cons_of_mem _ hj)
      obtain ⟨-, -, a3, a4⟩ := hhaar j (List.mem_cons_of_mem _ hj)
      haveI := a3; haveI := a4; haveI : (ρ' j).IsInvInvariant := spj.uniRB _ a3
      haveI : LocallyCompactSpace (B j) := spj.clB.locallyCompactSpace
      have hRBj : IsClosed (((R j).subgroupOf (B j) : Subgroup (B j)) : Set (B j)) := by
        rw [Subgroup.coe_subgroupOf]; exact spj.clR.preimage continuous_subtype_val
      exact IsQuotIntL1.unique hRBj h1 h2
    let T : Finset (B i) := (S.image fun s => s i).subtype (· ∈ B i)
    have cell : ∀ a ∈ A i, ∀ g : B i, (∃ s ∈ S, ∃ r ∈ R i, ∃ a₀ ∈ A i, ∃ k ∈ K i, a * (g : H i) = r * a₀ * s i * k) →
        ∃ t ∈ T, ∃ r ∈ (R i).subgroupOf (B i), ∃ k ∈ (K i).subgroupOf (B i), g = r * t * k := by
      rintro a ha g ⟨s, hs, r, hr, a₀, ha₀, k, hk, hdec⟩
      have hsB : s i ∈ B i := hSB s hs i
      have hkB : k ∈ B i := sp.le hk
      obtain ⟨e, he⟩ := sp.prod
      obtain ⟨⟨pa, pb⟩, hp⟩ : ∃ p, e.symm r = p := ⟨_, rfl⟩
      have hrp : r = (pa : H i) * pb := by rw [← he (pa, pb), ← hp, e.apply_symm_apply]
      subst hrp
      have hpR := sp.split _ pa.2 _ pb.2 hr
      have key : e (⟨a, ha⟩, g) = e (pa * ⟨a₀, ha₀⟩, pb * ⟨s i, hsB⟩ * ⟨k, hkB⟩) := by
        rw [he, he]
        show a * (g : H i) = ((pa : H i) * a₀) * ((pb : H i) * s i * k)
        rw [hdec, mul_assoc (pa : H i) pb a₀, ← sp.comm a₀ ha₀ pb pb.2]
        simp only [mul_assoc]
      have hq' : g = pb * ⟨s i, hsB⟩ * ⟨k, hkB⟩ := congrArg Prod.snd (e.injective key)
      exact ⟨⟨s i, hsB⟩, Finset.mem_subtype.2 (Finset.mem_image_of_mem _ hs), pb, Subgroup.mem_subgroupOf.2 hpR.2,
        ⟨k, hkB⟩, Subgroup.mem_subgroupOf.2 hk, hq'⟩
    obtain ⟨T', w, -, hW⟩ := GlobalTheory.T.quotientIntegral_finitelyManyCells_weightedSum (B i) ((R i).subgroupOf (B i)) ((K i).subgroupOf (B i)) hRB hKbc sp.opn
      (ρ' i) (μ' i) hρ' inferInstance hμ' inferInstance T
    simp only [NIter] at hN
    obtain ⟨f, hfz, hfg⟩ := hN
    have hf' : ∀ g, NIter ρ μ (fun x => q (Function.update x i g)) l 1 (f g) := fun g =>
      (niter_update ρ μ q i g l hil 1 (f g)).1 (hfg g)
    have fK : ∀ g, ∀ k ∈ K i, f (g * k) = f g := by
      intro g k hk
      have e : (fun x => q (Function.update x i (g * k))) = fun x => q (Function.update x i g) := by
        funext x
        have := (hBi i (List.mem_cons_self ..) (Function.update x i g)).2 k hk
        simpa [Function.update_self, Function.update_idem] using this
      have h1 := hf' (g * k)
      rw [e] at h1
      exact niter_unique ρ μ _ l huH 1 _ _ h1 (hf' g)
    have fL : ∀ r ∈ R i, ∀ x, f (r * x) = f x := (GlobalTheory.QuotZero.left_and_zero sp.clR (ρ i) (μ i) hfz).1
    have fS : ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ r ∈ R i, ∃ a₀ ∈ A i, ∃ k ∈ K i, g = r * a₀ * s i * k := by
      intro g hg
      by_contra hno
      apply hg
      have h0 : NIter ρ μ (fun _ => (0:ℂ)) l 1 (f g) := by
        refine (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι H R ρ μ l 1).2 (fun x => q (Function.update x i g)) _ _ ?_ (hf' g)
        intro x hx
        by_contra hq
        obtain ⟨s, hs, hc⟩ := hsupp (Function.update x i g) (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          rw [Function.update_of_ne hji]; exact hx j (fun hjl => hj (List.mem_cons_of_mem _ hjl))) hq
        obtain ⟨r, hr, a₀, ha₀, k, hk, e⟩ := hc i (List.mem_cons_self ..)
        rw [Function.update_self] at e
        exact hno ⟨s, hs, r, hr, a₀, ha₀, k, hk, e⟩
      exact niter_unique ρ μ _ l huH 1 _ _ h0 (niter_zero ρ μ l 1)
    refine GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct (H i) (A i) (B i) (R i) sp.clA sp.clB sp.clR sp.comm sp.prod sp.split (ρ i) (μ i) (ρ' i) (μ' i)
      hρ inferInstance hμ hρ' inferInstance hμ' f z hfz ?_
    intro a ha
    have h1 := hW (fun b => f (a * b.1))
      (fun r hr g => by
        show f (a * ((r : H i) * g)) = f (a * g)
        rw [← mul_assoc, sp.comm a ha r (r.2), mul_assoc]
        exact fL _ (Subgroup.mem_subgroupOf.1 hr) _)
      (fun k hk g => by
        show f (a * ((g : H i) * k)) = f (a * g)
        rw [← mul_assoc]
        exact fK _ _ (Subgroup.mem_subgroupOf.1 hk))
      (fun g hg => cell a ha g (fS _ hg))
    suffices hsum : ∑ t ∈ T', w t * f (a * t.1) = 0 by rw [hsum] at h1; exact h1
    let q' : (∀ j, H j) → ℂ := fun x => ∑ t ∈ T', w t * q (Function.update x i (a * t.1))
    have hq'N : NIter ρ μ q' l 1 (∑ t ∈ T', w t * f (a * t.1)) :=
      (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι H R ρ μ l 1).1 (B i) T' w (fun t => f (a * t.1))
        (fun t x => q (Function.update x i (a * t.1))) (fun t _ => hf' _)
    refine ih hnd' (fun j hj => hsp j (List.mem_cons_of_mem _ hj)) ρ μ ρ' μ'
      (fun j hj => hhaar j (List.mem_cons_of_mem _ hj)) S q' _ hSB ?_ ?_ hq'N ?_
    · intro j hj x
      have hji : j ≠ i := fun e => hil (e ▸ hj)
      have hI := fun y => hBi j (List.mem_cons_of_mem _ hj) y
      constructor
      · intro r hr
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        have := (hI (Function.update x i (a * t.1))).1 r hr
        rw [Function.update_of_ne hji, Function.update_comm hji.symm] at this
        exact this
      · intro k hk
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        have := (hI (Function.update x i (a * t.1))).2 k hk
        rw [Function.update_of_ne hji, Function.update_comm hji.symm] at this
        exact this
    · intro x hx hne
      obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hq : q (Function.update x i (a * t.1)) ≠ 0 := right_ne_zero_of_mul ht
      obtain ⟨s, hs, hc⟩ := hsupp _ (fun j hj => by
        have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
        rw [Function.update_of_ne hji]; exact hx j (fun hjl => hj (List.mem_cons_of_mem _ hjl))) hq
      refine ⟨s, hs, fun j hj => ?_⟩
      have hji : j ≠ i := fun e => hil (e ▸ hj)
      have := hc j (List.mem_cons_of_mem _ hj)
      rwa [Function.update_of_ne hji] at this
    · intro a' ha' ha'1
      let a'' : ∀ j, H j := Function.update a' i a
      have ha'' : ∀ j, a'' j ∈ A j := fun j => by
        by_cases hj : j = i
        · subst hj; simp [a'', ha]
        · simp only [a'', Function.update_of_ne hj]; exact ha' j
      have ha''1 : ∀ j, j ∉ i :: l → a'' j = 1 := fun j hj => by
        have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
        simp only [a'', Function.update_of_ne hji]; exact ha'1 j (fun hjl => hj (List.mem_cons_of_mem _ hjl))
      have hB'' := hB a'' ha'' ha''1
      simp only [NIter] at hB''
      obtain ⟨f₁, hf₁0, hf₁g⟩ := hB''
      let Qa : (∀ j, B j) → ℂ := fun b => q fun j => a'' j * (b j).1
      have hf₁' : ∀ g, NIter ρ' μ' (fun b => Qa (Function.update b i g)) l 1 (f₁ g) := fun g =>
        (niter_update ρ' μ' Qa i g l hil 1 (f₁ g)).1 (hf₁g g)
      have hQu : ∀ (b : ∀ j, B j) (g : B i),
          Qa (Function.update b i g) = q (Function.update (fun j => a'' j * (b j).1) i (a * g.1)) := by
        intro b g
        show (q fun j => a'' j * (Function.update b i g j).1) = _
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [a'']
        · simp [Function.update_of_ne hj]
      have f₁K : ∀ g, ∀ k ∈ (K i).subgroupOf (B i), f₁ (g * k) = f₁ g := by
        intro g k hk
        have e : (fun b => Qa (Function.update b i (g * k))) = fun b => Qa (Function.update b i g) := by
          funext b
          rw [hQu, hQu]
          have := (hBi i (List.mem_cons_self ..) (Function.update (fun j => a'' j * (b j).1) i (a * g.1))).2 k
            (Subgroup.mem_subgroupOf.1 hk)
          simpa [Function.update_self, Function.update_idem, mul_assoc] using this
        have h1 := hf₁' (g * k)
        rw [e] at h1
        exact niter_unique ρ' μ' _ l huB 1 _ _ h1 (hf₁' g)
      have f₁L := (GlobalTheory.QuotZero.left_and_zero hRB (ρ' i) (μ' i) hf₁0).1
      have f₁S : ∀ g, f₁ g ≠ 0 → ∃ s ∈ S, ∃ r ∈ R i, ∃ a₀ ∈ A i, ∃ k ∈ K i, a * (g : H i) = r * a₀ * s i * k := by
        intro g hg
        by_contra hno
        apply hg
        have h0 : NIter ρ' μ' (fun _ => (0:ℂ)) l 1 (f₁ g) := by
          refine (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι (fun j => B j) (fun j => (R j).subgroupOf (B j)) ρ' μ' l 1).2 _ _ _ ?_ (hf₁' g)
          intro b hb
          by_contra hq
          rw [hQu] at hq
          obtain ⟨s, hs, hc⟩ := hsupp _ (fun j hj => by
            have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
            rw [Function.update_of_ne hji]
            have h1 : b j = 1 := hb j (fun hjl => hj (List.mem_cons_of_mem _ hjl))
            simp [h1, ha''1 j hj]) hq
          obtain ⟨r, hr, a₀, ha₀, k, hk, e⟩ := hc i (List.mem_cons_self ..)
          rw [Function.update_self] at e
          exact hno ⟨s, hs, r, hr, a₀, ha₀, k, hk, e⟩
        exact niter_unique ρ' μ' _ l huB 1 _ _ h0 (niter_zero ρ' μ' l 1)
      have hf₁W := hW f₁ (fun r hr g => f₁L r hr g) (fun k hk g => f₁K g k hk) (fun g hg => cell a ha g (f₁S g hg))
      have hz := IsQuotIntL1.unique hRB hf₁W hf₁0
      have hlin := (GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr ι (fun j => B j) (fun j => (R j).subgroupOf (B j)) ρ' μ' l 1).1 (B i) T' w f₁
        (fun t b => Qa (Function.update b i t)) (fun t _ => hf₁' t)
      rw [hz] at hlin
      have e : (fun b : ∀ j, B j => q' fun j => a' j * (b j).1) = fun b => ∑ t ∈ T', w t * Qa (Function.update b i t) := by
        funext b
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hQu]
        congr 2
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, a'']
      rw [e]
      exact hlin

end GlobalTheory.NestVan
