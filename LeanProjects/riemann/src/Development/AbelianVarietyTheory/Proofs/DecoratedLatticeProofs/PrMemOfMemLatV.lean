import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdPairTop

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_mem_latV (p : SplitPt D k) {S : HSp D} {L : Lat S}
    (hL : ∀ z ∈ L, z ∈ GlobalTheory.AdForm.intVec D S.rank) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L (· = p.v)) (i : Fin S.rank) : p.pr (y i) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [p.int_iff, p.sec_pr, map_mul]
    refine FrameLat.mul_mem_intAE (FrameLat.e_mem_intAt p).2 ?_
    simp only [one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | neg a _ ha => simpa using neg_mem ha

theorem rat_mulVec_sec (p : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => p.sec (w i)) = fun i => p.sec (((rat Q).map p.pr *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (rat Q i j), FrameLat.sec_mul_right, mul_comm (w j)]

theorem hasVal_of_single {n : Type} [Fintype n] [DecidableEq n] (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k])
    (hval : ∀ i, Q.HasVal (Pi.single i 1) (if i = l then c else 0)) (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]) :
    Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c) := by
  have key : ∀ T : Finset n, Q.HasVal (∑ i ∈ T, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k))
      (∑ i ∈ T, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using GlobalTheory.LatPair.Pair.mem_ker.1 (zero_mem Q.ker)
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ((hval a).smul _).add ih
  have h1 : (∑ i, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
  have h2 : (∑ i, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) = residue 𝒪[k] ⟨x l, hx l⟩ * c := by
    simp [mul_ite]
  have := key Finset.univ
  rwa [h1, h2] at this

theorem mem_ker_iff {n : Type} (q : GlobalTheory.LatPair.Unif k) (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k]) (hc : c ≠ 0)
    (hlat : ∀ x ∈ Q.lat, ∀ i, x i ∈ 𝒪[k])
    (hval : ∀ (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]), Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c)) (x : n → k) :
    x ∈ Q.ker ↔ (∀ i, x i ∈ 𝒪[k]) ∧ q.inv * x l ∈ 𝒪[k] := by
  have hq := q.ne_zero
  rw [GlobalTheory.LatPair.Pair.mem_ker]
  constructor
  · intro h
    have hx := hlat x h.mem
    refine ⟨hx, ?_⟩
    have h0 := (mul_eq_zero.1 ((hval x hx).unique h)).resolve_right hc
    obtain ⟨m, hm⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
    have hm' : x l = ((q.1 : 𝒪[k]) : k) * (m : k) := congrArg Subtype.val hm
    rw [hm', GlobalTheory.LatPair.Unif.inv, inv_mul_cancel_left₀ hq]
    exact m.2
  · rintro ⟨hx, h⟩
    have h0 : residue 𝒪[k] ⟨x l, hx l⟩ = 0 := (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨_, h⟩, Subtype.ext (by
      change x l = ((q.1 : 𝒪[k]) : k) * (q.inv * x l)
      rw [GlobalTheory.LatPair.Unif.inv, mul_inv_cancel_left₀ hq])⟩)
    have := hval x hx
    rwa [h0, zero_mul] at this

theorem row_eq_zero {S A L : HSp D} (o : OrthDec S A L) (hg : S.gram = 1) (ζ : Fin L.rank → D.host.E) (l : Fin S.rank)
    (a : D.host.E) (ha : a ≠ 0) (hv : ∀ r, vecB o ζ r = if r = l then a else 0) (j : Fin A.rank) : o.iA l j = 0 := by
  have h1 : star (vecB o ζ) ᵥ* o.iA = 0 := by
    have h := o.orth
    rw [hg, Matrix.mul_one] at h
    rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_zero]
  have h2 := congrFun h1 j
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, hv, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, star_zero, zero_mul]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl] at h2
  exact (mul_eq_zero.1 h2).resolve_left (star_ne_zero.2 ha)

theorem ker_stdPair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (π : 𝓞 D.host.E) (πc : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then ((π : 𝓞 D.host.E) : D.host.E) else 0) → valuation k (p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D πc)) = 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A), (∀ z, z ∈ LS ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → (∃ LZ : GlobalTheory.FinPl.Lat L, GlobalTheory.FinPl.OrthAt o LS LA LZ p.v) → ∀ (β : GlobalTheory.FinPl.Frame p S (Fin S.rank)) (Q : GlobalTheory.LatPair.Pair k (Fin S.rank)), β.b = 1 → β.IsLat LS Q.lat → (∀ z ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k], (s : k) = p.pr (incA D (πc * z r)) ∧ Q.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (z r'))) (residue 𝒪[k] s)) → ∃ (γ : GlobalTheory.FinPl.Frame p A (Fin A.rank)) (γ₀ : GlobalTheory.FinPl.Frame p S (Fin A.rank ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame o ζ γ γ₀ ∧ ∃ (Λ : Submodule 𝒪[k] (Fin A.rank → k)) (s : 𝓀[k]ˣ), γ.IsLat LA Λ ∧ (∀ y, y ∈ Q.ker ↔ (γ₀.b' * β.b) *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer Λ) ∧ Q.HasVal ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) s := by
  intro D k _ _ _ _ p q S A L o hg ζ hζ π πc hvec hπ hπc LS LA hLS hOrth β Q hb hlat hQ
  obtain ⟨LZ, hLZ⟩ := hOrth
  have hN : S.rank = A.rank + 1 := by rw [← o.rank_add, hζ.1]
  obtain ⟨l, hl⟩ : ∃ l : Fin S.rank, ∀ r : Fin S.rank, r.1 + 1 = S.rank ↔ r = l :=
    ⟨⟨A.rank, by omega⟩, fun r => by rw [Fin.ext_iff]; dsimp only; omega⟩
  simp only [hl] at hvec hQ
  have hb' : β.b' = 1 := by have := β.b'b; rwa [hb, Matrix.mul_one] at this
  have hsingle : ∀ i : Fin S.rank,
      (fun r' => p.pr (incA D ((Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) r'))) = Pi.single i 1 := by
    intro i
    funext r'
    by_cases h : r' = i
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, RingHom.map_one, RingHom.map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, RingHom.map_zero, RingHom.map_zero]
  have hsLS : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ LS := by
    intro i
    rw [hLS]
    intro j
    by_cases h : j = i
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  obtain ⟨s0, hs0, hv0⟩ := hQ _ (hsLS l) l rfl
  rw [hb', Matrix.one_mulVec, hsingle] at hv0
  rw [Pi.single_eq_same, mul_one] at hs0
  have hval : ∀ i : Fin S.rank, Q.HasVal (Pi.single i 1) (if i = l then residue 𝒪[k] s0 else 0) := by
    intro i
    split_ifs with h
    · subst h; exact hv0
    · obtain ⟨s, hs, hv⟩ := hQ _ (hsLS i) l rfl
      rw [hb', Matrix.one_mulVec, hsingle] at hv
      rw [Pi.single_eq_of_ne (Ne.symm h), mul_zero, RingHom.map_zero, RingHom.map_zero] at hs
      have h0 : s = 0 := Subtype.ext hs
      rwa [h0, RingHom.map_zero] at hv
  have hint := hasVal_of_single Q l _ hval
  have hres : ∀ s : 𝒪[k], valuation k (s : k) = 1 → residue 𝒪[k] s ≠ 0 := fun s hs =>
    (residue_ne_zero_iff_isUnit s).2 ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hs)
  have hc : residue 𝒪[k] s0 ≠ 0 := hres s0 (by rw [hs0, hπc])
  have hlatV : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ (fun i => p.sec (x i)) ∈ latV S LS (· = p.v) := by
    intro x; rw [hlat x, hb, Matrix.one_mulVec]
  have hlatI : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ ∀ i, x i ∈ 𝒪[k] := by
    intro x
    refine ⟨fun h i => ?_, fun h => (hint x h).mem⟩
    have := pr_mem_of_mem_latV p (fun z hz => (hLS z).1 hz) ((hlatV x).1 h) i
    rwa [p.pr_sec] at this
  have hker := mem_ker_iff q Q l _ hc (fun x hx => (hlatI x).1 hx) hint
  have hq := q.ne_zero
  obtain ⟨πw, hπw⟩ : ∃ πw, p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E)) = πw := ⟨_, rfl⟩
  have hqv : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hqv (by
    rw [← hπ, h, RingHom.map_zero, RingHom.map_zero, Valuation.map_zero])
  rw [hπw] at hπ
  have hu : valuation k (q.inv * πw) = 1 := by
    rw [Valuation.map_mul, GlobalTheory.LatPair.Unif.inv, map_inv₀, hπ, inv_mul_cancel₀ hqv]
  have huO : q.inv * πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu.le
  have hmulu : ∀ t : k, t * (q.inv * πw) ∈ 𝒪[k] ↔ t ∈ 𝒪[k] := fun t => by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]
  have hπO : πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by
    rw [hπ]; exact (Valuation.mem_integer_iff _ _).1 q.1.2)
  have hrow := row_eq_zero o hg ζ l _ hπ0 hvec
  obtain ⟨γ, hγ⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 A (Fin A.rank) 1 1 (Matrix.mul_one _) (Matrix.mul_one _)
  obtain ⟨γ₀, hsum⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame o hζ γ β
  have hact : ∀ (w : Fin A.rank ⊕ Fin 1 → k) (i : Fin S.rank), (γ₀.b *ᵥ w) i =
      (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i + if i = l then πw * w (Sum.inr 0) else 0 := by
    intro w i
    have h : γ₀.b = _ := hsum
    rw [h, hγ, Matrix.mul_one]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
      replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, ratV, hvec]
    congr 1
    split_ifs
    · rw [hπw]
    · rw [RingHom.map_zero, RingHom.map_zero, zero_mul]
  have hlast : ∀ a : Fin A.rank → k, (o.jA.map p.pr *ᵥ a) l = 0 := fun a => by
    change ∑ j, p.pr (incA D (o.iA l j)) * a j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hrow, RingHom.map_zero, RingHom.map_zero, zero_mul]
  refine ⟨γ, γ₀, hsum, Q.lat.comap ((Matrix.mulVecLin (o.jA.map p.pr)).restrictScalars 𝒪[k]),
    Units.mk0 _ (mul_ne_zero (hres ⟨_, huO⟩ hu) hc), fun a => ?_, fun y => ?_, ?_⟩
  · change o.jA.map p.pr *ᵥ a ∈ Q.lat ↔ _
    have h := rat_mulVec_sec p o.iA a
    change o.jA *ᵥ _ = fun i => p.sec ((o.jA.map p.pr *ᵥ a) i) at h
    rw [hlatV, ← h, hLZ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jA, o.pB_jA, Matrix.one_mulVec,
      Matrix.zero_mulVec, hγ, Matrix.one_mulVec]
    exact and_iff_left (zero_mem _)
  · rw [hb, Matrix.mul_one, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hker]
    obtain ⟨w, hw⟩ : ∃ w, γ₀.b' *ᵥ y = w := ⟨_, rfl⟩
    have hy : y = γ₀.b *ᵥ w := by rw [← hw, Matrix.mulVec_mulVec, γ₀.bb', Matrix.one_mulVec]
    rw [hw]
    change _ ↔ o.jA.map p.pr *ᵥ (w ∘ Sum.inl) ∈ Q.lat ∧ _
    have hyl : y l = πw * w (Sum.inr 0) := by rw [hy, hact, hlast, if_pos rfl, zero_add]
    have hyi : ∀ i, i ≠ l → y i = (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i := fun i hi => by
      rw [hy, hact, if_neg hi, add_zero]
    rw [hlatI, hyl, ← mul_assoc, mul_comm _ (w (Sum.inr 0)), hmulu]
    refine and_congr_left fun ht => forall_congr' fun i => ?_
    by_cases hi : i = l
    · rw [hi, hyl, hlast]
      exact iff_of_true (mul_mem hπO ht) (zero_mem _)
    · rw [hyi i hi]
  · have hx : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i =
        if i = l then q.inv * πw else 0 := fun i => by
      have h0 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) ∘ Sum.inl = 0 := by
        funext j; simp [GlobalTheory.LatPair.avec]
      have h1 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) (Sum.inr 0) = q.inv := by
        simp [GlobalTheory.LatPair.avec]
      rw [hb', Matrix.one_mul, hact, h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add, mul_comm]
    have hO : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i ∈ 𝒪[k] := fun i => by
      rw [hx]
      split_ifs
      · exact huO
      · exact zero_mem _
    have h := hint _ hO
    have e : (⟨_, hO l⟩ : 𝒪[k]) = ⟨_, huO⟩ := Subtype.ext ((hx l).trans (if_pos rfl))
    rw [e] at h
    exact h

end GlobalTheory.StdPairTop

end
