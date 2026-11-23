import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

private theorem levOp_self (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hfs : (Function.support fun q : G ⧸ K => f q.out).Finite) (x : V) :
    levOp ρ K K f LinearMap.id x = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out x := by
  have hs : (Function.support fun q : G ⧸ K => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hfs.subset fun q hq h0 => hq (by simp [h0])
  have h := (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) x).toAddMonoidHom.map_finsum hs
  simp only [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  exact h

private theorem levOp_ind (ρ : Representation ℂ G V) (K : Subgroup G) {x : V} (hx : x ∈ fixed ρ K) :
    levOp ρ K K ((K : Set G).indicator 1) LinearMap.id x = x := by
  let q₁ : G ⧸ K := QuotientGroup.mk 1
  have hz : ∀ q : G ⧸ K, q ≠ q₁ → ((K : Set G).indicator 1 q.out : ℂ) = 0 := fun q hq => by
    refine Set.indicator_of_notMem (fun hm => hq ?_) _
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem hm)
  have h1 : Quotient.out q₁ ∈ K := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₁).symm
    simpa [q₁] using this
  rw [levOp_self ρ K _ ((Set.finite_singleton q₁).subset fun q hq => by
    by_contra hne
    exact hq (hz q hne)), finsum_eq_single _ q₁ fun q hq => by rw [hz q hq, zero_smul]]
  rw [Set.indicator_of_mem h1]
  simpa using GlobalTheory.LGrp.mem_fixed.1 hx _ h1

private theorem twTr_line (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (c : ℂ)
    (h1 : Module.finrank ℂ (fixed ρ K) = 1) {x : V} (hx : x ∈ fixed ρ K) (h0 : x ≠ 0)
    (hop : levOp ρ K K f LinearMap.id x = c • x) : twTr ρ K K f LinearMap.id = c := by
  have hx0 : (⟨x, hx⟩ : fixed ρ K) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hall : ∀ y ∈ fixed ρ K, levOp ρ K K f LinearMap.id y = c • y := fun y hy => by
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx0).1 h1 ⟨y, hy⟩
    have hy' : y = a • x := (congrArg Subtype.val ha).symm
    rw [hy', map_smul, hop, smul_comm]
  have hmem : ∀ v ∈ fixed ρ K, levOp ρ K K f LinearMap.id v ∈ fixed ρ K := fun v hv => by
    rw [hall v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K f LinearMap.id).restrict hmem = c • LinearMap.id := by
    ext y
    simp [LinearMap.restrict_apply, hall y.1 y.2]
  haveI : Module.Finite ℂ (fixed ρ K) := Module.finite_of_finrank_pos (by omega)
  rw [twTr, dif_pos hmem, hr, map_smul, LinearMap.trace_id, h1]
  simp

private theorem twTr_ind (ρ : Representation ℂ G V) (K : Subgroup G) (h1 : Module.finrank ℂ (fixed ρ K) = 1)
    (hne : fixed ρ K ≠ ⊥) : twTr ρ K K ((K : Set G).indicator 1) LinearMap.id = 1 := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  exact twTr_line ρ K _ 1 h1 hx h0 (by rw [levOp_ind ρ K hx, one_smul])

private theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) :
    (Function.support fun q : G ⧸ K => f q.out).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have himg : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) :=
    IsCompact.image hc continuous_quot_mk
  refine himg.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

private theorem levOp_comp (e : G ≃* H) (ρ : Representation ℂ H V) (K : Subgroup H) (K₁ : Subgroup G)
    (hK : ∀ g, g ∈ K₁ ↔ e g ∈ K) (F : G → ℂ) (f : H → ℂ) (hFf : ∀ g, F g = f (e g))
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) (hfin : (Function.support fun q : H ⧸ K => f q.out).Finite)
    {x : V} (hx : x ∈ fixed ρ K) :
    levOp (ρ.comp e.toMonoidHom) K₁ K₁ F LinearMap.id x = levOp ρ K K f LinearMap.id x := by
  let φ : G ⧸ K₁ → H ⧸ K := fun q => QuotientGroup.mk (e q.out)
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.2 ((hK _).2 ?_)
      have := QuotientGroup.eq.1 hab
      simpa using this
    · intro q
      refine ⟨QuotientGroup.mk (e.symm q.out), ?_⟩
      rw [← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 ?_
      have h1 : (e.symm q.out)⁻¹ * (Quotient.out (QuotientGroup.mk (e.symm q.out) : G ⧸ K₁)) ∈ K₁ :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      have h2 := (hK _).1 (K₁.inv_mem h1)
      simpa [φ] using h2
  have hrep : ∀ q : G ⧸ K₁, ∃ k ∈ K, (φ q).out = e q.out * k := fun q => by
    refine ⟨(e q.out)⁻¹ * (φ q).out, QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm, by group⟩
  have hval : ∀ q : G ⧸ K₁, F q.out = f (φ q).out := fun q => by
    obtain ⟨k, hk, h⟩ := hrep q
    rw [h, hf _ k hk, hFf]
  have hfin' : (Function.support fun q : G ⧸ K₁ => F q.out).Finite := by
    refine (hfin.preimage hφ.1.injOn).subset fun q hq => ?_
    simpa [hval q] using hq
  rw [levOp_self _ K₁ F hfin', levOp_self ρ K f hfin, ← finsum_comp_equiv (Equiv.ofBijective φ hφ)]
  refine finsum_congr fun q => ?_
  obtain ⟨k, hk, h⟩ := hrep q
  simp only [Equiv.ofBijective_apply]
  rw [hval q, h]
  congr 1
  have hk' := GlobalTheory.LGrp.mem_fixed.1 hx k hk
  rw [map_mul, Module.End.mul_apply, hk']
  rfl

private theorem fixed_comp (e : G ≃* H) (ρ : Representation ℂ H V) (K : Subgroup H) (K₁ : Subgroup G)
    (hK : ∀ g, g ∈ K₁ ↔ e g ∈ K) : fixed (ρ.comp e.toMonoidHom) K₁ = fixed ρ K := by
  refine Submodule.ext fun x => ⟨fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
  · have h1 := GlobalTheory.LGrp.mem_fixed.1 h (e.symm k) ((hK _).2 (by simpa using hk))
    simpa using h1
  · exact GlobalTheory.LGrp.mem_fixed.1 h (e k) ((hK k).1 hk)

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hs : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hs]
  exact Subgroup.mem_top _

private def eSp (hs : IsSplitAt w) : GLw n w ≃* UL n w where
  toFun g := ⟨g, mem_UL hs g⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) : SmIrr (GLw n w) :=
  { V := σ.V
    ρ := σ.ρ.comp (eSp hs).toMonoidHom
    smooth := fun v => (σ.smooth v).preimage (Continuous.subtype_mk continuous_id _)
    irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ _ (eSp hs).surjective σ.irred }

private theorem fixed_toGL (hs : IsSplitAt w) (σ : SmIrr (UL n w)) :
    fixed (toGL hs σ).ρ (KGL w n) = fixed σ.ρ (KL n w) :=
  fixed_comp (eSp hs) σ.ρ (KL n w) (KGL w n) fun _ => Iff.rfl

private theorem comp_toGL (hs : IsSplitAt w) {π : Submodule ℂ (UA E n → ℂ)} {σ : SmIrr (UL n w)}
    (h : IsCompU π w σ) :
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (toGL hs σ).ρ := by
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := h
  refine ⟨(toGL hs σ).irred, f, hf0, hfm, fun x v => ?_⟩
  have he : eSp hs (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
  exact (congrArg (fun g => f (σ.ρ g v)) he).trans (hf x v)

private theorem isHecke_val (hU : GlobalTheory.BCT.Unr E) (K₀ : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (h : IsHecke K₀ f) (K₁ : Subgroup (UL n w)) (hK : ∀ k ∈ K₁, k.1 ∈ K₀) :
    IsHecke K₁ fun y : UL n w => f y.1 :=
  ⟨h.1.comp_isClosedEmbedding (GlobalTheory.BCT.LocCompU.isClosed_UL hU n w).isClosedEmbedding_subtypeVal,
    fun k hk x => ⟨(h.2 k.1 (hK k hk) x.1).1, (h.2 k.1 (hK k hk) x.1).2⟩⟩

private theorem isHecke_ind (hU : GlobalTheory.BCT.Unr E) : IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1) := by
  refine ⟨HasCompactSupport.intro (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 fun x hx =>
    Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · by_cases hx : x ∈ KL n w
    · rw [Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_mem (show k * x ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hk hx)]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_notMem (show k * x ∉ (KL n w : Set (UL n w)) from
          fun h => hx (((KL n w).mul_mem_cancel_left hk).1 h))]
  · by_cases hx : x ∈ KL n w
    · rw [Set.indicator_of_mem (show x ∈ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_mem (show x * k ∈ (KL n w : Set (UL n w)) from (KL n w).mul_mem hx hk)]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ (KL n w : Set (UL n w)) from hx),
        Set.indicator_of_notMem (show x * k ∉ (KL n w : Set (UL n w)) from
          fun h => hx (((KL n w).mul_mem_cancel_right hk).1 h))]

private theorem trace_test_function_eq (hE : ExAct) (hU : GlobalTheory.BCT.Unr E) (hs : IsSplitAt w) (σ : SmIrr (UL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {B : Multiset ℂˣ} (hB : HasSatGL w (toGL hs σ).ρ B)
    (e : Ex (Fin (n + 1))) :
    twTr σ.ρ (KL n w) (KL n w) (fun y : UL n w => fn1 n w e y.1) LinearMap.id = ev1 n w e B := by
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨hH, hA⟩ := hE E n w e
  have hfix : x ∈ fixed σ.ρ (KL n w) := (fixed_toGL hs σ) ▸ hx.2.1
  have hHU := isHecke_val hU _ _ hH (KL n w) fun k hk => hk
  have hop := hA _ (toGL hs σ).ρ x B hx
  refine twTr_line σ.ρ (KL n w) _ _ h1 hfix hx.1 ?_
  rw [← levOp_comp (eSp hs) σ.ρ (KL n w) (KGL w n) (fun g => Iff.rfl) (fn1 n w e)
    (fun y : UL n w => fn1 n w e y.1) (fun _ => rfl) (fun y k hk => (hHU.2 k hk y).2)
    (finite_supp _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1 _ hHU.1) hfix]
  exact hop

end Local

theorem rUEval : RUEval := by
  intro hUS hPl hEx hSL hIL hUC E _ _ _ hU n hn S hS lam Z hZ f hf hreg
  obtain ⟨-, hcc, -, hsec⟩ := hPl E
  have hsplit' : ∀ w : Pl E, IsSplitAt w → IsSplitAt (cPl w) := fun w h =>
    (hcc (cPl w)).2.2 (by rw [(hcc w).1]; exact ((hcc w).2.1 h).symm)
  have hnot : ∀ w ∈ S, IsSplitAt w → cPl w ∉ S := fun w hw h hc =>
    (hcc w).2.1 h ((hsec S hS w).2 hw hc)

  obtain ⟨Kz, hKo, hKle, hKf, hKn⟩ : ∃ Kz : ∀ w : Pl E, Subgroup (GLw n w), (∀ w, IsOpen (Kz w : Set (GLw n w))) ∧
      (∀ w, Kz w ≤ KGL w n) ∧ (∀ w ∈ Z, IsHecke (Kz w) (f w)) ∧ ∀ w, w ∉ Z → Kz w = KGL w n := by
    refine ⟨fun w => if h : w ∈ Z then (hf w h).choose else KGL w n, fun w => ?_, fun w => ?_, fun w h => ?_, fun w h => ?_⟩
    · by_cases h : w ∈ Z
      · simpa [h] using (hf w h).choose_spec.1
      · simpa [h] using (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
    · by_cases h : w ∈ Z
      · simpa [h] using (hf w h).choose_spec.2.1
      · simp [h]
    · simpa [h] using (hf w h).choose_spec.2.2
    · simp [h]
  let K' : ∀ w : Pl E, Subgroup (UL n w) := fun w => (Kz w).subgroupOf (UL n w)
  have hKL : ∀ w, w ∉ Z → K' w = KL n w := fun w h => by
    simp only [K', hKn w h, KL]
  have hLev : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' := by
    refine ⟨fun w => ⟨?_, fun k hk => hKle w hk, fun k hk => hk⟩, ?_⟩
    · simp only [K', Subgroup.coe_subgroupOf]
      exact (hKo w).preimage continuous_subtype_val
    · refine Filter.eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
      by_contra h
      exact hw (hKL w h)
  obtain ⟨ι, hι, π, σ, hσ, -, hTr⟩ := hUS E hU n hn S hS lam K' hLev

  have hline : ∀ i, ∀ w ∈ S, w ∉ Z → fixed (σ i w).ρ (KL n w) ≠ ⊥ ∧ Module.finrank ℂ (fixed (σ i w).ρ (KL n w)) = 1 ∧
      ∃ B, ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B := fun i w hw hz => by
    obtain ⟨hc, hne, hfd⟩ := (hσ i).2.2.2 w hw
    rw [hKL w hz] at hne
    by_cases hs : IsSplitAt w
    · obtain ⟨h1, B, hB⟩ := hSL E n w (toGL hs (σ i w)) (by rw [fixed_toGL]; exact hne)
      refine ⟨hne, ?_, B, fun _ => hB⟩
      rw [fixed_toGL] at h1
      exact h1
    · exact ⟨hne, hIL E hU n w hs (σ i w) hne (hfd _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1),
        0, fun h => absurd h hs⟩
  let B₀ : ι → Pl E → Multiset ℂˣ := fun i w => Classical.epsilon fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B
  have hB₀ : ∀ i, ∀ w ∈ S, w ∉ Z → ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ (B₀ i w) := fun i w hw hz =>
    Classical.epsilon_spec (p := fun B => ∀ hs : IsSplitAt w, HasSatGL w (toGL hs (σ i w)).ρ B) (hline i w hw hz).2.2
  let B : ι → Pl E → Multiset ℂˣ := fun i w => if w ∈ S then B₀ i w else inv (B₀ i (cPl w))
  have hBS : ∀ i, ∀ w ∈ S, B i w = B₀ i w := fun i w hw => if_pos hw
  have hBN : ∀ i w, w ∉ S → B i w = inv (B₀ i (cPl w)) := fun i w hw => if_neg hw
  let A : ι → ℂ := fun i => ∏ w ∈ Z, twTr (σ i w).ρ (KL n w) (K' w) (fun x => f w x.1) LinearMap.id
  refine ⟨K', ι, hι, π, A, B, hLev, fun i => ⟨(hσ i).1, fun w hns => ?_, fun w hoff hs => ?_⟩, fun T hT hd e₁ e₂ k => ?_⟩
  ·
    have hw : w ∈ S := by
      have hcw : cPl w = w := by
        by_contra h
        exact hns ((hcc w).2.2 h)
      rcases (hsec S hS w).1 with h | h
      · exact h
      · rwa [hcw] at h
    have hz : w ∉ Z := fun h => hns (hZ w h).2
    obtain ⟨φ, hφ, h0, hfix⟩ := (hσ i).2.2.1
    obtain ⟨p, hp, -⟩ := ((hσ i).2.2.2 w hw).1
    refine ⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ⟨p ⟨x, hx⟩, ?_, hp ⟨x, hx⟩⟩⟩
    rw [hKL w hz]
    change (p ⟨x, hx⟩).1 ∈ KGL w n
    rw [hp ⟨x, hx⟩]
    exact hk
  ·
    by_cases hw : w ∈ S
    · rw [hBS i w hw]
      exact ⟨toGL hs (σ i w), comp_toGL hs ((hσ i).2.2.2 w hw).1, hB₀ i w hw hoff.1 hs⟩
    · have hcw : cPl w ∈ S := ((hsec S hS w).1).resolve_left hw
      have hsc := hsplit' w hs
      have hu := hUC E n (π i) (cPl w) hsc (toGL hsc (σ i (cPl w))) (B₀ i (cPl w))
        (comp_toGL hsc ((hσ i).2.2.2 _ hcw).1) (hB₀ i _ hcw hoff.2 hsc)
      rw [(hcc w).1] at hu
      rw [hBN i w hw]
      exact hu
  ·
    have hTs : ∀ w ∈ T, w ∈ S ∧ IsSplitAt w ∧ w ∉ Z := fun w hw =>
      ⟨(hT w hw).1, (hT w hw).2, Finset.disjoint_left.1 hd hw⟩
    have hfZ : ∀ w ∈ Z, famU Z T f e₁ e₂ k w = fun x => f w x.1 := fun w hw => by
      simp [famU, hw]
    have hfT : ∀ w ∈ T, famU Z T f e₁ e₂ k w = fun x => fn1 n w (((e₁ w).pow k).mul ((e₂ w).pow k)) x.1 := fun w hw => by
      simp [famU, hw, (hTs w hw).2.2]
    have hfO : ∀ w, w ∉ Z → w ∉ T → famU Z T f e₁ e₂ k w = (KL n w : Set _).indicator 1 := fun w h1 h2 => by
      simp [famU, h1, h2]
    have htest : GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h1 : w ∈ Z
        · rw [hfZ w h1]
          exact isHecke_val hU _ _ (hKf w h1) (K' w) fun k hk => hk
        · by_cases h2 : w ∈ T
          · rw [hfT w h2]
            exact isHecke_val hU _ _ (hEx E n w _).1 (K' w) fun k hk => hKle w hk
          · rw [hfO w h1 h2, hKL w h1]
            exact isHecke_ind hU
      · refine Filter.eventually_cofinite.2 ((Z ∪ T).finite_toSet.subset fun w hw => ?_)
        by_contra h
        have h' : w ∉ Z ∧ w ∉ T := by simpa using h
        exact hw (hfO w h'.1 h'.2)
    refine ⟨htest, ?_⟩
    have hr : ∃ w ∈ S, ∀ y, famU Z T f e₁ e₂ k w y ≠ 0 → y.1.val.charpoly.Separable := by
      obtain ⟨w, hw, hy⟩ := hreg
      refine ⟨w, (hZ w hw).1, fun y h => hy y.1 ?_⟩
      rwa [hfZ w hw] at h
    rw [← hTr _ htest hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    set g : Pl E → ℂ := fun w => twTr (σ i w).ρ (KL n w) (K' w) (famU Z T f e₁ e₂ k w) LinearMap.id with hg
    have hone : ∀ w ∈ S, w ∉ Z → w ∉ T → g w = 1 := fun w hw h1 h2 => by
      obtain ⟨hne, hfr, -⟩ := hline i w hw h1
      simp only [hg]
      rw [hfO w h1 h2, hKL w h1]
      exact twTr_ind _ _ hfr hne
    have hUS' : ∀ w ∈ Z ∪ T, w ∈ S := fun w hw => by
      rcases Finset.mem_union.1 hw with h | h
      · exact (hZ w h).1
      · exact (hTs w h).1
    have hsupp : ∏ᶠ w ∈ S, g w = ∏ w ∈ Z ∪ T, g w := by
      rw [← finprod_mem_coe_finset]
      refine finprod_mem_inter_mulSupport_eq' _ _ _ fun w hw => ⟨fun h => ?_, fun h => hUS' w h⟩
      by_contra hn
      have h' : w ∉ Z ∧ w ∉ T := by simpa using hn
      exact hw (hone w h h'.1 h'.2)
    rw [hsupp, Finset.prod_union hd.symm]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w hw => ?_) ?_
    · simp only [hg]
      rw [hfZ w hw]
    · rw [val1, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨hwS, hs, hz⟩ := hTs w hw
      have hinv : inv (inv (B₀ i w)) = B₀ i w := by simp [inv, Multiset.map_map]
      simp only [hg]
      rw [hfT w hw, hKL w hz, trace_test_function_eq hEx hU hs (σ i w) (hline i w hwS hz).2.1 (hB₀ i w hwS hz hs), hBS i w hwS,
        hBN i _ (hnot w hwS hs), (hcc w).1, hinv]
      simp only [ev1, Ex.ev, Ex.ev_pow, mul_pow]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
