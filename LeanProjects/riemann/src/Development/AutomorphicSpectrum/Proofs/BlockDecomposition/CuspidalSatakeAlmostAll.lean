import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCT
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestTail

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

namespace GlobalTheory.CompanionTheory.SatAe

theorem scalar_of_simple {F : Type} [AddCommGroup F] [Module ℂ F] (hr : Module.rank ℂ F ≤ Cardinal.aleph0)
    (A : Set (Module.End ℂ F))
    (hs : ∀ W : Submodule ℂ F, (∀ f ∈ A, ∀ x ∈ W, f x ∈ W) → W = ⊥ ∨ W = ⊤)
    (T : Module.End ℂ F) (hT : ∀ f ∈ A, f * T = T * f) : ∃ c : ℂ, ∀ x, T x = c • x := by
  by_cases hF : Nontrivial F
  swap
  · rw [not_nontrivial_iff_subsingleton] at hF
    exact ⟨0, fun x => Subsingleton.elim _ _⟩
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hr T
  set S : Module.End ℂ F := T - algebraMap ℂ _ c with hS
  have hSc : ∀ f ∈ A, f * S = S * f := fun f hf => by
    rw [hS, mul_sub, sub_mul, hT f hf, Algebra.commutes]
  have h1 := hs (LinearMap.ker S) fun f hf x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have := LinearMap.congr_fun (hSc f hf) x
    simp only [Module.End.mul_apply, hx, map_zero] at this
    exact this.symm
  have h2 := hs (LinearMap.range S) fun f hf x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨f y, (LinearMap.congr_fun (hSc f hf) y).symm⟩
  refine ⟨c, fun x => ?_⟩
  rcases h1 with h1 | h1
  · exfalso
    apply hc
    rw [Module.End.isUnit_iff]
    refine ⟨LinearMap.ker_eq_bot.1 h1, ?_⟩
    rcases h2 with h2 | h2
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : F)
      have h3 : S v ∈ LinearMap.range S := ⟨v, rfl⟩
      rw [h2] at h3
      have h4 : v ∈ LinearMap.ker S := (Submodule.mem_bot ℂ).1 h3
      rw [h1] at h4
      exact hv ((Submodule.mem_bot ℂ).1 h4)
    · exact LinearMap.range_eq_top.1 h2
  · have h3 : x ∈ LinearMap.ker S := h1 ▸ Submodule.mem_top
    have e : S x = 0 := h3
    have e2 : T x - c • x = 0 := by simpa [hS, Module.algebraMap_end_apply] using e
    exact sub_eq_zero.1 e2

theorem rank_le_of_simple {M ι : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (O : ι → Module.End ℂ M)
    (hne : S ≠ ⊥) (hirr : ∀ W ≤ S, (∀ i, ∀ x ∈ W, O i x ∈ W) → W = ⊥ ∨ W = S)
    (hc : ∀ x ∈ S, ∃ C : Set M, C.Countable ∧ C ⊆ S ∧ ∀ i, O i x ∈ Submodule.span ℂ C) :
    Module.rank ℂ S ≤ Cardinal.aleph0 := by
  classical
  obtain ⟨x0, hx0, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hc' : ∀ x : M, ∃ C : Set M, C.Countable ∧ C ⊆ S ∧ (x ∈ S → ∀ i, O i x ∈ Submodule.span ℂ C) := fun x => by
    by_cases hx : x ∈ S
    · obtain ⟨C, h1, h2, h3⟩ := hc x hx
      exact ⟨C, h1, h2, fun _ => h3⟩
    · exact ⟨∅, Set.countable_empty, Set.empty_subset _, fun h => absurd h hx⟩
  choose c c1 c2 c3 using hc'
  let T : ℕ → Set M := fun n => Nat.rec {x0} (fun _ s => s ∪ ⋃ x ∈ s, c x) n
  have Ts : ∀ n, T (n + 1) = T n ∪ ⋃ x ∈ T n, c x := fun _ => rfl
  have hTc : ∀ n, (T n).Countable := fun n => by
    induction n with
    | zero => exact Set.countable_singleton _
    | succ n ih => rw [Ts]; exact ih.union (ih.biUnion fun x _ => c1 x)
  have hTS : ∀ n, T n ⊆ S := fun n => by
    induction n with
    | zero => exact Set.singleton_subset_iff.2 hx0
    | succ n ih =>
      rw [Ts]
      exact Set.union_subset ih (Set.iUnion₂_subset fun x _ => c2 x)
  have hUc : (⋃ n, T n).Countable := Set.countable_iUnion hTc
  have hW : Submodule.span ℂ (⋃ n, T n) ≤ S := Submodule.span_le.2 (Set.iUnion_subset hTS)
  have hst : ∀ i, ∀ x ∈ Submodule.span ℂ (⋃ n, T n), O i x ∈ Submodule.span ℂ (⋃ n, T n) := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      exact Submodule.span_mono (fun y hy => Set.mem_iUnion.2 ⟨n + 1, by
        rw [Ts]; exact Or.inr (Set.mem_biUnion hn hy)⟩) (c3 x (hTS n hn) i)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha
  have hx0U : x0 ∈ Submodule.span ℂ (⋃ n, T n) :=
    Submodule.subset_span (Set.mem_iUnion.2 ⟨0, rfl⟩)
  have e : Submodule.span ℂ (⋃ n, T n) = S := (hirr _ hW hst).resolve_left fun h => h0 (by
    rw [h] at hx0U
    exact (Submodule.mem_bot ℂ).1 hx0U)
  rw [← e]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 hUc)

theorem countable_orbit {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (x : M) (h : IsOpen {g | ρ g x = x}) :
    (Set.range fun g => ρ g x).Countable :=
  _root_.UpperTheory.Reformulated.B.Yhd2.main ρ x h

section Cusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
theorem secondCountable_GL : SecondCountableTopology (GL (Fin a) (Af E)) := by
  haveI := Formalism.L2.Fam.ThC.sc_Af E
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Af E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Af E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem rank_cuspSub (π : CuspSub E a) : Module.rank ℂ π.V ≤ Cardinal.aleph0 := by
  haveI := secondCountable_GL (E := E) (a := a)
  refine rank_le_of_simple π.V (act (E := E) (a := a)) π.ne_bot (fun W hW hs => π.irred W hW hs) fun x hx => ?_
  have hcusp := (π.cusp x hx).1
  have hk := hcusp.kfin
  obtain ⟨s, hs1, hs2⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1
    (Module.Finite.iff_fg.1 hk)
  let b := Module.finBasis ℝ (Lie E a)
  refine ⟨(Set.range fun g => finRep E a g x) ∪ ((s : Set (Sm E a)) ∪ Set.range fun i => lie E a (b i) x),
    (countable_orbit _ _ hcusp.level).union (s.countable_toSet.union (Set.countable_range _)), ?_, fun o => ?_⟩
  · rintro y (⟨g, rfl⟩ | hy | ⟨i, rfl⟩)
    · exact π.stable (.fin g) x hx
    · obtain ⟨k, rfl⟩ := hs1 hy
      exact π.stable (.cpt k) x hx
    · exact π.stable (.lie (b i)) x hx
  · cases o with
    | fin k => exact Submodule.subset_span (Or.inl ⟨k, rfl⟩)
    | cpt k =>
      have h1 : cptRep E a k x ∈ Submodule.span ℂ (s : Set (Sm E a)) := hs2 ▸ Submodule.subset_span ⟨k, rfl⟩
      exact Submodule.span_mono (fun y hy => Or.inr (Or.inl hy)) h1
    | lie X =>
      change lie E a X x ∈ _
      have e : lie E a X = ∑ i, b.repr X i • lie E a (b i) := by
        conv_lhs => rw [← b.sum_repr X, map_sum]
        simp only [map_smul]
      rw [e, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.smul_apply, ← algebraMap_smul ℂ (b.repr X i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr (Or.inr ⟨i, rfl⟩)))

end Cusp

section Hecke

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

theorem heckeVec_dosetInd_eq_idem (hs : IsSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (g : G) {z : V} (hz : z ∈ fixed π K) :
    ∃ N : ℂ, N ≠ 0 ∧ heckeVec π K (dosetInd ℂ K g) z = N • idem hs hc (π g z) := by
  classical
  have hm := Final.DosetIndMem G K ℂ g
  have hfin := Formalism.UG.P.finite_support_cosets hK hm.2
  have hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c => by
    simp [dosetInd]
  refine ⟨hfin.toFinset.card, ?_, ?_⟩
  · refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩
  · rw [← idem_of_mem hs hc (heckeVec_mem_fixed hK hm hz), heckeVec,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun c hcS => ?_
      have h1 := (hS c).1 hcS
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h1
      rw [dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hz b hb]
      simpa using idem_apply_mem hs hc ha (π g z)
    · intro c hc'
      refine Finset.mem_coe.2 ((hS c).2 ?_)
      by_contra h0
      exact hc' (by simp [dosetInd, h0])

def IsBiSimple (π : Representation ℂ G V) : Prop :=
  ∀ S : Submodule ℂ V, (∀ g, ∀ x ∈ S, π g x ∈ S) →
    (∀ b : Module.End ℂ V, (∀ g, b * π g = π g * b) → ∀ x ∈ S, b x ∈ S) → S = ⊥ ∨ S = ⊤

theorem fixed_simple (hs : IsSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K) (hirr : IsBiSimple π)
    (W : Submodule ℂ V) (hW : W ≤ fixed π K)
    (hH : ∀ f ∈ Hecke ℂ K, ∀ x ∈ W, heckeVec π K f x ∈ W)
    (hB : ∀ b : Module.End ℂ V, (∀ g, b * π g = π g * b) → ∀ x ∈ W, b x ∈ W) : W = ⊥ ∨ W = fixed π K := by
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hW fun x hx => ?_)
  obtain ⟨w0, hw0, hw00⟩ := (Submodule.ne_bot_iff _).1 h0
  let C : Set V := {y | ∃ g, ∃ b : Module.End ℂ V, (∀ g, b * π g = π g * b) ∧ y = π g (b w0)}
  have h1 : ∀ g, ∀ y ∈ Submodule.span ℂ C, π g y ∈ Submodule.span ℂ C := fun g y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g', b, hb, rfl⟩ := hy
      exact Submodule.subset_span ⟨g * g', b, hb, by rw [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu
  have h2 : ∀ b : Module.End ℂ V, (∀ g, b * π g = π g * b) → ∀ y ∈ Submodule.span ℂ C, b y ∈ Submodule.span ℂ C :=
    fun b hb y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g', b', hb', rfl⟩ := hy
      refine Submodule.subset_span ⟨g', b * b', fun g => by rw [mul_assoc, hb' g, ← mul_assoc, hb g, mul_assoc], ?_⟩
      have := LinearMap.congr_fun (hb g') (b' w0)
      simpa [Module.End.mul_apply] using this
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu
  have hw0C : w0 ∈ Submodule.span ℂ C :=
    Submodule.subset_span ⟨1, 1, fun g => by rw [one_mul, mul_one], by simp⟩
  have htop : Submodule.span ℂ C = ⊤ := (hirr _ h1 h2).resolve_left fun h => hw00 (by
    rw [h] at hw0C
    exact (Submodule.mem_bot ℂ).1 hw0C)
  have key : ∀ y ∈ Submodule.span ℂ C, idem hs hc y ∈ W := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, b, hb, rfl⟩ := hy
      have hbw := hB b hb w0 hw0
      obtain ⟨N, hN, e⟩ := heckeVec_dosetInd_eq_idem hs hc hK g (hW hbw)
      have e2 : idem hs hc (π g (b w0)) = N⁻¹ • heckeVec π K (dosetInd ℂ K g) (b w0) := by
        rw [e, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [e2]
      exact W.smul_mem _ (hH _ (Final.DosetIndMem G K ℂ g) _ hbw)
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu
  have := key x (htop ▸ Submodule.mem_top)
  rwa [idem_of_mem hs hc hx] at this

theorem exists_scalar (hs : IsSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) (hirr : IsBiSimple π)
    (hr : Module.rank ℂ V ≤ Cardinal.aleph0) (h : G → ℂ) (hh : h ∈ Hecke ℂ K) :
    ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  have hbF : ∀ b : Module.End ℂ V, (∀ g, b * π g = π g * b) → ∀ x ∈ fixed π K, b x ∈ fixed π K := fun b hb x hx =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      have := LinearMap.congr_fun (hb k) x
      simp only [Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx k hk] at this
      exact this.symm
  let R : ∀ f, f ∈ Hecke ℂ K → Module.End ℂ (fixed π K) := fun f hf =>
    (heckeLin hK hf π).restrict fun x hx => heckeVec_mem_fixed hK hf hx
  let Rb : ∀ b : Module.End ℂ V, (∀ g, b * π g = π g * b) → Module.End ℂ (fixed π K) := fun b hb =>
    b.restrict (hbF b hb)
  let A : Set (Module.End ℂ (fixed π K)) :=
    {f | ∃ f' hf, f = R f' hf} ∪ {f | ∃ b hb, f = Rb b hb}
  have hrF : Module.rank ℂ (fixed π K) ≤ Cardinal.aleph0 := (Submodule.rank_le _).trans hr
  have hsim : ∀ W : Submodule ℂ (fixed π K), (∀ f ∈ A, ∀ x ∈ W, f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hWs
    have hWf : W.map (fixed π K).subtype ≤ fixed π K := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have := fixed_simple hs hc hK hirr (W.map (fixed π K).subtype) hWf (by
      rintro f hf _ ⟨x, hx, rfl⟩
      exact ⟨_, hWs _ (Or.inl ⟨f, hf, rfl⟩) x hx, rfl⟩) (by
      rintro b hb _ ⟨x, hx, rfl⟩
      exact ⟨_, hWs _ (Or.inr ⟨b, hb, rfl⟩) x hx, rfl⟩)
    refine this.imp (fun e => ?_) fun e => ?_
    · exact Submodule.map_injective_of_injective (Submodule.subtype_injective _) (by rw [e, Submodule.map_bot])
    · refine Submodule.map_injective_of_injective (Submodule.subtype_injective (fixed π K)) ?_
      rw [e, Submodule.map_top, Submodule.range_subtype]
  have hcm : ∀ f ∈ A, f * R h hh = R h hh * f := by
    rintro f (⟨f', hf, rfl⟩ | ⟨b, hb, rfl⟩)
    · refine LinearMap.ext fun x => Subtype.ext ?_
      change heckeVec π K f' (heckeVec π K h x.1) = heckeVec π K h (heckeVec π K f' x.1)
      rw [← heckeVec_conv hK hf hh x.2, ← heckeVec_conv hK hh hf x.2, hcomm _ hf _ hh]
    · refine LinearMap.ext fun x => Subtype.ext ?_
      exact map_heckeVec hK hh b (fun g y => LinearMap.congr_fun (hb g) y) x.1
  obtain ⟨c, hc'⟩ := scalar_of_simple hrF A hsim (R h hh) hcm
  exact ⟨c, fun x hx => congrArg Subtype.val (hc' ⟨x, hx⟩)⟩

end Hecke

section Main

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_hasSatGL_of_scalar {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    (hsc : ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed π (KGL w n), heckeVec π (KGL w n) h x = c • x)
    (hs : GlobalTheory.LGrp.IsSpherical π (KGL w n)) : ∃ B, HasSatGL w π B := by
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  choose c hc using fun j => hsc _ (Tj_mem_hecke (n := n) hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w n) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0 x hx, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n x hx
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hs, fun y hy hy0 => ⟨hy0, hy, hB, fun ϖ' hu' j hj => ?_⟩⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j y hy, hBc j hj]

variable [IsTotallyComplex E] {a : ℕ}

theorem isBiSimple_locRep (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : IsBiSimple (π.locRep w) := by
  intro S h1 h2
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ x ∈ S, π.op o x ∈ S := fun o ho =>
    h2 (π.op o) fun g => LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (ho g) φ.1)
  have hop : ∀ o : Op E a, ∀ x ∈ S, π.op o x ∈ S := by
    intro o x hx
    cases o with
    | fin k =>
      let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
      have h3 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
        change finRep E a _ * _ = _ * finRep E a _
        rw [← map_mul, ← map_mul, LocSph.comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])])
        _ (h1 g x hx)
      have h4 : π.op (.fin (k * (locGL E a w g)⁻¹)) (π.locRep w g x) = π.op (.fin k) x := by
        refine Subtype.ext ?_
        change finRep E a _ (finRep E a _ x.1) = finRep E a k x.1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rwa [h4] at h3
    | cpt k =>
      refine comm (.cpt k) (fun g => ?_) x hx
      have h3 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
      rw [map_mul, map_mul] at h3
      exact h3
    | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) x hx
  have hle : S.map π.V.subtype ≤ π.V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine (π.irred _ hle ?_).imp (fun e => ?_) fun e => ?_
  · rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩
  · exact Submodule.map_injective_of_injective (Submodule.subtype_injective _) (by rw [e, Submodule.map_bot])
  · refine Submodule.map_injective_of_injective (Submodule.subtype_injective π.V) ?_
    rw [e, Submodule.map_top, Submodule.range_subtype]

theorem exists_hasSatGL_locRep (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hs : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) : ∃ B, HasSatGL w (π.locRep w) B :=
  exists_hasSatGL_of_scalar (fun h hh => exists_scalar (π.isSmooth_locRep w) (isOpen_isCompact_KGL w a).2
    (Final.GLintComm E w a) (Final.HeckeCommGL E w a ℂ) (isBiSimple_locRep π w) (rank_cuspSub π) h hh) hs

theorem eventually_exists_hasSat : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ},
    ∀ (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ, (CG.mk π).HasSat w B := by
  intro E _ _ _ a π
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  let x : π.V := ⟨y, hy⟩
  have hx : x ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  filter_upwards [AeFix.eventually_mem_fixed E a π x] with w hw
  exact exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨x, hw, hx⟩)

end Main

end GlobalTheory.CompanionTheory.SatAe
