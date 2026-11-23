import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.FixProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem rU_mul (x y : UA E a) (f : UA E a → ℂ) : RU E a (x * y) f = RU E a x (RU E a y f) := by
  rw [map_mul]; rfl

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU a w ≤ finU E a :=
  fun _ hx => (Subgroup.mem_inf.1 hx).1

theorem commute_of_apart {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) {x y : UA E a}
    (hx : x ∈ locU a w) (hy : y ∈ locU a u) : Commute x y := by
  show x * y = y * x
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hx, GlobalTheory.DefU.LocRet.mem_locU_inf hy]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have hv' : v.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E)) := hv ▸ h
      simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hy hv', one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hx hv, one_mul, mul_one]

section Avg

variable (K : Subgroup (UA E a)) (K' : Subgroup K) [Fintype (K ⧸ K')]

def avg : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ) :=
  ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a)

theorem avg_apply (f : UA E a → ℂ) :
    avg K K' f = ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a) f := by
  unfold avg
  exact LinearMap.sum_apply _ _ _

theorem avg_comm {c : UA E a} (hc : ∀ k ∈ K, Commute c k) (f : UA E a → ℂ) :
    avg K K' (RU E a c f) = RU E a c (avg K K' f) := by
  rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← rU_mul, ← rU_mul, (hc _ (Quotient.out q).2).eq]

theorem avg_of_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K, RU E a k f = f) :
    avg K K' f = (Fintype.card (K ⧸ K') : ℂ) • f := by
  rw [avg_apply, Finset.sum_congr rfl (fun q _ => hf _ (Quotient.out q).2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem avg_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K', RU E a ((k : K) : UA E a) f = f) (k : UA E a) (hk : k ∈ K) :
    RU E a k (avg K K' f) = avg K K' f := by
  rw [avg_apply, map_sum]
  have key : ∀ q : K ⧸ K', RU E a k (RU E a ((Quotient.out q : K) : UA E a) f) =
      RU E a ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : UA E a) f := by
    intro q
    have hm : (Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (⟨k, hk⟩ : K) * Quotient.out q = Quotient.out ((⟨k, hk⟩ : K) • q) *
        ((Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q)) := (mul_inv_cancel_left _ _).symm
    have e' := congrArg (fun z : K => (z : UA E a)) e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at e'
    have hm' := hf _ hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hm'
    rw [← rU_mul, e', rU_mul, hm']
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun q => rfl)

end Avg

theorem mend (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (UA E a)) (hKw : K ≤ locU a w) (hKc : IsCompact (K : Set (UA E a)))
    {φw : UA E a → ℂ} (hφwU : φw ∈ U) (hφw0 : φw ≠ 0) (hφwK : ∀ k ∈ K, RU E a k φw = φw)
    {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0) :
    ∃ ψ ∈ U, ψ ≠ 0 ∧ (∀ k ∈ K, RU E a k ψ = ψ) ∧
      ∀ y : UA E a, (∀ x ∈ locU a w, Commute y x) → RU E a y φ = φ → RU E a y ψ = ψ := by
  classical

  let S := Submodule.span ℂ (Set.range fun g : UA E a => RU E a g φ)
  have hSU : S ≤ U := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hU.stable g φ hφU)
  have hSst : ∀ x, ∀ f ∈ S, RU E a x f ∈ S := by
    intro x f hf
    have : S ≤ S.comap (RU E a x) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU E a x (RU E a g φ) ∈ S
      rw [← rU_mul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact this hf
  have hφS : φ ∈ S := by
    have h1 : RU E a 1 φ = φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = U := by
    rcases hU.irred S hSU hSst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hφS)) hφ0
    · exact h
  have hφwS : φw ∈ S := hSeq ▸ hφwU
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφwS

  let r : UA E a → UA E a := fun g => (GlobalTheory.DefU.LocRet.ret w a g : UA E a)
  have hr : ∀ g, r g ∈ locU a w := fun g => (GlobalTheory.DefU.LocRet.ret w a g).2
  have hd : ∀ g, ∀ x ∈ locU a w, Commute ((r g)⁻¹ * g) x := fun g x hx =>
    GlobalTheory.DefU.LocRet.commute_ret g ⟨x, hx⟩
  have hsplit : ∀ g, RU E a g φ = RU E a ((r g)⁻¹ * g) (RU E a (r g) φ) := by
    intro g
    rw [← rU_mul, (hd g (r g) (hr g)).eq, mul_inv_cancel_left]

  have hKf : K ≤ finU E a := hKw.trans (locU_le_finU w)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let K' : Subgroup K :=
    { carrier := {k | ∀ g ∈ c.support, RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ}
      mul_mem' := fun {x y} hx hy g hg => by
        show RU E a ((x : UA E a) * (y : UA E a)) _ = _
        rw [rU_mul, hy g hg, hx g hg]
      one_mem' := fun g _ => by
        show RU E a 1 _ = _
        rw [map_one]; rfl
      inv_mem' := fun {x} hx g hg => by
        have h := hx g hg
        show RU E a ((x : UA E a)⁻¹) _ = _
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) (RU E a (r g) φ)) := by rw [h]
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hK'o : IsOpen (K' : Set K) := by
    have e : (K' : Set K) =
        ⋂ g ∈ c.support, {k : K | RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ} := by
      ext k
      rw [Set.mem_iInter₂]
      rfl
    rw [e]
    refine isOpen_biInter_finset fun g _ => ?_
    have ho := (hU.aut _ (hU.stable (r g) φ hφU)).level
    have hcont : Continuous fun k : K => (⟨(k : UA E a), hKf k.2⟩ : finU E a) :=
      continuous_subtype_val.subtype_mk _
    exact ho.preimage hcont
  haveI : Finite (K ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'o
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  have hA : avg K K' φw = c.sum fun g b => b • RU E a ((r g)⁻¹ * g) (avg K K' (RU E a (r g) φ)) := by
    rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hsplit g, avg_comm K K' (fun k hk => hd g k (hKw hk))]
  by_cases h0 : ∀ g ∈ c.support, avg K K' (RU E a (r g) φ) = 0
  · exfalso
    have hz : avg K K' φw = 0 := by
      rw [hA, Finsupp.sum]
      exact Finset.sum_eq_zero fun g hg => by rw [h0 g hg, map_zero, smul_zero]
    rw [avg_of_fixed K K' hφwK] at hz
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    exact hφw0 ((smul_eq_zero.1 hz).resolve_left hcard)
  · push_neg at h0
    obtain ⟨g, hg, hne⟩ := h0
    refine ⟨avg K K' (RU E a (r g) φ), ?_, hne, ?_, ?_⟩
    · rw [avg_apply]
      exact Submodule.sum_mem _ fun q _ => hU.stable _ _ (hU.stable _ _ hφU)
    · exact avg_fixed K K' (fun k hk => hk g hg)
    · intro y hy hyφ
      rw [← avg_comm K K' (fun k hk => hy k (hKw hk)), ← rU_mul, (hy (r g) (hr g)).eq, rU_mul, hyφ]

theorem fix_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w a) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  intro E _ _ _ a U hU w₀ K hKl hKeq hKc hKint _ hφ'
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU E a) :=
    { carrier := {k | RU E a (k : UA E a) φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        show RU E a ((x : UA E a) * (y : UA E a)) φ₀ = φ₀
        rw [rU_mul]
        exact (congrArg _ hy).trans hx
      one_mem' := by
        show RU E a 1 φ₀ = φ₀
        rw [map_one]; rfl
      inv_mem' := fun {x} hx => by
        show RU E a ((x : UA E a)⁻¹) φ₀ = φ₀
        have hx' : RU E a (x : UA E a) φ₀ = φ₀ := hx
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) φ₀) := by rw [hx']
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hLo : IsOpen (L : Set (finU E a)) := (hU.aut φ₀ hφ₀U).level
  have hev := GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo
  have hgood : ∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, RU E a x φ₀ = φ₀ := by
    filter_upwards [hev, hKint] with w h1 h2 x hx
    exact h1 x (hKl w hx) (h2 x hx) (locU_le_finU w (hKl w hx))
  have hB := Filter.eventually_cofinite.1 hgood
  have main : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), ∃ φ ∈ U, φ ≠ 0 ∧ ∀ u, Apart u w₀ →
      ((∀ x ∈ K u, RU E a x φ₀ = φ₀) ∨ u ∈ S) → ∀ x ∈ K u, RU E a x φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨φ₀, hφ₀U, hφ₀, fun u _ hu x hx => ?_⟩
      rcases hu with hu | hu
      · exact hu x hx
      · exact absurd hu (Finset.notMem_empty u)
    | insert w S hwS ih =>
      obtain ⟨φ, hφU, hφ0, hφ⟩ := ih
      by_cases hw : Apart w w₀
      · obtain ⟨φw, hφwU, hφw0, hφwK⟩ := hφ' w hw
        obtain ⟨ψ, hψU, hψ0, hψK, hψy⟩ := mend U hU w (K w) (hKl w) (hKc w) hφwU hφw0 hφwK hφU hφ0
        refine ⟨ψ, hψU, hψ0, fun u hu hu' x hx => ?_⟩
        by_cases hap : Apart u w
        · refine hψy x (fun z hz => commute_of_apart hap (hKl u hx) hz) ?_
          rcases hu' with h | h
          · exact hφ u hu (Or.inl h) x hx
          · rcases Finset.mem_insert.1 h with rfl | h
            · exact absurd rfl hap
            · exact hφ u hu (Or.inr h) x hx
        · rw [hKeq u w hap] at hx
          exact hψK x hx
      · refine ⟨φ, hφU, hφ0, fun u hu hu' x hx => ?_⟩
        rcases hu' with h | h
        · exact hφ u hu (Or.inl h) x hx
        · rcases Finset.mem_insert.1 h with rfl | h
          · exact absurd hu hw
          · exact hφ u hu (Or.inr h) x hx
  obtain ⟨φ, hφU, hφ0, hφ⟩ := main hB.toFinset
  refine ⟨φ, hφU, hφ0, fun u hu x hx => hφ u hu ?_ x hx⟩
  by_cases h : ∀ x ∈ K u, RU E a x φ₀ = φ₀
  · exact Or.inl h
  · exact Or.inr (hB.mem_toFinset.2 h)

end GlobalTheory.Cong.FixProd
