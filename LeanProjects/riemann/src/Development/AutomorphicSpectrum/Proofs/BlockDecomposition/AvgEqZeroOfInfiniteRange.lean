import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLTwConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchLinear

theorem index_rStab_ne_zero {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (u : H → ℂ) (hu : IsLocallyConstant u) : (rStab u).index ≠ 0 := by
  have hd : IsLocallyConstant fun p : H × H => u (p.1 * p.2) - u p.1 :=
    (hu.comp_continuous (continuous_fst.mul continuous_snd)).sub (hu.comp_continuous continuous_fst)
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ := generalized_tube_lemma (isCompact_univ (X := H)) (isCompact_singleton (x := (1 : H)))
    (hd.isOpen_fiber 0) (fun p hp => by
      obtain ⟨-, h⟩ := hp
      have : p.2 = 1 := h
      simp [this])
  have hsub : B ⊆ (rStab u : Set H) := fun k hk x =>
    sub_eq_zero.1 (hAB (show (x, k) ∈ A ×ˢ B from ⟨hA (Set.mem_univ x), hk⟩))
  have hopen : IsOpen (rStab u : Set H) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hB.mem_nhds (h1 rfl)) hsub)
  haveI := Subgroup.quotient_finite_of_isOpen (rStab u) hopen
  exact Subgroup.index_ne_zero_of_finite

theorem avg_lin {H : Type} [Group H] (S : Subgroup H) (hS : S.index ≠ 0) {J : Type} [Fintype J] (a : J → ℂ)
    (u : J → H → ℂ) (hu : ∀ j, S ≤ rStab (u j)) :
    avg (fun h => ∑ j, a j * u j h) = ∑ j, a j * avg (u j) := by
  have hsum : S ≤ rStab (fun h => ∑ j, a j * u j h) := fun k hk => show ∀ x, _ from fun x =>
    Finset.sum_congr rfl fun j _ => by rw [(hu j hk : ∀ x, u j (x * k) = u j x) x]
  haveI : S.FiniteIndex := ⟨hS⟩
  haveI : Finite (H ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (H ⧸ S) := Fintype.ofFinite _
  rw [avg_eq_of_le_rStab _ _ S hsum hS, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [avg_eq_of_le_rStab _ _ S (hu j) hS, finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  ring

theorem twOrb_lin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (hθ : Continuous θ)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (y : G) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (hg : ∀ j, IsLocallyConstant (g j))
    (hfin : ∀ j, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      ∃ k ∈ K, g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)) ≠ 0}.Finite) :
    twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hsupp : ∀ j, (Function.support fun q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) =>
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).Finite := by
    intro j
    refine (hfin j).subset fun q hq => ?_
    by_contra hno
    simp only [Set.mem_setOf_eq, not_exists, not_and, ne_eq, not_not] at hno
    apply hq
    have h0 : (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = fun _ => 0 :=
      funext fun k => hno k k.2
    have ha : avg (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = 0 := by
      rw [h0]; simp [avg]
    simp only [ha, mul_zero]
  unfold twOrb
  have hterm : ∀ q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G),
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        (avg fun k : K => ∑ j, a j * g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) =
      ∑ j, a j * ((((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) := by
    intro q
    have hc : Continuous fun k : K => (Quotient.out q * (k : G))⁻¹ * y * θ (Quotient.out q * (k : G)) := by
      have h1 : Continuous fun k : K => Quotient.out q * (k : G) := continuous_const.mul continuous_subtype_val
      exact (h1.inv.mul continuous_const).mul (hθ.comp h1)
    have hi : ∀ j, (rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).index ≠ 0 :=
      fun j => index_rStab_ne_zero _ ((hg j).comp_continuous hc)
    rw [avg_lin (⨅ j, rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)))
      (Subgroup.index_iInf_ne_zero hi) a
      (fun j (k : K) => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) (fun j => iInf_le _ j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

theorem clSum_lin {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ)
    (hS : {c : TwCl θ | c.rep ∈ S}.Finite) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (h : ∀ y ∈ S, twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j)) :
    clSum θ K S wt (fun z => ∑ j, a j * g j z) = ∑ j, a j * clSum θ K S wt (g j) := by
  have hsupp : ∀ j, (Function.support fun c : TwCl θ => if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0).Finite :=
    fun j => hS.subset fun c hc => by
      by_contra hn
      exact hc (if_neg hn)
  unfold clSum
  have hterm : ∀ c : TwCl θ, (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (fun z => ∑ j, a j * g j z) else 0) =
      ∑ j, a j * (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0) := by
    intro c
    by_cases hc : c.rep ∈ S
    · simp only [if_pos hc, h _ hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x g : GLw n w) :
    (nrmL n w (g⁻¹ * x * thL n w g)).val.charpoly = (nrmL n w x).val.charpoly := by
  rw [GlobalTheory.CompanionTheory.TwistOrbit.nrmL_twConj' hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

theorem finite_dc_unitary (hU : Unr E) (n : ℕ) (w : Pl E) (y : UL n w) (hy : y.1.val.charpoly.Separable)
    (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (KL n w : Set (UL n w)) |
      ∃ k ∈ KL n w, f ((Quotient.out q * k)⁻¹ * y * MonoidHom.id (UL n w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  obtain ⟨D, hD, hP⟩ := GlobalTheory.OrbitU.orbit_cpt_U E hU n w y hy _ hf.isCompact
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : UL n w × UL n w => p.1 * p.2⁻¹) '' (D ×ˢ (KL n w : Set (UL n w))))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ KL n w,
      f ((x * k)⁻¹ * y * MonoidHom.id (UL n w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem finite_dc_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (f : GLw a w × GLw b w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) |
      ∃ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), f ((Quotient.out q * k)⁻¹ * y *
        (thL a w).prodMap (thL b w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨D, hD, hP⟩ := GlobalTheory.CompanionTheory.TwistOrbit.proper_pair hU a b w y h₁ h₂ _ hf.isCompact
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK (E := E) a b w
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) '' (D ×ˢ _))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b),
      f ((x * k)⁻¹ * y * (thL a w).prodMap (thL b w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem matchLin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a b : ℕ) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ)
    (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, IsLocallyConstant (f j) ∧ HasCompactSupport (f j) ∧ IsLocallyConstant (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y) := by
  intro E _ _ _ hU n a b w μ J _ c f φ hreg hM Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  have e₁ : stTw2 a b w Q₁ Q₂ (fun y => ∑ j, c j * φ j y) = ∑ j, c j * stTw2 a b w Q₁ Q₂ (φ j) := by
    unfold stTw2
    refine clSum_lin _ _ _ _ ?_ c φ ?_
    · exact GlobalTheory.BCT.StTw2Add.finite_prod _ _ (fun x => (nrmL a w x).val.charpoly = Q₁)
        (fun x => (nrmL b w x).val.charpoly = Q₂)
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ hs₁).1 (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ hs₂).1
    · rintro y ⟨hy₁, hy₂⟩
      have hθ : Continuous ((thL a w).prodMap (thL b w)) :=
        ((GlobalTheory.BCT.thL_continuous_involutive E hU a w).1.comp continuous_fst).prodMk
          ((GlobalTheory.BCT.thL_continuous_involutive E hU b w).1.comp continuous_snd)
      exact twOrb_lin _ hθ _ (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b w).2 y c φ (fun j => (hreg j).2.2.1)
        fun j => finite_dc_pair hU a b w y (hy₁ ▸ hs₁) (hy₂ ▸ hs₂) (φ j) (hreg j).2.2.2
  have e₂ : kapOrb n w Q₁ Q₂ (fun γ => ∑ j, c j * f j γ) = ∑ j, c j * kapOrb n w Q₁ Q₂ (f j) := by
    unfold kapOrb
    refine clSum_lin _ _ _ _ (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (Q₁ * Q₂) hsep).2 c f ?_
    intro y hy
    exact twOrb_lin _ continuous_id _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 y c f (fun j => (hreg j).1)
      fun j => finite_dc_unitary hU n w y (by rw [show y.1.val.charpoly = Q₁ * Q₂ from hy]; exact hsep) (f j) (hreg j).2.1
  rw [e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM j Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂]
  ring

end GlobalTheory.CompanionTheory.MatchLinear
