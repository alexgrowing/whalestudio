import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ValEqCard
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

def loE (n : ℕ) : Fin (n / 2) ↪ Fin n :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, fun a b h => Fin.ext (by
    have h' := congrArg Fin.val h
    exact h')⟩

def hiE (n : ℕ) : Fin (n / 2) ↪ Fin n :=
  ⟨fun i => ⟨n - 1 - i.val, by have := i.isLt; omega⟩, fun a b h => Fin.ext (by
    have h' := congrArg Fin.val h
    change n - 1 - a.val = n - 1 - b.val at h'
    have := a.isLt; have := b.isLt
    omega)⟩

def xiOf (n : ℕ) (β : Fin (n / 2) → ℂˣ) (k : Fin n) : ℂˣ :=
  if h : k.val < n / 2 then β ⟨k.val, h⟩ else if h' : n - 1 - k.val < n / 2 then (β ⟨n - 1 - k.val, h'⟩)⁻¹ else 1

theorem xi_lo (n : ℕ) (β : Fin (n / 2) → ℂˣ) (i : Fin (n / 2)) : xiOf n β (loE n i) = β i := by
  unfold xiOf
  rw [dif_pos (show (loE n i).val < n / 2 from i.isLt)]
  rfl

theorem xi_hi (n : ℕ) (β : Fin (n / 2) → ℂˣ) (i : Fin (n / 2)) : xiOf n β (hiE n i) = (β i)⁻¹ := by
  have hi := i.isLt
  unfold xiOf
  rw [dif_neg (show ¬ (hiE n i).val < n / 2 by show ¬ (n - 1 - i.val < n / 2); omega),
    dif_pos (show n - 1 - (hiE n i).val < n / 2 by show n - 1 - (n - 1 - i.val) < n / 2; omega)]
  have key : ∀ j : Fin (n / 2), j.val = i.val → (β j)⁻¹ = (β i)⁻¹ := by
    intro j hj
    rw [Fin.ext hj]
  exact key _ (by show n - 1 - (n - 1 - i.val) = i.val; omega)

theorem xi_mid (n : ℕ) (β : Fin (n / 2) → ℂˣ) (k : Fin n) (h1 : ¬ k.val < n / 2) (h2 : ¬ n - 1 - k.val < n / 2) :
    xiOf n β k = 1 := by
  unfold xiOf
  rw [dif_neg h1, dif_neg h2]

theorem prod_halves {M : Type} [CommMonoid M] (n : ℕ) (F : Fin n → M)
    (hmid : ∀ k : Fin n, ¬ k.val < n / 2 → ¬ n - 1 - k.val < n / 2 → F k = 1) :
    ∏ k, F k = ∏ i : Fin (n / 2), F (loE n i) * F (hiE n i) := by
  have hdisj : Disjoint (Finset.univ.map (loE n)) (Finset.univ.map (hiE n)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, hi⟩ := Finset.mem_map.1 ha
    obtain ⟨j, -, hj⟩ := Finset.mem_map.1 hb
    have e1 : a.val = i.val := by rw [← hi]; rfl
    have e2 : a.val = n - 1 - j.val := by rw [← hj]; rfl
    have := i.isLt; have := j.isLt
    omega
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      k ∉ Finset.univ.map (loE n) ∪ Finset.univ.map (hiE n) → F k = 1 := by
    intro k _ hk
    have hkl := k.isLt
    apply hmid k
    · intro h
      exact hk (Finset.mem_union_left _ (Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩))
    · intro h
      refine hk (Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨n - 1 - k.val, h⟩, Finset.mem_univ _, Fin.ext ?_⟩))
      show n - 1 - (n - 1 - k.val) = k.val
      omega
  rw [← Finset.prod_subset (Finset.subset_univ _) hsub, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map,
    Finset.prod_mul_distrib]

def uq {E : Type} [Field E] [NumberField E] (w : Pl E) : ℂˣ := Units.mk0 (qh w) (qh_ne_zero' w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem chi_pair (w : Pl E) (β : Fin (n / 2) → ℂˣ) (x : Fin n → ℤ) (i : Fin (n / 2)) :
    chiN w (xiOf n β) (loE n i) ^ x (loE n i) * chiN w (xiOf n β) (hiE n i) ^ x (hiE n i) =
      uq w ^ (((n : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * lOf x i) * β i ^ lOf x i := by
  have hi := i.isLt
  have r1 : rh n (loE n i : ℕ) = (n : ℤ) - 1 - 2 * ((i : ℕ) : ℤ) := rfl
  have r2 : rh n (hiE n i : ℕ) = -((n : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) := by
    show (n : ℤ) - 1 - 2 * (((n - 1 - i.val : ℕ)) : ℤ) = _
    omega
  have hl : lOf x i = x (loE n i) - x (hiE n i) := rfl
  unfold chiN
  rw [xi_lo, xi_hi, unit_power_eq_residue_power, unit_power_eq_residue_power, r1, r2, hl]
  change (β i * uq w ^ _) ^ _ * ((β i)⁻¹ * uq w ^ _) ^ _ = _
  set r : ℤ := (n : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)
  set a := x (loE n i)
  set c := x (hiE n i)
  rw [mul_zpow, mul_zpow, _root_.inv_zpow', ← _root_.zpow_mul, ← _root_.zpow_mul,
    show r * (a - c) = r * a + -r * c by ring, show a - c = a + -c by ring, _root_.zpow_add, _root_.zpow_add]
  ac_rfl

theorem dlt_pw (w : Pl E) (β : Fin (n / 2) → ℂˣ) (x : Fin n → ℤ) :
    dlt n w (lOf x) * pw β (lOf x) = ((∏ k, chiN w (xiOf n β) k ^ x k : ℂˣ) : ℂ) := by
  rw [prod_halves n (fun k => chiN w (xiOf n β) k ^ x k) (fun k h1 h2 => by
    have hk := k.isLt
    show chiN w (xiOf n β) k ^ x k = 1
    unfold chiN
    rw [xi_mid n β k h1 h2, unit_power_eq_residue_power, show rh n (k : ℕ) = 0 by unfold rh; omega]
    simp)]
  simp only [chi_pair]
  rw [Finset.prod_mul_distrib, Units.val_mul, ← zpow_finsum']
  congr 1
  · unfold dlt uq
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  · unfold pw
    rw [Units.coe_prod]

theorem xn_lo (β : Fin (n / 2) → ℂˣ) (k : Fin n) (h : k.val < n / 2) :
    ‖(xiOf n β k : ℂ)‖ = ‖(β ⟨k.val, h⟩ : ℂ)‖ := by
  unfold xiOf
  rw [dif_pos h]

theorem xn_hi (β : Fin (n / 2) → ℂˣ) (k : Fin n) (h1 : ¬ k.val < n / 2) (h : n - 1 - k.val < n / 2) :
    ‖(xiOf n β k : ℂ)‖ = ‖(β ⟨n - 1 - k.val, h⟩ : ℂ)‖⁻¹ := by
  unfold xiOf
  rw [dif_neg h1, dif_pos h, Units.val_inv_eq_inv_val, norm_inv]

theorem xn_mid (β : Fin (n / 2) → ℂˣ) (k : Fin n) (h1 : ¬ k.val < n / 2) (h2 : ¬ n - 1 - k.val < n / 2) :
    ‖(xiOf n β k : ℂ)‖ = 1 := by
  rw [xi_mid n β k h1 h2, Units.val_one, norm_one]

theorem xi_mono (β : Fin (n / 2) → ℂˣ) (hm : ∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖)
    (hg : ∀ i, 1 ≤ ‖(β i : ℂ)‖) : N3.Mono (xiOf n β) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hi := i.isLt; have hj := j.isLt
  have hpos : ∀ k, 0 < ‖(β k : ℂ)‖ := fun k => lt_of_lt_of_le one_pos (hg k)
  by_cases h1 : i.val < n / 2
  · by_cases h3 : j.val < n / 2
    · rw [xn_lo β j h3, xn_lo β i h1]
      exact hm _ _ hij'
    · by_cases h4 : n - 1 - j.val < n / 2
      · rw [xn_hi β j h3 h4, xn_lo β i h1]
        exact le_trans (inv_le_one_of_one_le₀ (hg _)) (hg _)
      · rw [xn_mid β j h3 h4, xn_lo β i h1]
        exact hg _
  · have h3 : ¬ j.val < n / 2 := by omega
    by_cases h2 : n - 1 - i.val < n / 2
    · have h4 : n - 1 - j.val < n / 2 := by omega
      rw [xn_hi β j h3 h4, xn_hi β i h1 h2]
      exact inv_anti₀ (hpos _) (hm _ _ (show n - 1 - j.val ≤ n - 1 - i.val by omega))
    · rw [xn_mid β i h1 h2]
      by_cases h4 : n - 1 - j.val < n / 2
      · rw [xn_hi β j h3 h4]
        exact inv_le_one_of_one_le₀ (hg _)
      · rw [xn_mid β j h3 h4]

theorem xi_map (β : Fin (n / 2) → ℂˣ) : Finset.univ.val.map (xiOf n β) = GlobalTheory.LGrp.bcParam n β := by
  have e1 : (Finset.univ : Finset (Fin n)).filter (fun k => k.val < n / 2) = Finset.univ.map (loE n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      exact ⟨⟨k.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  have e2 : ((Finset.univ : Finset (Fin n)).filter (fun k => ¬ k.val < n / 2)).filter
      (fun k => n - 1 - k.val < n / 2) = Finset.univ.map (hiE n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    have hk := k.isLt
    constructor
    · rintro ⟨-, h⟩
      refine ⟨⟨n - 1 - k.val, h⟩, Fin.ext ?_⟩
      show n - 1 - (n - 1 - k.val) = k.val
      omega
    · rintro ⟨i, rfl⟩
      have := i.isLt
      exact ⟨by show ¬ (n - 1 - i.val < n / 2); omega, by show n - 1 - (n - 1 - i.val) < n / 2; omega⟩
  set S := ((Finset.univ : Finset (Fin n)).filter (fun k => ¬ k.val < n / 2)).filter
      (fun k => ¬ n - 1 - k.val < n / 2) with hS
  have e3 : S.val.map (xiOf n β) = Multiset.replicate S.card 1 := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun u hu => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.1 hu
    have hk2 : k ∈ S := hk
    rw [hS] at hk2
    have hk' := Finset.mem_filter.1 hk2
    exact xi_mid n β k (Finset.mem_filter.1 hk'.1).2 hk'.2
  have hsplit : (Finset.univ : Finset (Fin n)).val =
      ((Finset.univ : Finset (Fin n)).filter (fun k => k.val < n / 2)).val +
      (((Finset.univ : Finset (Fin n)).filter (fun k => ¬ k.val < n / 2)).filter
        (fun k => n - 1 - k.val < n / 2)).val + S.val := by
    rw [hS, add_assoc]
    simp only [Finset.filter_val]
    rw [Multiset.filter_add_not, Multiset.filter_add_not]
  have hcard : S.card = n % 2 := by
    have hc := congrArg Multiset.card hsplit
    simp only [Multiset.card_add, ← Finset.card_def, e1, e2, Finset.card_map, Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [hsplit, Multiset.map_add, Multiset.map_add, e3, hcard, e1, e2, Finset.map_val, Finset.map_val, Multiset.map_map,
    Multiset.map_map]
  unfold GlobalTheory.LGrp.bcParam
  congr 3
  · funext i
    exact xi_lo n β i
  · funext i
    exact xi_hi n β i

theorem levOp_fsum {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (A : V →ₗ[ℂ] V) (s : Finset ι) (a : ι → ℂ) (f : ι → G → ℂ)
    (hf : ∀ i, {q : G ⧸ K' | f i q.out ≠ 0}.Finite) :
    levOp ρ K K' (∑ i ∈ s, a i • f i) A = ∑ i ∈ s, a i • levOp ρ K K' (f i) A := by
  induction s using Finset.induction_on with
  | empty =>
    simp [levOp]
  | insert j s hj ih =>
    have hfin : {q : G ⧸ K' | (∑ i ∈ s, a i • f i) q.out ≠ 0}.Finite := by
      refine (s.finite_toSet.biUnion fun i _ => hf i).subset ?_
      intro q hq
      have hq' : ∑ i ∈ s, a i * f i q.out ≠ 0 := by
        simpa [Finset.sum_apply] using hq
      obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
      exact Set.mem_biUnion hi (right_ne_zero_of_mul hne)
    have hfin1 : {q : G ⧸ K' | (a j • f j) q.out ≠ 0}.Finite :=
      (hf j).subset fun q hq => right_ne_zero_of_mul (by simpa using hq)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, GlobalTheory.TwTrLin.levOp_add ρ K K' _ _ A hfin1 hfin,
      GlobalTheory.TwTrLin.levOp_smul_fun, ih]

theorem isHecke_fsum {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (s : Finset ι) (a : ι → ℂ) (f : ι → G → ℂ) (hf : ∀ i, IsHecke K' (f i)) : IsHecke K' (∑ i ∈ s, a i • f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact GlobalTheory.CompanionTheory.LocHecke.isHecke_add (GlobalTheory.CompanionTheory.LocHecke.isHecke_smul _ (hf j)) ih

theorem coneEigOf : ConeEigOf := by
  intro hEI hBW E _ _ _ n w hw b ϖ q σ α hb hϖ hq hadm hsat
  obtain ⟨β, hWβ, hmono, hge, y, hyfix, hy0, hey⟩ := hEI E n w hw b ϖ q σ α hb hϖ hq hadm hsat
  refine ⟨xiOf n β, xi_mono β hmono hge, by rw [hBW n α β hWβ]; exact xi_map β, ⟨y, hyfix⟩,
    fun h => hy0 (congrArg Subtype.val h), fun c hc => ?_⟩
  have ho := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b
  have hidx : (iwU n w b).relIndex (KL n w) ≠ 0 :=
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero ho (GlobalTheory.LocFinU.isCompact_KL n w)
  have hH : ∀ l, IsHecke (iwU n w b) (fU n w b ϖ l) := fun l =>
    GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ l (GlobalTheory.LocFinU.continuous_cj w)
  have hidx' : (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hg : gc w b ϖ c = ∑ x ∈ c.support,
      (c x * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)) • fU n w b ϖ (lOf x) := by
    funext γ
    simp only [gc, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hHg : IsHecke (iwU n w b) (gc w b ϖ c) := by
    rw [hg]
    exact isHecke_fsum _ _ _ _ fun x => hH _
  have hcone : ∀ x ∈ c.support, Cone (lOf x) := by
    intro x hx
    by_cases hn : 2 ≤ n
    · exact coneTwo n x hn (hc hx)
    · refine ⟨fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
  apply Subtype.ext
  rw [GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho hHg, hg,
    levOp_fsum _ _ _ _ _ _ _ fun x => GlobalTheory.TwTrLin.finite_out_support ho (hH _).1,
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [Submodule.coe_smul, evalGL, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hey (lOf x) (hcone x hx), smul_smul, ← dlt_pw w β x]
  congr 1
  field_simp

end PositivityTheory.Rg.BcB.F.FX

end
