import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  obtain ⟨f, hf⟩ := Int.subgroup_cyclic S
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at haS
  obtain ⟨k, rfl⟩ := haS
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem norm_sub_lt (K : FinExt l) (g : GQ l) (hg : ∀ x ∈ K0 K, g x = x) (x : Om l) (hxK : x ∈ K.1)
    (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  have key : ∀ (σ : GQ l) (y : Om l), ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun σ y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key g x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have hζK : ζ ∈ K.1 := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      let b : OO l := ⟨ζ, (norm_root hm hζ).le⟩
      have hb : b ^ m = 1 := Subtype.ext hζ
      have h1 := key σ _ hn
      rw [map_sub, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hxK] at h1
      have h2 : res b = res (galO σ b) := (res_eq_iff _ _).2 (by
        show ‖ζ - σ ζ‖ < 1
        convert h1 using 2; ring)
      exact (congrArg Subtype.val (res_inj hm hlm hb (by rw [← map_pow, hb, map_one]) h2)).symm
    have := key g _ hn
    rw [map_sub, hg ζ ⟨hζK, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩] at this
    simpa using this

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem cyclic_mod (K : FinExt l) {I : Type} [Group I] (j : I →* GQ l)
    (hst : ∀ g, ∀ x ∈ K.1, j g x ∈ K.1) (hfix : ∀ g, ∀ x ∈ K0 K, j g x = x)
    (H : Subgroup I) [H.Normal] [H.FiniteIndex] (hH : ∀ g, g ∈ H ↔ ∀ x ∈ K.1, j g x = x)
    (hN : ¬ l ∣ H.index) : ∃ γ : I, ∀ g : I, ∃ (n : ℕ) (u : I), u ∈ H ∧ g = γ ^ n * u := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := exists_gen K
  let χ : I →* kk l :=
    { toFun := fun g => res (ratio (j g) π)
      map_one' := by rw [res_ratio_iff _ hπ0]; simpa using hπ0
      map_mul' := fun a b => by
        have e : ratio (j (a * b)) π = ratio (j a) π * galO (j a) (ratio (j b) π) := Subtype.ext (by
          show j (a * b) π / π = j a π / π * j a (j b π / π)
          have : j a π ≠ 0 := by simpa using hπ0
          rw [map_mul, AlgEquiv.mul_apply, map_div₀]
          field_simp)
        have e2 : res (galO (j a) (ratio (j b) π)) = res (ratio (j b) π) :=
          (res_eq_iff _ _).2 (norm_sub_lt K (j a) (hfix a) _ (div_mem (hst b π hπ) hπ)
            (ratio (j b) π).2)
        rw [e, map_mul, e2] }
  have hker : ∀ g, χ g = 1 ↔ g ∈ H := by
    intro g
    constructor
    · intro hg
      rw [hH]
      refine fix_of_near K (j g) (hst g) (fun x hx hx0 => ?_) hN (fun x hx => ?_)
      · obtain ⟨k, hk⟩ := hgen x hx hx0
        have hp : π ^ k ≠ 0 := zpow_ne_zero k hπ0
        have hu : ‖x / π ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
        have h1 : res (ratio (j g) (x / π ^ k)) = 1 := by
          rw [res_ratio_iff _ (div_ne_zero hx0 hp), hu]
          exact norm_sub_lt K _ (hfix g) _ (div_mem hx (zpow_mem hπ k)) hu.le
        rw [← res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp, ratio_mul, map_mul, h1,
          res_ratio_zpow _ hπ0 hg, one_mul]
      · rw [← map_pow]
        exact (hH _).1 (H.pow_index_mem g) x hx
    · intro hg
      show res (ratio (j g) π) = 1
      rw [res_ratio_iff _ hπ0, (hH g).1 hg π hπ]
      simpa using hπ0
  let f : I ⧸ H →* kk l := QuotientGroup.lift H χ fun g hg => (hker g).2 hg
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact (QuotientGroup.eq_one_iff g).2 ((hker g).1 ha)
  haveI : IsCyclic (I ⧸ H) := isCyclic_of_injective_ringHom f hf
  obtain ⟨c, hc⟩ := IsCyclic.exists_monoid_generator (α := I ⧸ H)
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨γ, fun g => ?_⟩
  obtain ⟨n, hn⟩ := hc (g : I ⧸ H)
  refine ⟨n, (γ ^ n)⁻¹ * g, QuotientGroup.eq.1 ?_, by rw [mul_inv_cancel_left]⟩
  rw [QuotientGroup.mk_pow]
  exact hn

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem inertia_cyclic : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'), ¬ l ∣ ((pc P h hN hF hS).H.subgroupOf (pc P h hN hF hS).Iner).index → ∃ γ : (pc P h hN hF hS).Iner, ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), ((u : ↥(GK K)) ∈ (pc P h hN hF hS).H) ∧ g = γ ^ n * u := by
  intro l _ P K K' h hN hF hS hidx
  haveI : (pc P h hN hF hS).H.Normal := hN
  haveI : (pc P h hN hF hS).H.FiniteIndex := hF
  haveI : Nontrivial P.R.B := by
    by_contra h
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp h
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _
  refine cyclic_mod K' ((GK K).subtype.comp (pc P h hN hF hS).Iner.subtype) ?_ ?_ _ ?_ hidx
  · intro g x hx
    refine (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
      ((IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => ?_)
    have h1 : (g : ↥(GK K))⁻¹ * ⟨σ, GK_le h hσ⟩ * (g : ↥(GK K)) ∈ GKin h :=
      hN.conj_mem' _ hσ _
    have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x hx
    have h3 := congrArg ((g : ↥(GK K)) : GQ l) h2
    simpa using h3
  · intro g x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      g.2 ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  · intro g
    exact IntermediateField.mem_fixingSubgroup_iff K'.1 ((g : ↥(GK K)) : GQ l)

end GlobalTheory.TameInertiaCyclic
