import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestSpan

section Abstract

variable {p : ℕ} [Fact p.Prime] {J : Type} [Fintype J]

theorem norm_sum_lt {I : Type} [Fintype I] (f : I → PadicAlgCl p) {ε : ℝ} (hε : 0 < ε) (h : ∀ i, ‖f i‖ < ε) :
    ‖∑ i, f i‖ < ε := by
  refine Finset.sum_induction f (fun x => ‖x‖ < ε) (fun a b ha hb => ?_) (by simpa using hε) fun i _ => h i
  exact (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem map_mulVec' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Matrix J J R) (w : J → R) :
    (A.map f).mulVec (fun j => f (w j)) = fun j => f (A.mulVec w j) := by
  funext j
  simp [Matrix.mulVec, dotProduct]

theorem norm_mul_le_of_irreducible {I : Type} (P : Matrix J J (OO p)) (hP : P * P = P) (s : Set I)
    (A : I → Matrix J J (OO p)) (hcomm : ∀ h ∈ s, P * A h = A h * P)
    (hirr : ∀ W : Submodule (kb p) (J → kb p),
      (∀ v ∈ W, (P.map (IsLocalRing.residue (OO p))).mulVec v = v) →
      (∀ h ∈ s, ∀ v ∈ W, ((A h).map (IsLocalRing.residue (OO p))).mulVec v ∈ W) →
      W = ⊥ ∨ ∀ v, (P.map (IsLocalRing.residue (OO p))).mulVec v = v → v ∈ W)
    (M : Submodule (OO p) (J → PadicAlgCl p))
    (hM : ∀ h ∈ s, ∀ e ∈ M, ((A h).map (OO p).subtype).mulVec e ∈ M)
    (x : J → PadicAlgCl p) (δ ε : ℝ) (hε : 0 < ε) (hx : ∀ e ∈ M, ‖e ⬝ᵥ x‖ ≤ δ)
    (hle : ∀ i, ‖∑ j, (P j i : PadicAlgCl p) * x j‖ ≤ ε) (i₁ : J) (hge : ε ≤ ‖∑ j, (P j i₁ : PadicAlgCl p) * x j‖)
    (v : J → PadicAlgCl p) (hv : v ∈ M) (hPv : (P.map (OO p).subtype).mulVec v = v) (j : J) :
    ‖v j‖ * ε ≤ δ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) ⟨j, Finset.mem_univ _⟩
  refine (mul_le_mul_of_nonneg_right (hi₀ j (Finset.mem_univ _)) hε.le).trans ?_
  by_cases h0 : v i₀ = 0
  · simpa [h0] using hx 0 M.zero_mem
  have hpos : 0 < ‖v i₀‖ := norm_pos_iff.2 h0
  let r := IsLocalRing.residue (OO p)
  let W : Submodule (kb p) (J → kb p) :=
    { carrier := {z | ∃ w : J → OO p, P.mulVec w = w ∧ v i₀ • (fun j => (w j : PadicAlgCl p)) ∈ M ∧
        z = fun j => r (w j)}
      add_mem' := by
        rintro _ _ ⟨w, h1, h2, rfl⟩ ⟨w', h1', h2', rfl⟩
        refine ⟨w + w', by rw [Matrix.mulVec_add, h1, h1'], ?_, funext fun j => by simp⟩
        convert M.add_mem h2 h2' using 1
        funext j
        simp [mul_add]
      zero_mem' := ⟨0, by simp, by
        convert M.zero_mem using 1
        funext j
        simp, funext fun j => by simp⟩
      smul_mem' := by
        rintro c _ ⟨w, h1, h2, rfl⟩
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨a • w, by rw [Matrix.mulVec_smul, h1], ?_, funext fun j => by simp [r]⟩
        convert M.smul_mem a h2 using 1
        funext j
        change v i₀ * ((a : PadicAlgCl p) * w j) = (a : PadicAlgCl p) * (v i₀ * w j)
        ring }
  have hW := hirr W (by
      rintro _ ⟨w, h1, -, rfl⟩
      rw [map_mulVec', h1])
    (by
      rintro h hh _ ⟨w, h1, h2, rfl⟩
      refine ⟨(A h).mulVec w, ?_, ?_, map_mulVec' _ _ _⟩
      · rw [Matrix.mulVec_mulVec, hcomm h hh, ← Matrix.mulVec_mulVec, h1]
      · have h3 := hM h hh _ h2
        rw [Matrix.mulVec_smul] at h3
        have h4 := map_mulVec' (OO p).subtype (A h) w
        simp only [ValuationSubring.coe_subtype] at h4 h3
        rwa [h4] at h3)
  let w₀ : J → OO p := fun j => ⟨v j / v i₀, (mem_OO_iff _).2 (by
    rw [norm_div, div_le_one hpos]
    exact hi₀ j (Finset.mem_univ _))⟩
  have hw₀ : v i₀ • (fun j => (w₀ j : PadicAlgCl p)) = v := by
    funext j
    change v i₀ * (v j / v i₀) = v j
    field_simp
  have hmem : (fun j => r (w₀ j)) ∈ W := by
    refine ⟨w₀, ?_, hw₀.symm ▸ hv, rfl⟩
    have h4 := map_mulVec' (OO p).subtype P w₀
    simp only [ValuationSubring.coe_subtype] at h4 hPv
    rw [← hw₀, Matrix.mulVec_smul, h4] at hPv
    funext j
    exact Subtype.ext (mul_left_cancel₀ h0 (congrFun hPv j))
  rcases hW with hW | hW
  · rw [hW, Submodule.mem_bot] at hmem
    have h1 : w₀ i₀ = 1 := Subtype.ext (div_self h0)
    have h2 := congrFun hmem i₀
    simp [h1] at h2
  have hcol : P.mulVec (fun j => P j i₁) = fun j => P j i₁ := by
    funext j
    exact congrFun (congrFun hP j) i₁
  obtain ⟨w, h1, h2, h3⟩ := hW (fun j => r (P j i₁)) (by rw [map_mulVec', hcol])
  have hz : ∀ j, ‖((P j i₁ - w j : OO p) : PadicAlgCl p)‖ < 1 := fun j => by
    rw [← not_isUnit_OO_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit, not_not, map_sub]
    exact sub_eq_zero.2 (congrFun h3 j)
  have hfix : ∀ j, (P j i₁ - w j : OO p) = ∑ i, P j i * (P i i₁ - w i) := fun j => by
    have h5 := congrFun hcol j
    have h6 := congrFun h1 j
    simp only [Matrix.mulVec, dotProduct] at h5 h6
    simp only [mul_sub, Finset.sum_sub_distrib, h5, h6]
  have hsum : ∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j =
      ∑ i, ((P i i₁ - w i : OO p) : PadicAlgCl p) * ∑ j, (P j i : PadicAlgCl p) * x j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfix j, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul]
    ring
  have hlt : ‖∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j‖ < ε := by
    rw [hsum]
    refine norm_sum_lt _ hε fun i => ?_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hle i) (norm_nonneg _)).trans_lt (by nlinarith [hz i])
  have hdec : ∑ j, (P j i₁ : PadicAlgCl p) * x j =
      ∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j + ∑ j, (w j : PadicAlgCl p) * x j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hw : ε ≤ ‖∑ j, (w j : PadicAlgCl p) * x j‖ := by
    rw [hdec] at hge
    have := hge.trans (IsUltrametricDist.norm_add_le_max _ _)
    rcases le_max_iff.1 this with h | h
    · exact absurd h (not_le.2 hlt)
    · exact h
  have h7 := hx _ h2
  rw [smul_dotProduct, smul_eq_mul, norm_mul] at h7
  exact (mul_le_mul_of_nonneg_left hw hpos.le).trans h7

end Abstract

section System

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_mul_comm (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (h : S.Gam) (hh : h ∈ S.perp T) :
    S.proj T c * S.ρ h = S.ρ h * S.proj T c := by
  have := Fintype.ofFinite T
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : eStd S.g _ h t = 0 := hh t t.2
  rw [mul_smul_comm, smul_mul_assoc, S.ρ_add _ _ (by rw [Weights.eStd_swap, h1, neg_zero, smul_zero]),
    S.ρ_add _ _ (by rw [h1, smul_zero]), add_comm]

variable {p : ℕ} [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p)

def bdd (H : AddSubgroup S.Gam) (δ : ℝ) (hδ : 0 ≤ δ) : Submodule (OO p) (S.J → PadicAlgCl p) where
  carrier := {e | ∀ a ∈ H, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ δ}
  add_mem' := fun {e e'} he he' a ha => by
    rw [add_dotProduct]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (he a ha) (he' a ha))
  zero_mem' := fun a _ => by simpa using hδ
  smul_mem' := fun c e he a ha => by
    change ‖((c : PadicAlgCl p) • e) ⬝ᵥ _‖ ≤ δ
    rw [smul_dotProduct, smul_eq_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_right ((mem_OO_iff _).1 c.2) (norm_nonneg _)).trans (by simpa using he a ha)

theorem bdd_stable (φ : o →+* OO p) (hφ : ∀ a, (φ a : PadicAlgCl p) = y₀ (algebraMap o S.R a))
    (hev : ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n =
      algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i)
    (H : AddSubgroup S.Gam) (δ : ℝ) (hδ : 0 ≤ δ) (h : S.Gam) (hh : h ∈ H) (e : S.J → PadicAlgCl p)
    (he : e ∈ bdd y₀ H δ hδ) : (((S.ρ h).map φ).map (OO p).subtype).mulVec e ∈ bdd y₀ H δ hδ := by
  intro a ha
  obtain ⟨k, hk⟩ := hev h a
  have h1 : ∀ i, ∑ n, (φ (S.ρ h n i) : PadicAlgCl p) * y₀ ⟨S.ev a n, S.ev_mem a n⟩ =
      (φ (S.ζ ^ k) : PadicAlgCl p) * y₀ ⟨S.ev (a + S.r • h) i, S.ev_mem _ i⟩ := fun i => by
    simp only [hφ, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    exact hk i
  have h2 : (((S.ρ h).map φ).map (OO p).subtype).mulVec e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) =
      (φ (S.ζ ^ k) • e) ⬝ᵥ (fun i => y₀ ⟨S.ev (a + S.r • h) i, S.ev_mem _ i⟩) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ((φ (S.ζ ^ k) : PadicAlgCl p) * e i) * _
    rw [mul_right_comm, ← h1 i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    change (φ (S.ρ h n i) : PadicAlgCl p) * e i * _ = _
    ring
  rw [h2]
  exact (bdd y₀ H δ hδ).smul_mem _ he _ (H.add_mem ha (H.nsmul_mem hh _))

theorem proj_stable (φ : o →+* OO p) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (M : Submodule (OO p) (S.J → PadicAlgCl p))
    (hM : ∀ t ∈ T, ∀ e ∈ M, (((S.ρ t).map φ).map (OO p).subtype).mulVec e ∈ M) (e : S.J → PadicAlgCl p)
    (he : e ∈ M) : (((S.proj T c).map φ).map (OO p).subtype).mulVec e ∈ M := by
  have := Fintype.ofFinite T
  have h1 : (((S.proj T c).map φ).map (OO p).subtype).mulVec e =
      ∑ t : T, φ (Ring.inverse (Nat.card T : o) * S.ζN ^ (-(c t)).val) •
        (((S.ρ t).map φ).map (OO p).subtype).mulVec e := by
    funext j
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, Finset.sum_mul, Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    change _ = (OO p).subtype _ * _
    simp only [map_mul]
    ring
  rw [h1]
  exact M.sum_mem fun t _ => M.smul_mem _ (hM t t.2 e he)

variable {y₀} (τ : S.Test p y₀)

theorem exists_le_norm (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {α : τ.X}
    (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) : ∃ t ∈ S.perp τ.yy.ker, ∃ i, τ.δ * Real.exp (-(τ.q α / S.N)) ≤
      ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [h1, map_sum] at h
  refine (norm_sum_lt _ (mul_pos τ.δ_pos (Real.exp_pos _)) fun t => ?_).ne h
  rw [map_mul, norm_mul, map_sum]
  simp only [map_mul]
  exact (mul_le_mul_of_nonneg_right (hint _) (norm_nonneg _)).trans_lt (by simpa using h0 t t.2 k.1)

theorem E_eq_bdd [ArithBase o Ω] (φ : o →+* OO p) (hφ : ∀ a, (φ a : PadicAlgCl p) = y₀ (algebraMap o S.R a))
    (hev : ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n =
      algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i)
    (hirr : ∀ (c : S.perp τ.yy.ker →+ ZMod S.N) (W : Submodule (kb p) (S.J → kb p)),
      (∀ v ∈ W, ((S.proj _ c).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v = v) →
      (∀ h ∈ S.perp (S.perp τ.yy.ker), ∀ v ∈ W,
        ((S.ρ h).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v ∈ W) →
      W = ⊥ ∨ ∀ v, ((S.proj _ c).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v = v → v ∈ W) :
    τ.E = bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le := by
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => hφ a ▸ (mem_OO_iff _).1 (φ a).2
  have : IsDomain o := (ArithBase.inj (o := o) (Ω := Ω)).isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hpp := TestBasis.perp_perp S τ.yy.ker
  have hTH : S.perp τ.yy.ker ≤ τ.yy.ker := τ.isoFree.1.trans hpp.le
  refine le_antisymm (Submodule.span_le.2 ?_) fun e he => ?_
  · rintro _ ⟨α, l, i, hα, hl, rfl⟩ a ha
    have h1 := τ.le α hα a ha i
    simp only [dotProduct, _root_.mul_assoc, ← Finset.mul_sum, norm_mul]
    refine (mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, _root_.mul_one]
  have hst := bdd_stable y₀ φ hφ hev τ.yy.ker τ.δ τ.δ_pos.le
  let ψ : o →+* PadicAlgCl p := (OO p).subtype.comp φ
  have he' : e = ∑ c : S.perp τ.yy.ker →+ ZMod S.N, (ψ.mapMatrix (S.proj _ c)).mulVec e := by
    rw [← Matrix.sum_mulVec, ← map_sum, hsum, map_one, Matrix.one_mulVec]
  rw [he']
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨α, hα, rfl⟩ := (test_weights o Ω S p y₀ τ).1 c
  have hPP : S.proj _ (τ.wt α) * S.proj _ (τ.wt α) = S.proj _ (τ.wt α) := by rw [hmul, if_pos rfl]
  have hfix : (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec ((ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e) =
      (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e := by
    rw [Matrix.mulVec_mulVec, ← map_mul, hPP]
  have hv : (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e ∈ bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le :=
    proj_stable φ _ _ _ (fun t ht => hst t (hTH ht)) e he
  generalize (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e = v at hfix hv
  obtain ⟨t, ht, i₁, hi₁⟩ := exists_le_norm τ hint hα
  have key := norm_mul_le_of_irreducible (φ.mapMatrix (S.proj _ (τ.wt α))) (by rw [← map_mul, hPP])
    (S.perp (S.perp τ.yy.ker) : Set S.Gam) (fun h => φ.mapMatrix (S.ρ h))
    (fun h hh => by rw [← map_mul, ← map_mul, proj_mul_comm _ _ h hh]) (hirr _)
    (bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le) (fun h hh => hst h (hpp.le hh))
    (fun j => y₀ ⟨S.ev t j, S.ev_mem t j⟩) τ.δ (τ.δ * Real.exp (-(τ.q α / S.N)))
    (mul_pos τ.δ_pos (Real.exp_pos _)) (fun e he => he t (hTH ht))
    (fun i => by simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ] using τ.le α hα t (hTH ht) i) i₁
    (by simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ] using hi₁) v hv hfix
  have hv' : v = ∑ i, fun j => v i * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
    funext j
    rw [Finset.sum_apply, ← congrFun hfix j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hφ, _root_.mul_comm]
    rfl
  rw [hv']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨α, v i, i, hα, ?_, rfl⟩
  have h1 := key i
  rw [mul_left_comm, mul_le_iff_le_one_right τ.δ_pos, Real.exp_neg, ← div_eq_mul_inv,
    div_le_one (Real.exp_pos _)] at h1
  exact h1

end System

end GlobalTheory.ZH.TestSpan
