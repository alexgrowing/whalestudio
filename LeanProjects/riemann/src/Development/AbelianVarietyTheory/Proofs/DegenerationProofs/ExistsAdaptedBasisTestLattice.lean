import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.TestBasis

open FreeNear

theorem exists_eStd_eq_linear (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
  · by_contra hxH
    let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
    obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
      (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
    obtain ⟨b, hb⟩ := exists_eStd_eq_linear _ _ (f ∘ₗ H'.mkQ)
    have hb' : b ∈ S.perp H := fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
    have h1 : eStd S.g _ x b = 0 := hx b hb'
    rw [Weights.eStd_swap, neg_eq_zero, hb] at h1
    exact hf h1
  · rw [Weights.eStd_swap, hy x hx, neg_zero]

variable {S} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem exists_nsmul_of_wt_eq_zero [ArithBase o Ω] (α : τ.X) (h : τ.wt α = 0) : ∃ v, α = S.N • v := by
  choose w hw using fun x => QuotientAddGroup.mk_surjective (τ.yy x)
  have h1 := ((test_weights o Ω S p y₀ τ).2 _ τ.isoFree le_rfl w (fun x => (hw x).symm) τ.yy.ker
    (by rw [perp_perp, AddSubgroup.closure_eq]) α).1 (fun t h₂ _ => by rw [h]; rfl)
  have h2 : AddSubgroup.closure (w '' τ.yy.ker ∪ Set.range fun v₀ : τ.X => S.N • v₀) ≤
      (nsmulAddMonoidHom S.N : τ.X →+ τ.X).range := by
    rw [AddSubgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | ⟨v, rfl⟩)
    · have h3 := hw x
      rw [AddMonoidHom.mem_ker.1 hx, QuotientAddGroup.eq_zero_iff] at h3
      obtain ⟨u, hu⟩ := h3
      exact ⟨S.r • u, by rw [← hu]; exact (mul_nsmul u S.r S.N).symm⟩
    · exact ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := h2 h1
  exact ⟨v, hv.symm⟩

theorem q_le_of_wt_eq [ArithBase o Ω] {α β : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀))
    (h : τ.wt β = τ.wt α) : τ.q α ≤ τ.q β := by
  obtain ⟨v, hv⟩ := exists_nsmul_of_wt_eq_zero τ (β - α) (by rw [map_sub, h, sub_self])
  have := hα v
  rwa [← hv, add_sub_cancel] at this

theorem exists_norm_eq_exp {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ l : PadicAlgCl p, ‖l‖ = Real.exp (τ.q α / S.N) := by
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  obtain ⟨x, hx⟩ := τ.δ_max.1
  refine ⟨y₀ ⟨S.th x, S.th_mem x⟩ / y₀ ⟨_, hk⟩, ?_⟩
  have hx' : ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = τ.δ := hx
  rw [norm_div, hx', h, Real.exp_neg]
  have := τ.δ_pos.ne'
  have := (Real.exp_pos (τ.q α / S.N)).ne'
  field_simp

theorem exists_proj_ne_zero {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ j i, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) ≠ 0 := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [h1] at h
  simp only [map_sum, map_mul, h0, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

end GlobalTheory.ZH.TestBasis

namespace GlobalTheory.ZH

open FreeNear TestBasis in

theorem exists_adapted_basis_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (B : Matrix S.J S.J (PadicAlgCl p)) (l : S.J → PadicAlgCl p) (α : S.J → τ.X), (∀ i j, ‖B i j‖ ≤ 1) ∧ ‖B.det‖ = 1 ∧ (∀ i v₀, τ.q (α i) ≤ τ.q (α i + S.N • v₀)) ∧ (∀ i, ‖l i‖ = Real.exp (τ.q (α i) / S.N)) ∧ (∀ c, ∃ i, τ.wt (α i) = c) ∧ (∀ i, ((S.proj _ (τ.wt (α i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (B i) = B i) ∧ τ.E = Submodule.span (OO p) (Set.range fun i j => l i * B i j) := by
  intro o Ω _ _ _ hA S p _ y₀ τ hint
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := proj_orthogonal S _ τ.isoFree
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (OO p) S.J
    (S.perp τ.yy.ker →+ ZMod S.N) (fun c => φ.mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  choose a ha hwa using (test_weights o Ω S p y₀ τ).1
  choose f hf using fun c => exists_norm_eq_exp τ (ha c)
  refine ⟨Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i))), fun i => f (κ i),
    fun i => a (κ i), fun i j => hint _, ?_, fun i => ha _, fun i => hf _, fun c => ?_, fun i => ?_, ?_⟩
  · have h1 : (((Matrix.of fun i j => φ.mapMatrix (S.proj _ (κ i)) j (col i)).det : OO p) : PadicAlgCl p) =
        (Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))).det :=
      RingHom.map_det (OO p).subtype _
    rw [← h1]
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hdet)
  · by_contra! h
    obtain ⟨j, i, hji⟩ := exists_proj_ne_zero τ (ha c)
    rw [hwa] at hji
    have h1 := (hspan c).le (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : {v : S.J → OO p | ∃ i, κ i = c ∧ v = fun j => φ.mapMatrix (S.proj _ c) j (col i)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨i, hi, _⟩ => h i ((hwa _).trans hi)
    rw [h2, Submodule.span_empty, Submodule.mem_bot] at h1
    exact hji (congrArg Subtype.val (congrFun h1 j))
  · rw [hwa]
    funext j
    have h1 := congrArg (fun a => y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul (κ i) (κ i)) j) (col i))
    simp only [if_true, Matrix.mul_apply, map_sum, map_mul] at h1
    exact h1
  · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨α, l, i, hα, hl, rfl⟩
      generalize hc : τ.wt α = c
      have h1 : ∀ w ∈ Submodule.span (OO p) {v : S.J → OO p | ∃ i, κ i = c ∧
          v = fun j => φ.mapMatrix (S.proj _ c) j (col i)},
          (fun j => f c * (w j : PadicAlgCl p)) ∈ Submodule.span (OO p) (Set.range fun i j =>
            f (κ i) * y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem _ h' =>
          obtain ⟨i', rfl, rfl⟩ := h'
          exact Submodule.subset_span ⟨i', rfl⟩
        | zero =>
          have : (fun j => f c * (((0 : S.J → OO p) j : OO p) : PadicAlgCl p)) = 0 := funext fun j => by simp
          rw [this]
          exact Submodule.zero_mem _
        | add a a' _ _ ha ha' =>
          convert Submodule.add_mem _ ha ha' using 1
          funext j
          simp [mul_add]
        | smul s a _ ha =>
          convert Submodule.smul_mem _ s ha using 1
          funext j
          change f c * ((s : PadicAlgCl p) * a j) = (s : PadicAlgCl p) * (f c * a j)
          ring
      have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
      have hpos : 0 < ‖f c‖ := hf c ▸ Real.exp_pos _
      have h0 : f c ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / f c ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hf]
        refine hl.trans (Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)))
        exact q_le_of_wt_eq τ hα ((hwa c).trans hc.symm)
      have h3 : (fun j => l * y₀ (algebraMap o S.R (S.proj _ c j i))) =
          (⟨_, hq⟩ : OO p) • fun j => f c * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
        funext j
        change _ = l / f c * (f c * y₀ (algebraMap o S.R (S.proj _ c j i)))
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [h3]
      exact Submodule.smul_mem _ _ h2
    · rintro _ ⟨i, rfl⟩
      exact ⟨a (κ i), f (κ i), col i, ha _, (hf _).le, by rw [hwa]; rfl⟩

end GlobalTheory.ZH
