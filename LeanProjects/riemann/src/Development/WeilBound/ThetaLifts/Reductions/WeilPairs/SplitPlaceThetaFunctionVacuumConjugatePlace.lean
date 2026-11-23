import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilOrthogonalFiniteCover
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace PositivityTheory.ThKW.SplitVacuumEigenvectors

theorem exists_eigen_of_sep {Y V : Type} [AddCommGroup Y] [AddCommGroup V] [Module ℂ V]
    (ρ : Y → V →ₗ[ℂ] V) (hρ : ∀ a b w, ρ (a + b) w = ρ a (ρ b w))
    (Q : AddSubgroup Y) [Finite (Y ⧸ Q)] (v : V) (hv : v ≠ 0) (hQ : ∀ q ∈ Q, ρ q v = v)
    (X : Set (Y → ℂ)) (hmul : ∀ χ ∈ X, ∀ a b, χ (a + b) = χ a * χ b) (hQχ : ∀ χ ∈ X, ∀ q ∈ Q, χ q = 1)
    (hclos : ∀ χ ∈ X, ∀ χ' ∈ X, χ * χ' ∈ X) (hone : (1 : Y → ℂ) ∈ X)
    (hsep : ∀ y, y ∉ Q → ∃ χ ∈ X, χ y ≠ 1) :
    ∃ χ ∈ X, ∃ w ∈ Submodule.span ℂ (Set.range fun y => ρ y v), w ≠ 0 ∧ ∀ y, χ y • ρ y w = w := by
  classical
  haveI : Fintype (Y ⧸ Q) := Fintype.ofFinite _
  let wf : (Y → ℂ) → V := fun χ => ∑ a : Y ⧸ Q, χ (Quotient.out a) • ρ (Quotient.out a) v
  have hout : ∀ a : Y ⧸ Q, ((Quotient.out a : Y) : Y ⧸ Q) = a := fun a => QuotientAddGroup.out_eq' a

  have heig : ∀ χ ∈ X, ∀ y, χ y • ρ y (wf χ) = wf χ := by
    intro χ hχ y
    have h0 : χ 0 = 1 := hQχ χ hχ 0 Q.zero_mem
    have hterm : ∀ a : Y ⧸ Q, χ (Quotient.out a) • ρ y (ρ (Quotient.out a) v) =
        χ (-y) • (χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v) := by
      intro a
      set b := (y : Y ⧸ Q) + a
      have hq : -(Quotient.out b) + (y + Quotient.out a) ∈ Q := by
        rw [← QuotientAddGroup.eq, hout, QuotientAddGroup.mk_add, hout]
      set q := -(Quotient.out b) + (y + Quotient.out a) with hqdef
      have e1 : y + Quotient.out a = Quotient.out b + q := by rw [hqdef]; abel
      have e2 : Quotient.out a = -y + (Quotient.out b + q) := by rw [← e1]; abel
      rw [← hρ, e1, hρ, hQ q hq, smul_smul, e2, hmul χ hχ, hmul χ hχ, hQχ χ hχ q hq, mul_one]
    calc χ y • ρ y (wf χ) = χ y • ∑ a : Y ⧸ Q, χ (Quotient.out a) • ρ y (ρ (Quotient.out a) v) := by
          simp only [wf, map_sum, map_smul]
      _ = χ y • ∑ a : Y ⧸ Q, χ (-y) • (χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v) := by
          simp only [hterm]
      _ = (χ y * χ (-y)) • ∑ a : Y ⧸ Q, χ (Quotient.out ((y : Y ⧸ Q) + a)) • ρ (Quotient.out ((y : Y ⧸ Q) + a)) v := by
          rw [← Finset.smul_sum, smul_smul]
      _ = wf χ := by
          rw [← hmul χ hχ, add_neg_cancel, h0, one_smul]
          exact Fintype.sum_equiv (Equiv.addLeft (y : Y ⧸ Q)) _ _ (fun _ => rfl)

  have hne : ∃ χ ∈ X, wf χ ≠ 0 := by
    by_contra hc
    push_neg at hc
    let Φ : (Y → ℂ) →ₗ[ℂ] V := ∑ a : Y ⧸ Q, (LinearMap.proj (Quotient.out a) : (Y → ℂ) →ₗ[ℂ] ℂ).smulRight (ρ (Quotient.out a) v)
    have hΦ : ∀ h, Φ h = wf h := fun h => by simp [Φ, wf]
    let M := Submodule.span ℂ X
    have hker : M ≤ LinearMap.ker Φ := Submodule.span_le.2 fun χ hχ => by
      show Φ χ = 0
      rw [hΦ]; exact hc χ hχ
    have hMM : ∀ f ∈ M, ∀ g ∈ M, f * g ∈ M := by
      intro f hf g hg
      have h1 : f * g ∈ M * M := Submodule.mul_mem_mul hf hg
      rw [Submodule.span_mul_span] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hclos a ha b hb
    have hsep' : ∀ a : Y ⧸ Q, a ≠ 0 → ∃ χ ∈ X, χ (Quotient.out a) ≠ 1 := by
      intro a ha
      refine hsep _ fun hm => ha ?_
      rw [← hout a]
      exact (QuotientAddGroup.eq_zero_iff _).2 hm
    choose! χa hχa hχne using hsep'
    let fac : Y ⧸ Q → (Y → ℂ) := fun a =>
      (1 - χa a (Quotient.out a))⁻¹ • (χa a - χa a (Quotient.out a) • (1 : Y → ℂ))
    let p : Y → ℂ := ∏ a ∈ Finset.univ.filter (fun a : Y ⧸ Q => a ≠ 0), fac a
    have hpM : p ∈ M := by
      refine Finset.prod_induction _ (· ∈ M) (fun f g hf hg => hMM f hf g hg) (Submodule.subset_span hone) ?_
      intro a ha
      have ha' := (Finset.mem_filter.1 ha).2
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (hχa a ha'))
        (Submodule.smul_mem _ _ (Submodule.subset_span hone)))
    have hp0 : ∀ a : Y ⧸ Q, a ≠ 0 → p (Quotient.out a) = 0 := by
      intro a ha
      simp only [p, Finset.prod_apply]
      refine Finset.prod_eq_zero (i := a) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩) ?_
      simp [fac]
    have hp1 : p (Quotient.out (0 : Y ⧸ Q)) = 1 := by
      have hq0 : Quotient.out (0 : Y ⧸ Q) ∈ Q := (QuotientAddGroup.eq_zero_iff _).1 (hout 0)
      simp only [p, Finset.prod_apply]
      refine Finset.prod_eq_one fun a ha => ?_
      have ha' := (Finset.mem_filter.1 ha).2
      have h1 : 1 - χa a (Quotient.out a) ≠ 0 := sub_ne_zero.2 (Ne.symm (hχne a ha'))
      simp only [fac, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one, hQχ _ (hχa a ha') _ hq0]
      exact inv_mul_cancel₀ h1
    have hΦp : Φ p = v := by
      rw [hΦ]
      simp only [wf]
      rw [Finset.sum_eq_single (0 : Y ⧸ Q) (fun a _ ha => by rw [hp0 a ha, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
        hp1, one_smul]
      exact hQ _ ((QuotientAddGroup.eq_zero_iff _).1 (hout 0))
    exact hv (by rw [← hΦp]; exact hker hpM)
  obtain ⟨χ, hχ, hw⟩ := hne
  refine ⟨χ, hχ, wf χ, Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩), hw,
    heig χ hχ⟩

end PositivityTheory.ThKW.SplitVacuumEigenvectors

end

noncomputable section

namespace PositivityTheory.ThKW.SplitVacuumEigenvectors

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

theorem heisOF_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    {f : WOF F E nS nT → ℂ} (hf : heisOF σ JS JT xi0 ψ x f = f) (n : ℕ) : heisOF σ JS JT xi0 ψ (n • x) f = f := by
  induction n with
  | zero => rw [zero_smul, heisOF_zero]
  | succ n ih => rw [succ_nsmul, heisOF_add_half he (nsmul_mem hx n) hx, hf, ih]

end PositivityTheory.ThKW.SplitVacuumEigenvectors

end

noncomputable section

namespace PositivityTheory.ThKW.SplitVacuumEigenvectors

open GlobalTheory.SplitInvFormF

theorem exists_vac_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  classical
  have he' := isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := PositivityTheory.ThKW.exists_finite_lattice_cover_open F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => mem_conjHalf_conj he (hGX g hg)

  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun {a b} ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ := fun q hq =>
    hUf _ (hGU _ q.2.1 hq) (fin_of_mem he q.2.1)

  have hN : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT ξ₀ B.ψ (k • g) f₀ = f₀ := fun g hg => exists_nsmul_fix he' (hGX' g hg) hf₀
  choose! Ng hNg0 hNg using hN
  set N := ∏ g ∈ G, Ng g with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := by
    intro g hg y
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m

  haveI : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK), ?_⟩) ?_
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN0]
      exact hpowN g g.2 _
    · intro a b hab
      rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
      intro g hg
      have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
      simp only at h1
      show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
      rw [AddSubgroup.coe_add, commF_add_right, ← h1, AddSubgroup.coe_neg, commF_neg_right]

  let Ch : Set (YK → ℂ) := {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧ χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT))
    (fun a b f => heisOF_add_half he a.2.1 b.2.1 f) Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y
      simp only [Pi.mul_apply, commF_add_left])
    ⟨0, X.zero_mem, fun q _ => commF_zero_left _, by funext y; simp only [Pi.one_apply, commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push_neg at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)

  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    exact GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) = heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hwθ : IsThetaFunOF σ JS JT ξ₀ B.ψ w := hspan_theta hwspan
  refine ⟨heisOF σ JS JT ξ₀ B.ψ (-x) w, GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ _ _ hwθ, ?_, ?_⟩
  · intro h0
    apply hw0
    have := heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  · intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have hyy : y ∈ YK := ⟨hy, hyK⟩
      have h1 := hweig ⟨y, hyy⟩
      change commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w at h1
      rw [heisOF_comm, commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push_neg at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, commF_half he' hk (X.neg_mem hxX), one_smul]
      congr 1
      exact hspan_fix k hk hkf hwspan

end PositivityTheory.ThKW.SplitVacuumEigenvectors

end
