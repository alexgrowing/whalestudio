import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationEqConjNilpotentIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationRelIndexEqResidueCardPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumDiagPairsToNatEqWeightedSumStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem filt_zero (ϖ : kˣ) (x : Fin n → ℤ) : filt ϖ x 0 = nO k n := by
  have h : ∀ g : GL (Fin n) k, Deep ϖ x 0 g := fun g i j hij hd => by
    have := Fin.lt_def.1 hij; omega
  ext g
  exact ⟨fun hg => hg.1, fun hg => ⟨hg, h _, h _⟩⟩

theorem filt_succ_le (ϖ : kˣ) (x : Fin n → ℤ) (d : ℕ) : filt ϖ x (d + 1) ≤ filt ϖ x d :=
  fun _ hg => ⟨hg.1, fun i j hij hd => hg.2.1 i j hij (by omega), fun i j hij hd => hg.2.2 i j hij (by omega)⟩

theorem relIndex_filt_zero {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    (filt ϖ x d).relIndex (nO k n) =
      Nat.card 𝓀[k] ^ ∑ e ∈ Finset.range d, ∑ p ∈ diagPairs n e, (x p.1 - x p.2).toNat := by
  induction d with
  | zero => rw [filt_zero]; simp
  | succ d ih =>
    have hle : ∀ e, filt ϖ x e ≤ nO k n := fun e _ hg => hg.1
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (filt_succ_le ϖ x d) (hle d), ih, GlobalTheory.T.filtration_relIndex_eq_residue_card_pow k n ϖ h1 x hx d,
      Finset.sum_range_succ, pow_add, mul_comm]

theorem mk_fiber {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {m m' : GL (Fin n) k}
    (hm : m ∈ nO k n) (hm' : m' ∈ nO k n) :
    (QuotientGroup.mk (m * tor ϖ x) : GL (Fin n) k ⧸ iwahori k (Fin n)) = QuotientGroup.mk (m' * tor ϖ x) ↔
      m⁻¹ * m' ∈ filt ϖ x n := by
  have hnorm : (tor ϖ x)⁻¹ ∈ Subgroup.normalizer ((unipB k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
    inv_mem ((GlobalTheory.CompanionTheory.IwahoriDatumGL.iwahoriCass k n).norm_N _ ⟨_, rfl⟩)
  have e : (m * tor ϖ x)⁻¹ * (m' * tor ϖ x) = (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ := by group
  rw [QuotientGroup.eq, e, GlobalTheory.T.filtration_eq_conj_nilpotent_integral k n ϖ h1 x hx]
  have hy : m⁻¹ * m' ∈ nO k n := mul_mem (inv_mem hm) hm'
  constructor
  · intro h
    refine ⟨_, ⟨h, (Subgroup.mem_normalizer_iff.1 hnorm _).1 hy.2⟩, ?_⟩
    simp [MulAut.conj_apply]
    group
  · rintro ⟨z, hz, e'⟩
    have : (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ = z := by
      rw [← e']
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hz.1

theorem jacHk : JacHk := by
  intro k _ _ _ _ n V _ _ π _ ϖ h1 x hx u hu
  have hfix : ∀ b ∈ iwahori k (Fin n), π b u = u := fun b hb => GlobalTheory.IwahoriInj.mem_fixed.1 hu b hb
  set I := iwahori k (Fin n) with hI
  set t : GL (Fin n) k := tor ϖ x with ht
  set w : Jacquet π (unipB k (Fin n)) := Submodule.Quotient.mk (π t u) with hw
  let F : nO k n → GL (Fin n) k ⧸ I := fun m => QuotientGroup.mk (m.1 * t)
  have hval : ∀ m ∈ nO k n, ∀ b ∈ I, (Submodule.Quotient.mk (π (m * t * b) u) : Jacquet π (unipB k (Fin n))) = w := by
    intro m hm b hb
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix b hb, hw, Submodule.Quotient.eq]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hm.2 _
  let f : GL (Fin n) k → ℂ := fun g => if ∃ a ∈ I, ∃ b ∈ I, g = a * t * b then (1 : ℂ) else 0

  have hsupp : ∀ q : GL (Fin n) k ⧸ I, (∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b) ↔ q ∈ Set.range F := by
    intro q
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      obtain ⟨m, hm, c, hc, e2⟩ := GlobalTheory.T.iwahori_double_coset_torus_nilpotent k n ϖ h1 x hx a ha b hb
      rw [← ht] at e2
      refine ⟨⟨m, hm⟩, ?_⟩
      rw [← QuotientGroup.out_eq' q, e, e2]
      refine QuotientGroup.eq.2 ?_
      simpa [mul_assoc] using inv_mem hc
    · rintro ⟨m, rfl⟩
      have : (F m).out⁻¹ * (m.1 * t) ∈ I := QuotientGroup.eq.1 (QuotientGroup.out_eq' (F m))
      refine ⟨m.1, m.2.1, (m.1 * t)⁻¹ * (F m).out, ?_, by group⟩
      simpa using inv_mem this

  have hcard : Nat.card (Set.range F) = (filt ϖ x n).relIndex (nO k n) := by
    let Φ : (nO k n ⧸ (filt ϖ x n).subgroupOf (nO k n)) → Set.range F := fun c =>
      Quotient.liftOn' c (fun m => (⟨F m, m, rfl⟩ : Set.range F)) (fun a b hab => Subtype.ext
        ((mk_fiber h1 hx a.2 b.2).2 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab))))
    have hΦ : Function.Bijective Φ := by
      constructor
      · intro c c'
        refine Quotient.inductionOn₂' c c' fun a b e => ?_
        exact Quotient.sound' (QuotientGroup.leftRel_apply.2 (Subgroup.mem_subgroupOf.2
          ((mk_fiber h1 hx a.2 b.2).1 (congrArg Subtype.val e))))
      · rintro ⟨_, m, rfl⟩
        exact ⟨Quotient.mk'' m, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  have hq : Nat.card 𝓀[k] ≠ 0 := Nat.card_pos.ne'
  have hcard' := hcard.trans (relIndex_filt_zero h1 hx n)
  have hQ : (Set.range F).Finite := by
    have : Finite (Set.range F) := Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ hq)
    exact Set.toFinite _
  have hs : (Function.support fun q : GL (Fin n) k ⧸ I => f q.out • π q.out u).Finite := by
    refine hQ.subset fun q hq' => (hsupp q).1 ?_
    by_contra h
    exact hq' (by simp only [f, if_neg h, zero_smul])
  have e2 : ∀ q : GL (Fin n) k ⧸ I, (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom (f q.out • π q.out u) =
      if q ∈ Set.range F then w else 0 := by
    intro q
    by_cases h : q ∈ Set.range F
    · obtain ⟨m, hm⟩ := id h
      have hb : (m.1 * t)⁻¹ * q.out ∈ I :=
        QuotientGroup.eq.1 ((show (QuotientGroup.mk (m.1 * t) : GL (Fin n) k ⧸ I) = q from hm).trans
          (QuotientGroup.out_eq' q).symm)
      have e : m.1 * t * ((m.1 * t)⁻¹ * q.out) = q.out := by group
      have hp : ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := ⟨m.1, m.2.1, _, hb, e.symm⟩
      have := hval m.1 m.2 _ hb
      rw [e] at this
      simp only [f, if_pos hp, if_pos h, one_smul]
      exact this
    · have : ¬ ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := fun h' => h ((hsupp q).1 h')
      simp only [f, if_neg this, if_neg h, zero_smul, map_zero]
  have e1 : (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) =
      ∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0 := by
    rw [← finsum_congr e2]
    exact AddMonoidHom.map_finsum (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom hs
  have e3 : (∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0) = Nat.card (Set.range F) • w := by
    rw [finsum_eq_sum_of_support_subset (s := hQ.toFinset) _ (fun q hq' => by
      simp only [Set.Finite.coe_toFinset]
      by_contra h
      exact hq' (by simp only [if_neg h]))]
    rw [Finset.sum_congr rfl (fun q hq' => if_pos (hQ.mem_toFinset.1 hq')), Finset.sum_const,
      Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hQ]
  change (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) = _
  rw [e1, e3, hcard', ← GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum n x hx, zpow_natCast, ← Nat.cast_pow, jacBU_mk, Nat.cast_smul_eq_nsmul ℂ]
  rfl

end GlobalTheory.CompanionTheory.IwJac

end
