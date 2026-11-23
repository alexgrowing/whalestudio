import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

open NumberField IsDedekindDomain in
open Polynomial Matrix in
private theorem eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero {K : Type} [Field K] [CharZero K]
    {a : ℕ} (B : Subalgebra K (Matrix (Fin a) (Fin a) K)) {z : Matrix (Fin a) (Fin a) K}
    (hzB : z ∈ B) (htr : ∀ y ∈ B, (z * y).trace = 0) {v : Fin a → K} (hv : z *ᵥ v = v) :
    v = 0 := by
  classical
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd z.charpoly
    (Matrix.charpoly_monic z).ne_zero 0
  set m := z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hpq hq
  have hc : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  set c := q.coeff 0 with hcdef
  set R := aeval z q.divX with hR
  have hq' : aeval z q = z * R + c • 1 := by
    calc aeval z q = aeval z (X * q.divX + C (q.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
      _ = z * R + c • 1 := by
        rw [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h0 : z ^ m * (z * R + c • 1) = 0 := by
    have := Matrix.aeval_self_charpoly z
    rwa [hpq, map_mul, map_pow, aeval_X, hq'] at this
  have hRz : z * R = R * z := by
    have := congrArg (aeval z) (mul_comm X q.divX)
    simpa [R] using this
  have h1 : z ^ (m + 1) * R = -(c • z ^ m) := by
    rw [pow_succ, mul_assoc]
    rw [mul_add, mul_smul_comm, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : z ^ m = z ^ (m + 1) * ((-c⁻¹) • R) := by
    rw [mul_smul_comm, h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, one_smul,
      neg_neg]
  set u := (-c⁻¹) • R with hu
  have hcomm : Commute z u := (show Commute z R from hRz).smul_right _
  have hstep : ∀ i, z ^ (m + i) = z ^ (m + i + 1) * u := by
    intro i
    rw [pow_add z m i, hkey, mul_assoc, ← (hcomm.pow_left i).eq, ← mul_assoc, ← pow_add,
      show m + 1 + i = m + i + 1 by omega]
  have hpow : ∀ k, z ^ (m + 1) = z ^ (m + 1 + k) * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, show m + 1 + k = m + (k + 1) by omega, hstep (k + 1), mul_assoc, ← pow_succ',
        show m + (k + 1) + 1 = m + 1 + (k + 1) by omega]
  have hRB : R ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hzB) (Polynomial.aeval_mem_adjoin_singleton K z)
  have huB : u ∈ B := B.smul_mem hRB _
  set n := m + 1 with hn
  have hnn := hpow n
  have hc' : u ^ n * z ^ n = z ^ n * u ^ n := (hcomm.pow_pow n n).eq.symm
  have he : IsIdempotentElem (z ^ n * u ^ n) := by
    show z ^ n * u ^ n * (z ^ n * u ^ n) = z ^ n * u ^ n
    rw [mul_assoc, ← mul_assoc (u ^ n) (z ^ n) (u ^ n), hc', ← mul_assoc, ← mul_assoc, ← pow_add,
      ← hnn]
  have hez : z ^ n * u ^ n * z ^ n = z ^ n := by
    rw [mul_assoc, hc', ← mul_assoc, ← pow_add, ← hnn]
  have htre : (z ^ n * u ^ n).trace = 0 := by
    have : z ^ n * u ^ n = z * (z ^ m * u ^ n) := by
      show z ^ (m + 1) * u ^ n = _
      rw [pow_succ', mul_assoc]
    rw [this]
    exact htr _ (B.mul_mem (B.pow_mem hzB m) (B.pow_mem huB n))
  have he0 : z ^ n * u ^ n = 0 := by
    have h1 : IsIdempotentElem (Matrix.toLin' (z ^ n * u ^ n)) := by
      unfold IsIdempotentElem at he ⊢
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    have h2 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h1).1
      (by rw [Matrix.trace_toLin'_eq, htre])
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hzn : z ^ n = 0 := by rw [← hez, he0, zero_mul]
  have hvn : ∀ k, (z ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  rw [← hvn n, hzn, Matrix.zero_mulVec]

open NumberField IsDedekindDomain in
open Polynomial Matrix in

theorem _root_.GlobalTheory.isSSRep_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), _root_.Formalism.MainNotions.N.IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K _ _ _ a ρ hss x hx htrx
  classical
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hss
  set P : Γ → Matrix (Fin a) (Fin a) K :=
    fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) with hP
  have hPmul : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [hP, map_mul]
  have hP1 : P 1 = 1 := by simp [hP]
  have hgen : ∀ g, P g ∈ Submodule.span K (Set.range P) := fun g => Submodule.subset_span ⟨g, rfl⟩
  have hleft : ∀ g, ∀ y ∈ Submodule.span K (Set.range P),
      P g * y ∈ Submodule.span K (Set.range P) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨h, rfl⟩ := hy; rw [← hPmul]; exact hgen _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hAmul : ∀ y ∈ Submodule.span K (Set.range P), ∀ w ∈ Submodule.span K (Set.range P),
      y * w ∈ Submodule.span K (Set.range P) := by
    intro y hy w hw
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hleft g w hw
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add y t _ _ hy ht => rw [add_mul]; exact Submodule.add_mem _ hy ht
    | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let B : Subalgebra K (Matrix (Fin a) (Fin a) K) :=
    { carrier := Submodule.span K (Set.range P)
      mul_mem' := fun hy hw => hAmul _ hy _ hw
      add_mem' := fun hy hw => Submodule.add_mem _ hy hw
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, ← hP1]
        exact Submodule.smul_mem _ c (hgen 1) }
  let J : Matrix (Fin a) (Fin a) K → Prop :=
    fun z => z ∈ Submodule.span K (Set.range P) ∧ ∀ g, (z * P g).trace = 0
  have hJtr : ∀ z, J z → ∀ y ∈ B, (z * y).trace = 0 := by
    intro z hz y hy
    have hy' : y ∈ Submodule.span K (Set.range P) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hg => obtain ⟨g, rfl⟩ := hg; exact hz.2 g
    | zero => simp
    | add y w _ _ h1 h2 => rw [mul_add, Matrix.trace_add, h1, h2, add_zero]
    | smul c y _ h => rw [mul_smul_comm, Matrix.trace_smul, h, smul_zero]
  have hJleft : ∀ g z, J z → J (P g * z) := by
    intro g z hz
    refine ⟨hleft g z hz.1, fun h => ?_⟩
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, ← hPmul]
    exact hz.2 _
  have hJright : ∀ g z, J z → J (z * P g) := by
    intro g z hz
    refine ⟨hAmul _ hz.1 _ (hgen g), fun h => ?_⟩
    rw [mul_assoc, ← hPmul]
    exact hz.2 _
  have hJ0 : J 0 := ⟨Submodule.zero_mem _, fun g => by simp⟩
  have hJadd : ∀ y z, J y → J z → J (y + z) := fun y z hy hz =>
    ⟨Submodule.add_mem _ hy.1 hz.1, fun g => by rw [add_mul, Matrix.trace_add, hy.2, hz.2, add_zero]⟩
  have hJsmul : ∀ (c : K) z, J z → J (c • z) := fun c z hz =>
    ⟨Submodule.smul_mem _ c hz.1, fun g => by rw [smul_mul_assoc, Matrix.trace_smul, hz.2, smul_zero]⟩
  have hfix : ∀ z, J z → ∀ v, z *ᵥ v = v → v = 0 := fun z hz v hv =>
    eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero B hz.1 (hJtr z hz) hv
  have hpres : ∀ S : Submodule K (Fin a → K), _root_.Formalism.MainNotions.N.IsInv ρ S →
      ∀ y ∈ Submodule.span K (Set.range P), ∀ s ∈ S, y *ᵥ s ∈ S := by
    intro S hS y hy s hs
    unfold _root_.Formalism.MainNotions.N.IsInv at hS
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hS g s hs
    | zero => rw [Matrix.zero_mulVec]; exact S.zero_mem
    | add y w _ _ h1 h2 => rw [Matrix.add_mulVec]; exact S.add_mem h1 h2
    | smul c y _ h => rw [Matrix.smul_mulVec]; exact S.smul_mem c h
  let W : Submodule K (Fin a → K) :=
    { carrier := {v | ∀ z, J z → z *ᵥ v = 0}
      add_mem' := fun {v w} hv hw z hz => by rw [Matrix.mulVec_add, hv z hz, hw z hz, add_zero]
      zero_mem' := fun z _ => Matrix.mulVec_zero z
      smul_mem' := fun c v hv z hz => by rw [Matrix.mulVec_smul, hv z hz, smul_zero] }
  have hWst : _root_.Formalism.MainNotions.N.IsInv ρ W := by
    unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    have hv' : ∀ z, J z → z *ᵥ v = 0 := hv
    show ∀ z, J z → z *ᵥ (P g *ᵥ v) = 0
    intro z hz
    rw [Matrix.mulVec_mulVec]
    exact hv' _ (hJright g z hz)
  obtain ⟨W', hW'st, hcompl⟩ := hss W hWst
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨S, ⟨hSst, hSW', hSne⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {S : Submodule K (Fin a → K) | _root_.Formalism.MainNotions.N.IsInv ρ S ∧ S ≤ W' ∧ S ≠ ⊥} ⟨W', hW'st, le_rfl, hne⟩
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
    let T : Submodule K (Fin a → K) :=
      { carrier := {w | ∃ z, J z ∧ z *ᵥ s = w}
        add_mem' := by
          rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, hJadd y z hy hz, Matrix.add_mulVec _ _ _⟩
        zero_mem' := ⟨0, hJ0, Matrix.zero_mulVec _⟩
        smul_mem' := by
          rintro c _ ⟨z, hz, rfl⟩
          exact ⟨c • z, hJsmul c z hz, Matrix.smul_mulVec _ _ _⟩ }
    have hTS : T ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact hpres S hSst z hz.1 s hsS
    have hTst : _root_.Formalism.MainNotions.N.IsInv ρ T := by
      unfold _root_.Formalism.MainNotions.N.IsInv
      rintro g _ ⟨z, hz, rfl⟩
      exact ⟨P g * z, hJleft g z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩
    by_cases hT : T = ⊥
    · apply hs0
      have hsW : s ∈ W := by
        show ∀ z, J z → z *ᵥ s = 0
        intro z hz
        have hzT : z *ᵥ s ∈ T := ⟨z, hz, rfl⟩
        rw [hT] at hzT
        exact (Submodule.mem_bot K).1 hzT
      exact (Submodule.disjoint_def.1 hcompl.disjoint) s hsW (hSW' hsS)
    · have hTeq : T = S := by
        by_contra hTS'
        exact hmin T ⟨hTst, hTS.trans hSW', hT⟩ (lt_of_le_of_ne hTS hTS')
      have hsT : s ∈ T := hTeq ▸ hsS
      obtain ⟨z, hz, hzs⟩ := hsT
      exact hs0 (hfix z hz s hzs)
  have hWtop : W = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hW'bot, sup_bot_eq] at h
  have hxJ : J x := ⟨hx, htrx⟩
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [Matrix.zero_mulVec]
  have hv : ∀ z, J z → z *ᵥ v = 0 := (hWtop ▸ Submodule.mem_top : v ∈ W)
  exact hv x hxJ

end GlobalTheory
