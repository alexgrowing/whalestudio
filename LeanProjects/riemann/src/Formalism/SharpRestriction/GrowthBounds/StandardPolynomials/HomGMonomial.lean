import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsS
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXRen
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SgKSPowP

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.ColF

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2 Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

theorem md_single {ι : Type} [DecidableEq ι] {n : ℕ} (l' l : ι) (b : Fin n) (e : ℕ) :
    multideg (Finsupp.single (l', b) e) l = if l' = l then e else 0 := by
  classical
  unfold multideg
  by_cases h : l' = l
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      rw [Finsupp.single_apply, if_neg (fun hh => hc (congrArg Prod.snd hh).symm)]
    · intro hh; exact absurd (Finset.mem_univ b) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg (fun hh => h (congrArg Prod.fst hh))]

theorem phi_single {σ : Type} (φ : (σ →₀ ℕ) →+ ℕ) (v : σ) (e : ℕ) :
    φ (Finsupp.single v e) = e * φ (Finsupp.single v 1) := by
  have : Finsupp.single v e = e • Finsupp.single v 1 := by rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [this, map_nsmul, smul_eq_mul]

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} {β : GlobalTheory X} (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

theorem sum_lam_le (h2 : 2 ≤ numSeg X.TT) (d : Fin (2 * segS X.TT j + 1 + 1) → ℕ) (Q : ℕ) (hd : ∀ t, d t ≤ Q)
    (l : X.TT × Bool) : (∑ t, if lamS X j t = l then d t else 0) ≤ Q := by
  classical
  by_cases hl : ∃ t0, lamS X j t0 = l
  · obtain ⟨t0, rfl⟩ := hl
    rw [Finset.sum_eq_single t0]
    · rw [if_pos rfl]; exact hd t0
    · intro b _ hb
      rw [if_neg (fun hh => hb (lamS_injective X j h2 hh))]
    · intro hh; exact absurd (Finset.mem_univ t0) hh
  · rw [Finset.sum_eq_zero fun t _ => if_neg (fun hh => hl ⟨t, hh⟩)]
    exact Nat.zero_le _

theorem dgS_le (hp : 0 < X.p) (hG : segG X.TT j ≤ X.G') (c : ℤ) (t : Fin (2 * segS X.TT j + 1 + 1)) :
    dgS X.p (posS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (2 * segS X.TT j + 1 + 1) (zS X j) t ≤ X.p ^ X.G' := by
  unfold dgS
  split_ifs
  · exact lev_le X j hp hG t
  · exact Nat.zero_le _

theorem colDgQ (hp : 0 < X.p) (h2 : 2 ≤ numSeg X.TT) (hG : segG X.TT j ≤ X.G') (c : ℤ) (l : X.TT × Bool) :
    dgCS C0 CE1 CE2 mu X β j ka c l ≤ X.p ^ X.G' :=
  sum_lam_le j h2 _ _ (fun t => dgS_le j ka hp hG c t) l

theorem colDgY (c : ℤ) (j' : Fin (numSeg X.TT)) : dgCS C0 CE1 CE2 mu X β j ka c (topEnd X j', false) = 0 :=
  Finset.sum_eq_zero fun t _ => if_neg (lamS_ne_endFalse X j t j')

theorem phi_plS (φ : MonH X →+ ℕ) (c : ℤ) :
    φ (plS C0 CE1 CE2 mu X β j c) = ∑ t : Fin (2 * segS X.TT j + 1 + 1),
      if nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1) then
        PS X j t * φ (Finsupp.single (phiS X j (t, Fin.castAdd X.m 0)) 1) else 0 := by
  unfold plS
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact phi_single φ _ _
  · exact map_zero φ

theorem md_plS (c : ℤ) (l : X.TT × Bool) :
    multideg (plS C0 CE1 CE2 mu X β j c) l = ∑ t : Fin (2 * segS X.TT j + 1 + 1),
      if nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1) then
        (if lamS X j t = l then PS X j t else 0) else 0 := by
  have := phi_plS (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) j (mdHom X l) c
  refine Eq.trans this (Finset.sum_congr rfl fun t _ => ?_)
  have e : (mdHom X l) (Finsupp.single (phiS X j (t, Fin.castAdd X.m 0)) 1) = if lamS X j t = l then 1 else 0 :=
    md_single (lamS X j t) l _ 1
  rw [e]
  split_ifs <;> simp

theorem colPlQ (hp : 0 < X.p) (h2 : 2 ≤ numSeg X.TT) (hG : segG X.TT j ≤ X.G') (c : ℤ) (l : X.TT × Bool) :
    multideg (plS C0 CE1 CE2 mu X β j c) l ≤ X.p ^ X.G' := by
  rw [md_plS]
  refine le_trans (Finset.sum_le_sum fun t _ => ?_) (sum_lam_le j h2 (PS X j) _ (fun t => lev_le X j hp hG t) l)
  split_ifs <;> simp

end

section

variable {O : Type} [CommRing O] [IsDomain O] {N n : ℕ}

theorem colKInt (ka : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (J : Finset (Fin n)) :
    Kcol (KK O) ka c N J ∈ IntPol O (Fin N × Fin n) :=
  ⟨Kcol O ka c N J, Formalism.MainNotions.G.Joints.StandardMonomialSpace.lift_Kcol_map (algebraMap O (KK O)) ka c N J⟩

def mdG (N n : ℕ) (i : Fin N) : (Fin N × Fin n →₀ ℕ) →+ ℕ where
  toFun := fun m => multideg m i
  map_zero' := by simp [multideg]
  map_add' := fun a b => multideg_add a b i

theorem homG_monomial {σ R : Type} [CommRing R] (φ : (σ →₀ ℕ) →+ ℕ) (M : σ →₀ ℕ) (a : R) :
    HomG φ (φ M) (monomial M a : MvPolynomial σ R) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem kcol_pol {R : Type} [CommRing R] (ka : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (J : Finset (Fin n)) :
    Kcol R ka c N J ∈ Pol R n (fun i : Fin N => if colH (ka i.castSucc) c = colH (ka i.succ) c then 0 else 1) := by
  classical
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro m hm i
  rw [Kcol_eq_KG R ka c N le_rfl] at hm
  have hx : ∀ a b, HomG (mdG N n i) (if a = i.val then 1 else 0) (xOf R N n a b) := by
    intro a b
    unfold xOf
    by_cases h1 : a < N
    · rw [dif_pos h1]
      have e : (if a = i.val then 1 else 0) = mdG N n i (Finsupp.single ((⟨a, h1⟩ : Fin N), b) 1) := by
        show _ = multideg (Finsupp.single ((⟨a, h1⟩ : Fin N), b) 1) i
        rw [md_single]
        simp [Fin.ext_iff]
      rw [e]
      exact homG_monomial _ _ _
    · rw [dif_neg h1]; exact HomG.zero _ _
  have key : multideg m i = _ :=
    KG_hom (mdG N n i) c (hsOf ka c) (xOf R N n) (fun a => if a = i.val then 1 else 0) hx N J m (Finset.mem_coe.1 hm)
  rw [key, Finset.sum_eq_single i.val]
  · rw [hsOf_eq ka c i.val (by have := i.2; omega), hsOf_eq ka c (i.val + 1) (by have := i.2; omega), if_pos rfl]
    rfl
  · intro b _ hb
    rw [if_neg hb]; simp
  · intro hh; exact absurd (Finset.mem_range.2 i.2) hh

end

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O]
  {β : GlobalTheory X} (j : Fin (numSeg X.TT)) (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

theorem colKPol (c : ℤ) (J : Finset (Fin X.m)) :
    Kcol (KK O) ka c (2 * segS X.TT j + 1) J ∈ Pol (KK O) X.m (dKS X j ka c) := kcol_pol ka c J

theorem colFPol (h2 : 2 ≤ numSeg X.TT) (I'' : ℤ → Finset (Fin X.m)) (c : ℤ) :
    fCS C0 CE1 CE2 mu X β j ka O I'' c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgCS C0 CE1 CE2 mu X β j ka c) := by
  classical
  have hF : KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
      (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)) ∈ Pol (KK O) (1 + X.m)
        (dgS X.p (posS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (2 * segS X.TT j + 1 + 1) (zS X j)) := by
    rw [KKc_eq]
    unfold Pol
    rw [mem_restrictSupport_iff]
    intro m hm
    exact ZZ_HomD X.p (letG X.p X.n' (O := O) (LLseg X j) 1) (LLseg X j).pos _ c (posS_mono X j)
      (letG_HomD X.p X.n' (LLseg X j) 1) (2 * segS X.TT j + 1 + 1) le_rfl (zS X j) (fun i _ _ => position_le_segment_end X j i) _ m
      (Finset.mem_coe.1 hm)
  have := mem_Pol_rename (lamS X j) (lamS_injective X j h2) (Nat.add_comm 1 X.m) _ _ hF
  have this' := mem_Pol_iffW.1 this
  refine mem_Pol_iffW.2 fun l m hm => ?_
  refine (this' l m hm).trans ?_
  unfold dgCS
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> rfl

end

end Formalism.MainNotions.ColumnSystems.Pf.ColF
