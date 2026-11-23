import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace CEqGen

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq RowTiePCEqSum ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def SumAt (V : VF C) (X : RawChart C d I κ) : Prop :=
  ∀ (g : Fin 2) (H : X.CartHyp V g) (S : Sys (RawChart.cart H))
    (t : I g → MvPowerSeries (I g) C), S.IsT t →
    ∃ Φ : κ → MvPowerSeries (I g) C, (∀ i, MvPowerSeries.constantCoeff (Φ i) = 0) ∧ (∀ i, IntS V (Φ i)) ∧
      (∀ i, MvPowerSeries.subst t (Φ i) = X.expG g i) ∧
      ∀ q : JJ I g, ∃ Λ : MvPowerSeries (I g) C, IntS V Λ ∧
        MvPowerSeries.subst (X.expG g) (X.sg (X.u (1 - g) q)) =
          S.ze t q + MvPowerSeries.subst t Λ + ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) • (MvPowerSeries.X c : MvPowerSeries (I g) C) else 0

def DerAt (V : VF C) (X : RawChart C d I κ) : Prop :=
  ∀ (g : Fin 2) (k : I (1 - g)), ∃ J : MvPowerSeries (Fin 2 × κ) C, IntS V J ∧
    dVar (⟨1 - g, k⟩ : WV I) X.hRow =
      (X.k : C) • (MvPowerSeries.subst (fun q : Fin 2 × κ => X.expPt q.1 q.2) J -
        MvPowerSeries.subst (X.expPt g) (X.sg (X.u (1 - g) k)))

def IsCvK (V : VF C) {τ : Type} (γ : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 ∧ IntS V (γ i)

def AddM (V : VF C) (X : RawChart C d I κ) : Prop :=
  ∀ (τ : Type) [Finite τ] (γ γ' : κ → MvPowerSeries τ C), IsCvK V γ → IsCvK V γ' →
    ∃ γ'' : κ → MvPowerSeries τ C, IsCvK V γ'' ∧
      (∀ i, MvPowerSeries.subst γ'' (X.lg i) = MvPowerSeries.subst γ (X.lg i) + MvPowerSeries.subst γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        IntS V (MvPowerSeries.subst γ'' (X.sg v) - MvPowerSeries.subst γ (X.sg v) - MvPowerSeries.subst γ' (X.sg v))

theorem cEq_of {V : VF C} (X : RawChart C d I κ) (H : ∀ g, X.CartHyp V g) (hS : SumAt V X) (hD : DerAt V X) :
    RawChart.CEqSt H := by
  intro _ g a a' hodd S t ht k hk
  have ht0 : ∀ g' c, MvPowerSeries.constantCoeff (t g' c) = 0 := fun g' => (ht g').1
  have hT := MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht0)
  have hne : a ≠ a' := by
    intro h
    subst h
    rw [sub_self, ZMod.val_zero] at hodd
    have := Nat.odd_iff.mp hodd
    omega
  have hSg := fun g' => hS g' (H g') (S g') (t g') (ht g')
  choose Φ hΦ0 hΦI hΦt hΛ using hSg
  obtain ⟨Λ, hΛI, hσ⟩ := hΛ g k
  obtain ⟨J, hJI, hder⟩ := hD g k
  set Φ' : Fin 2 × κ → MvPowerSeries (WV I) C := fun q => upG q.1 (Φ q.1 q.2) with hΦ'
  have hΦ'0 : ∀ q, MvPowerSeries.constantCoeff (Φ' q) = 0 := fun q => upG_const _ (hΦ0 q.1 q.2)
  have hΦ'I : ∀ q, IntS V (Φ' q) := fun q => intS_upG _ (hΦI q.1 q.2)
  have hΨ : (fun q : Fin 2 × κ => X.expPt q.1 q.2) = fun q => MvPowerSeries.subst (tW t) (Φ' q) := by
    funext q
    rw [expPt_eq, ← hΦt q.1 q.2, subst_tW_upG ht0]
  have hJ' : MvPowerSeries.subst (fun q : Fin 2 × κ => X.expPt q.1 q.2) J =
      MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J) := by
    rw [hΨ, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hΦ'0) hT]
  have hexG0 : ∀ i, MvPowerSeries.constantCoeff (X.expG g i) = 0 := fun i => by
    rw [← hΦt g i]
    exact constantCoeff_subst_zero (ht0 g) (hΦ0 g i)
  have hsg : MvPowerSeries.subst (X.expPt g) (X.sg (X.u (1 - g) k)) =
      upG g (MvPowerSeries.subst (X.expG g) (X.sg (X.u (1 - g) k))) := by
    rw [upG_subst g hexG0]
    congr 1
    funext i
    exact expPt_eq X g i
  set sig0 : MvPowerSeries (I g) C := ∑ c : I g, if X.ty g c = X.ty (1 - g) k then
    X.sg1 (X.u g c) (X.u (1 - g) k) • (MvPowerSeries.X c : MvPowerSeries (I g) C) else 0 with hsig0
  set L := toLeafL (fun g => RawChart.cart (H g)) g a a' with hL
  have hsig : L (upG g sig0) = 0 := by
    rw [hsig0, upG_eq, map_sum, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hc
    · rw [map_smul, map_smul, ← upG_eq, upG_X]
      have : L (MvPowerSeries.X (⟨g, c⟩ : WV I)) = 0 := by
        refine toLeaf_X_off _ g a a' _ ?_
        rintro (⟨-, h2⟩ | ⟨h1, -⟩)
        · exact hne (h2.symm.trans (hc.trans hk))
        · fin_cases g <;> simp at h1
      rw [this, smul_zero]
    · rw [map_zero, map_zero]
  refine ⟨MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)),
    ⟨(X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ), fun μ => ?_, rfl⟩, ?_⟩
  · have hI : IntS V ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)) := by
      intro ν
      rw [MvPowerSeries.coeff_smul, map_sub]
      exact (ge_natCast _).mul_int ((IntS.subst hΦ'0 hΦ'I hJI ν).sub (intS_upG g hΛI ν))
    exact hI μ
  · have hpair : (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) =
        (-(X.k : C)) • upG g ((S g).ze (t g) k) := by
      rw [Finset.sum_eq_single k]
      · simp [RawChart.pairK]
      · intro q _ hq
        simp [RawChart.pairK, hq]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have hw : X.OnLf g a a' (⟨1 - g, k⟩ : WV I) := Or.inr ⟨rfl, hk⟩
    rw [dVar_hLf X H g a a' _ hw, hpair, hder, hJ', hsg, hσ]
    have e1 : upG g ((S g).ze (t g) k + MvPowerSeries.subst (t g) Λ + sig0) =
        upG g ((S g).ze (t g) k) + MvPowerSeries.subst (tW t) (upG g Λ) + upG g sig0 := by
      rw [upG_eq, map_add, map_add, ← upG_eq, ← upG_eq, ← upG_eq, subst_tW_upG ht0]
    have e2 : MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)) =
        (X.k : C) • (MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J) -
          MvPowerSeries.subst (tW t) (upG g Λ)) := by
      rw [← MvPowerSeries.coe_substAlgHom hT, map_smul, map_sub]
    rw [e1, e2]
    show L _ - L _ = L _
    simp only [map_smul, map_sub, map_add, hsig]
    module

theorem sumCvK {V : VF C} (X : RawChart C d I κ) (hA : AddM V X)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hax : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    {τ : Type} [Finite τ] {ι : Type} (s : Finset ι) (γ : ι → κ → MvPowerSeries τ C)
    (hγ : ∀ c, IsCvK V (γ c)) :
    ∃ Γ : κ → MvPowerSeries τ C, IsCvK V Γ ∧
      (∀ i, MvPowerSeries.subst Γ (X.lg i) = ∑ c ∈ s, MvPowerSeries.subst (γ c) (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        IntS V (MvPowerSeries.subst Γ (X.sg v) - ∑ c ∈ s, MvPowerSeries.subst (γ c) (X.sg v)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => ⟨map_zero _, intS_zero⟩, fun i => ?_, fun v _ => ?_⟩
    · rw [Finset.sum_empty]
      exact subst_zero_const _ (hlg0 i)
    · rw [Finset.sum_empty, sub_zero, subst_zero_const _ (X.constantCoeff_sg hax v)]
      exact intS_zero
  | insert c s hc ih =>
    obtain ⟨Γ, hΓ, hL, hS⟩ := ih
    obtain ⟨Γ', hΓ', hL', hS'⟩ := hA τ Γ (γ c) hΓ (hγ c)
    refine ⟨Γ', hΓ', fun i => ?_, fun v hv => ?_⟩
    · rw [hL', hL, Finset.sum_insert hc]
      ring
    · rw [Finset.sum_insert hc]
      have := intS_add (hS' v hv) (hS v hv)
      convert this using 1
      ring

theorem sumAt_of {V : VF C} (X : RawChart C d I κ) (hA : AddM V X)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hax : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (huI : ∀ g c i, V.Ge 0 (X.u g c i)) : SumAt V X := by
  intro g H S t ht
  have hl2 : 2 ≤ V.l := V.l_prime.two_le
  have ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := ht.1
  have htS := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have hmem : ∀ c, ∃ γ : κ → PowerSeries C, ∃ lam : JJ I g → PowerSeries C, IsCv V γ ∧ IsCv V lam ∧
      (∀ i, alongCv γ (X.lg i) =
        ∑ c' : I g, X.u g c' i • tyS V.l (fun s => S.cur c s (Sum.inl c'))) ∧
      ∀ q : JJ I g, tyS V.l (fun s => S.cur c s (Sum.inr q)) =
        lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
          ∑ c' : I g, if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') (X.u (1 - g) q) •
              tyS V.l (fun s => S.cur c s (Sum.inl c')) else 0 :=
    fun c => by
      obtain ⟨h, -, -⟩ := S.curve c
      exact h
  choose γ lam hγ hlam h1 h2 using hmem
  have be0 : ∀ c (q : JJ I g), S.cur c 0 (Sum.inr q) = 0 := fun c q => by
    obtain ⟨-, h0, -⟩ := S.curve c
    rw [h0]
    rfl
  have hc : ∀ c (a : ℕ → C) (μ : I g →₀ ℕ),
      MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l a)) =
        ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)) :=
    fun c a μ => coeff_subst_tyS hl2 (ht0 c) a μ
  have hC : ∀ x : I g, ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl x))) =
      MvPowerSeries.X x := by
    intro x
    ext μ
    rw [map_sum, MvPowerSeries.coeff_X]
    simp only [hc]
    rw [Finset.sum_comm]
    exact ht.2 x μ
  have hB : ∀ q : JJ I g, ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inr q))) =
      -S.ze t q := by
    intro q
    ext μ
    rw [map_sum, map_neg]
    simp only [hc]
    rw [Finset.sum_comm]
    show _ = -(-(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c : I g, S.be c s q * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))))
    rw [neg_neg, show Finset.range (μ.degree + 1) = insert 0 (Finset.Icc 1 μ.degree) by ext s; simp; omega,
      Finset.sum_insert (by simp)]
    simp only [be0, zero_mul, Finset.sum_const_zero, zero_add]
    rfl
  set γt : I g → κ → MvPowerSeries (I g) C :=
    fun c i => MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (γ c i) with hγtd
  have hγt : ∀ c, IsCvK V (γt c) := fun c i =>
    ⟨constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hγ c i).1,
      IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (intS_ps.2 (hγ c i).2)⟩
  have key1 : ∀ c (f : MvPowerSeries (κ) C), MvPowerSeries.subst (γt c) f =
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (alongCv (γ c) f) := by
    intro c f
    unfold alongCv
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ c i).1)
      (hasSubst_unit (MvPowerSeries.constantCoeff_X c))]
  have key2 : ∀ c (F : PowerSeries C), MvPowerSeries.subst t
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) F) =
      MvPowerSeries.subst (fun _ : Unit => t c) F := by
    intro c F
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_unit (MvPowerSeries.constantCoeff_X c)) htS]
    congr 1
    funext _
    rw [MvPowerSeries.subst_X htS]
  have hlin : ∀ c (r : I g → C) (F : I g → PowerSeries C),
      MvPowerSeries.subst (fun _ : Unit => t c) (∑ c' : I g, r c' • F c') =
        ∑ c' : I g, r c' • MvPowerSeries.subst (fun _ : Unit => t c) (F c') :=
    fun c r F => subst_lin (hasSubst_unit (ht0 c)) _ r F
  obtain ⟨Γ, hΓ, hL, hSg⟩ := sumCvK X hA hlg0 hax Finset.univ γt hγt
  have hΓS := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hΓ i).1
  have hZ0 : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst t (Γ j)) = 0 := fun j =>
    constantCoeff_subst_zero ht0 (hΓ j).1
  have hZS := MvPowerSeries.hasSubst_of_constantCoeff_zero hZ0
  have hsum : ∀ f : MvPowerSeries (κ) C, MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j)) f =
      MvPowerSeries.subst t (MvPowerSeries.subst Γ f) := fun f =>
    (MvPowerSeries.subst_comp_subst_apply hΓS htS f).symm
  have hpush : ∀ f : MvPowerSeries (κ) C, MvPowerSeries.subst t (∑ c, MvPowerSeries.subst (γt c) f) =
      ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) f) := by
    intro f
    rw [← MvPowerSeries.coe_substAlgHom htS, map_sum, MvPowerSeries.coe_substAlgHom]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [key1, key2]
  have hlgZ : ∀ i, MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j)) (X.lg i) =
      ∑ c' : I g, X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
    intro i
    rw [hsum, hL i, hpush]
    simp only [h1, hlin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.smul_sum, hC c']
  have hZ : ∀ i, MvPowerSeries.subst t (Γ i) = X.expG g i := by
    intro i
    have e1 : MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j))
        (MvPowerSeries.subst X.lg (X.ex i)) = MvPowerSeries.subst t (Γ i) := by
      rw [hexlg i, MvPowerSeries.subst_X hZS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0) hZS]
    unfold RawChart.expG
    congr 1
    funext j
    exact hlgZ j
  refine ⟨Γ, fun i => (hΓ i).1, fun i => (hΓ i).2, hZ, fun q => ?_⟩
  set v := X.u (1 - g) q with hv
  have hvI : ∀ i, V.Ge 0 (v i) := fun i => huI (1 - g) q i
  refine ⟨(MvPowerSeries.subst Γ (X.sg v) - ∑ c, MvPowerSeries.subst (γt c) (X.sg v)) +
    ∑ c, MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (lam c q), ?_, ?_⟩
  · refine intS_add (hSg v hvI) (intS_sum _ fun c _ => ?_)
    exact IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (intS_ps.2 (hlam c q).2)
  · have hexp : X.expG g = fun j => MvPowerSeries.subst t (Γ j) := by
      funext j
      exact (hZ j).symm
    have hA : ∀ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) (X.sg v)) =
        MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) -
          MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inr q))) +
          ∑ c' : I g, if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') v •
              MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl c'))) else 0 := by
      intro c
      have e : alongCv (γ c) (X.sg v) = lam c q - tyS V.l (fun s => S.cur c s (Sum.inr q)) +
          ∑ c' : I g, if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') v • tyS V.l (fun s => S.cur c s (Sum.inl c')) else 0 := by
        rw [h2 c q]
        ring
      rw [e, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit (ht0 c)), map_add, map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      split_ifs
      · rw [map_smul]
      · rw [map_zero]
    have hAll : ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) (X.sg v)) =
        S.ze t q + ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) +
          ∑ c' : I g, if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') v • (MvPowerSeries.X c' : MvPowerSeries (I g) C) else 0 := by
      simp only [hA]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hB q, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      have hx : ∀ c' : I g, (∑ c : I g, if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') v •
              MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl c'))) else 0) =
          if X.ty g c' = X.ty (1 - g) q then
            X.sg1 (X.u g c') v • (MvPowerSeries.X c' : MvPowerSeries (I g) C) else 0 := by
        intro c'
        split_ifs
        · rw [← Finset.smul_sum, hC c']
        · exact Finset.sum_const_zero
      rw [Finset.sum_congr rfl fun c' _ => hx c']
      ring
    have hsplit : MvPowerSeries.subst t ((MvPowerSeries.subst Γ (X.sg v) -
        ∑ c, MvPowerSeries.subst (γt c) (X.sg v)) +
          ∑ c, MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (lam c q)) =
        MvPowerSeries.subst t (MvPowerSeries.subst Γ (X.sg v)) -
          ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) (X.sg v)) +
          ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) := by
      rw [← hpush, ← MvPowerSeries.coe_substAlgHom htS, map_add, map_sub, map_sum, map_sum]
      simp only [MvPowerSeries.coe_substAlgHom, key2]
    rw [hexp, hsum, hsplit, hAll]
    ring

end CEqGen
end Formalism.L2.FormalSeriesBounds
