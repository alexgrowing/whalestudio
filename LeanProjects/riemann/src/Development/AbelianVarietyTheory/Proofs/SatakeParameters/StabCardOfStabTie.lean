import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AmbientLatticeAvoidance
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecorationLiftStdLatticeReductionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGlReductionModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReductionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

noncomputable section

namespace GlobalTheory.KFormsCmp

theorem prod_union_sub {α M : Type} [DecidableEq α] [CommMonoid M] {s t : Finset α} (h : Disjoint s t)
    (F : ↥(s ∪ t) → M) :
    ∏ x, F x = (∏ a : s, F ⟨a.1, Finset.mem_union_left _ a.2⟩) * ∏ b : t, F ⟨b.1, Finset.mem_union_right _ b.2⟩ := by
  classical
  let G : α → M := fun x => if hx : x ∈ s ∪ t then F ⟨x, hx⟩ else 1
  have h0 : ∏ x, F x = ∏ x : ↥(s ∪ t), G x.1 := Finset.prod_congr rfl fun x _ => by simp only [G, dif_pos x.2]
  have h1 : (∏ a : s, F ⟨a.1, Finset.mem_union_left _ a.2⟩) = ∏ a : s, G a.1 :=
    Finset.prod_congr rfl fun x _ => by simp only [G, dif_pos (Finset.mem_union_left t x.2)]
  have h2 : (∏ a : t, F ⟨a.1, Finset.mem_union_right _ a.2⟩) = ∏ a : t, G a.1 :=
    Finset.prod_congr rfl fun x _ => by simp only [G, dif_pos (Finset.mem_union_right s x.2)]
  rw [h0, h1, h2, Finset.prod_coe_sort (s ∪ t) G, Finset.prod_coe_sort s G, Finset.prod_coe_sort t G,
    Finset.prod_union h]

section Cong

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

def congSub (M : AddSubgroup V) (c : E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {k | (∀ x, k x ∈ M ↔ x ∈ M) ∧ ∀ x ∈ M, c⁻¹ • (k x - x) ∈ M}
  one_mem' := ⟨fun _ => Iff.rfl, fun x _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨fun x => (ha.1 (b x)).trans (hb.1 x), fun x hx => by
    have e : c⁻¹ • ((a * b) x - x) = a (c⁻¹ • (b x - x)) + c⁻¹ • (a x - x) := by
      rw [map_smul, map_sub, ← smul_add]
      congr 1
      show a (b x) - x = _
      abel
    rw [e]
    exact add_mem ((ha.1 _).2 (hb.2 x hx)) (ha.2 x hx)⟩
  inv_mem' := fun {a} ha => ⟨fun x => by
      have := ha.1 (a⁻¹ x)
      rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
      exact this.symm, fun x hx => by
      have h1 : a⁻¹ x ∈ M := by
        have := ha.1 (a⁻¹ x)
        rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
        exact this.1 hx
      have h2 := ha.2 _ h1
      rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at h2
      have e : c⁻¹ • (a⁻¹ x - x) = -(c⁻¹ • (x - a⁻¹ x)) := by rw [← smul_neg, neg_sub]
      rw [e]
      exact neg_mem h2⟩

theorem congSub_conj {M : AddSubgroup V} {c : E} {g k : V ≃ₗ[E] V} (hg : ∀ x, g x ∈ M ↔ x ∈ M)
    (hk : k ∈ congSub M c) : g * k * g⁻¹ ∈ congSub M c := by
  have hg' : ∀ x, g⁻¹ x ∈ M ↔ x ∈ M := fun x => by
    have := hg (g⁻¹ x)
    rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at this
    exact this.symm
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · show g (k (g⁻¹ x)) ∈ M ↔ _
    rw [hg, hk.1, hg']
  · have e : c⁻¹ • ((g * k * g⁻¹) x - x) = g (c⁻¹ • (k (g⁻¹ x) - g⁻¹ x)) := by
      rw [map_smul, map_sub, show g (g⁻¹ x) = x from g.apply_symm_apply x]
      rfl
    rw [e, hg]
    exact hk.2 _ ((hg' x).2 hx)

end Cong

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem mem_std (x : Sp E n) : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

omit [StarRing E] in
theorem intAt_neg {a : E} (h : IntAt P a) : IntAt P (-a) := by
  have := (IntAt.coe P (-1)).mul h
  simpa using this

omit [StarRing E] in
theorem reduction_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a - b) = redP P a - redP P b := by
  have h := reduction_add (ha.add (intAt_neg hb)) hb
  rw [← sub_eq_add_neg, sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

omit [StarRing E] in
theorem qOf_ne (P : HeightOneSpectrum (𝓞 E)) : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

omit [StarRing E] in
theorem qOf_mem (P : HeightOneSpectrum (𝓞 E)) : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _

omit [StarRing E] in
theorem reduction_absNorm_mul_eq_zero {a : E} (ha : IntAt P a) : redP P ((qOf P : E) * a) = 0 := by
  have h := reduction_mul (IntAt.coe P ((qOf P : ℕ) : 𝓞 E)) ha
  rw [reduction_coe, Ideal.Quotient.eq_zero_iff_mem.2 (qOf_mem P), zero_mul] at h
  simpa using h

theorem cong_iff (hq : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))) (k : Sp E n ≃ₗ[E] Sp E n) :
    k ∈ congSub (stdAt E n P).toAddSubgroup (qOf P : E) ↔
      k ∈ GLint E n P ∧ ∀ x ∈ stdAt E n P, redV P (k x) = redV P x := by
  have hq0 : (qOf P : E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_ne P)
  refine and_congr_right fun hk => forall₂_congr fun x hx => ?_
  have hx' : x ∈ stdAt E n P := hx
  have hkx : k x ∈ stdAt E n P := (hk x).2 hx
  show _ ∈ stdAt E n P ↔ _
  rw [mem_std] at hx' hkx ⊢
  constructor
  · intro h
    funext i
    have h1 := reduction_absNorm_mul_eq_zero (h i)
    rw [Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hq0, Pi.sub_apply, reduction_sub (hkx i) (hx' i)] at h1
    exact sub_eq_zero.1 h1
  · intro h i
    have h1 : redP P (k x i - x i) = 0 := by
      rw [reduction_sub (hkx i) (hx' i)]
      exact sub_eq_zero.2 (congrFun h i)
    have := hq _ (by rw [sub_eq_add_neg]; exact (hkx i).add (intAt_neg (hx' i))) h1
    rwa [div_eq_inv_mul] at this

theorem lamY_zero (q : ℕ) (ex : ℕ → ℕ) (x : Sp E (n + 0)) : x ∈ LocE.lamY P q n 0 ex ↔ x ∈ stdAt E (n + 0) P := by
  have e : (LinearMap.pi fun l : Fin (n + 0) => ((q : E) ^ LocE.scE n ex l.1)⁻¹ • (LinearMap.proj l : Sp E (n + 0) →ₗ[E] E)) x = x := by
    funext l
    have : l.1 < n := l.2
    simp [LocE.scE, this]
  show (LinearMap.pi fun l : Fin (n + 0) => ((q : E) ^ LocE.scE n ex l.1)⁻¹ • (LinearMap.proj l : Sp E (n + 0) →ₗ[E] E)) x ∈ stdAt E (n + 0) P ↔ _
  rw [e]

end Red

section Primes

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_of_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

theorem g_mem_of_vGs (hP : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ∃ k, (Pr.g k : 𝓞 X.E) ∈ w.asIdeal := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, hP.g_mem h⟩
  · exact ⟨1, hP.g_mem h⟩

theorem disj (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (hg : ∀ k, Pr.g k ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hQ : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := fun hw => by
  obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
  exact notMem_of_QE hs mu hQ (hP.g_prime k) (hg k) hk

theorem pi_notMem (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (P : rowSG Pr sel mu) : Pr.piT u ∉ P.1.asIdeal := by
  classical
  intro h
  have hT' : (Pr.T u : 𝓞 X.E) ∈ P.1.asIdeal := by
    rw [← hP.piT_norm u]
    exact Ideal.mul_mem_right _ _ h
  rcases Finset.mem_union.1 P.2 with hw | hw
  · obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
    have hc : Nat.Coprime (Pr.T u) (Pr.g k) := (Nat.coprime_primes (hP.T_prime u) (hP.g_prime k)).2 (hP.T_ne_g u k)
    have hc' : IsCoprime ((Pr.T u : ℕ) : 𝓞 X.E) ((Pr.g k : ℕ) : 𝓞 X.E) := Nat.Coprime.cast hc
    obtain ⟨a, b, hab⟩ := hc'
    exact one_notMem P.1 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hT') (Ideal.mul_mem_left _ _ hk))
  · exact notMem_of_QE hs mu hw (hP.T_prime u) hT hT'

end Primes

section Top

variable {E : Type} [Field E] {a n : ℕ}

theorem cpy_apply (a b : ℕ) (x : Sp E a) (l : Fin b) : cpy E a b x l = atNL E a l.1 x := rfl

theorem atNL_lt (x : Sp E n) {l : ℕ} (h : l < n) : atNL E n l x = x ⟨l, h⟩ := by simp [atNL, h]

theorem atNL_ge (x : Sp E n) {l : ℕ} (h : ¬ l < n) : atNL E n l x = 0 := by simp [atNL, h]

theorem cpy_cpy (hn : n = a + 1) (y : Sp E (a + 0)) : cpy E n (a + 0) (cpy E (a + 0) n y) = y := by
  funext l
  have h : l.1 < n := by have := l.2; omega
  rw [cpy_apply, atNL_lt _ h, cpy_apply, atNL_lt _ l.2]

theorem last_cpy (hn : n = a + 1) (y : Sp E (a + 0)) : atNL E n a (cpy E (a + 0) n y) = 0 := by
  rw [atNL_lt _ (by omega : a < n), cpy_apply, atNL_ge _ (by simp)]

theorem cpy_eN (hn : n = a + 1) : cpy E n (a + 0) (Loc.eN E n a) = 0 := by
  funext l
  have h0 := l.2
  have h : l.1 < n := by omega
  rw [cpy_apply, atNL_lt _ h]
  have : l.1 ≠ a := by omega
  simp [Loc.eN, this]

theorem last_eN (hn : n = a + 1) : atNL E n a (Loc.eN E n a) = 1 := by
  rw [atNL_lt _ (by omega : a < n)]
  simp [Loc.eN]

theorem ext_top (hn : n = a + 1) {x y : Sp E n} (h1 : cpy E n (a + 0) x = cpy E n (a + 0) y)
    (h2 : atNL E n a x = atNL E n a y) : x = y := by
  funext l
  by_cases h : l.1 < a
  · have := congrFun h1 ⟨l.1, h⟩
    rwa [cpy_apply, cpy_apply, atNL_lt _ l.2, atNL_lt _ l.2] at this
  · have hl : l = ⟨a, by omega⟩ := Fin.ext (by have := l.2; simp only; omega)
    rw [atNL_lt _ (by omega : a < n), atNL_lt _ (by omega : a < n)] at h2
    rw [hl]
    exact h2

theorem decomp (hn : n = a + 1) (x : Sp E n) :
    x = cpy E (a + 0) n (cpy E n (a + 0) x) + atNL E n a x • Loc.eN E n a := by
  apply ext_top hn
  · rw [map_add, map_smul, cpy_cpy hn, cpy_eN hn, smul_zero]
    exact (add_zero _).symm
  · rw [map_add, map_smul, last_cpy hn, last_eN hn, zero_add, smul_eq_mul, mul_one]

def Ext (a : ℕ) (jx : Sp E n ≃ₗ[E] Sp E n) (j : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)) : Prop :=
  (∀ x, cpy E n (a + 0) (jx x) = j (cpy E n (a + 0) x)) ∧ ∀ x, atNL E n a (jx x) = atNL E n a x

theorem ext_iff' (hn : n = a + 1) (jx : Sp E n ≃ₗ[E] Sp E n) (j : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)) :
    Ext a jx j ↔ (∀ y, jx (cpy E (a + 0) n y) = cpy E (a + 0) n (j y)) ∧ jx (Loc.eN E n a) = Loc.eN E n a := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y => ext_top hn ?_ ?_, ext_top hn ?_ (h2 _)⟩
    · rw [h1, cpy_cpy hn, cpy_cpy hn]
    · rw [h2, last_cpy hn, last_cpy hn]
    · rw [h1, cpy_eN hn, map_zero]
  · rintro ⟨h1, h2⟩
    have e : ∀ x, jx x = cpy E (a + 0) n (j (cpy E n (a + 0) x)) + atNL E n a x • Loc.eN E n a := fun x => by
      conv_lhs => rw [decomp hn x]
      rw [map_add, map_smul, h1, h2]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [e, map_add, map_smul, cpy_cpy hn, cpy_eN hn, smul_zero]
      exact add_zero _
    · rw [e, map_add, map_smul, last_cpy hn, last_eN hn, zero_add, smul_eq_mul, mul_one]

theorem Ext.one : Ext a (1 : Sp E n ≃ₗ[E] Sp E n) 1 := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Ext.mul {jx jx' : Sp E n ≃ₗ[E] Sp E n} {j j' : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)} (h : Ext a jx j)
    (h' : Ext a jx' j') : Ext a (jx * jx') (j * j') :=
  ⟨fun x => (h.1 (jx' x)).trans (congrArg j (h'.1 x)), fun x => (h.2 (jx' x)).trans (h'.2 x)⟩

theorem Ext.inv {jx : Sp E n ≃ₗ[E] Sp E n} {j : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)} (h : Ext a jx j) :
    Ext a jx⁻¹ j⁻¹ := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := h.1 (jx⁻¹ x)
    rw [show jx (jx⁻¹ x) = x from jx.apply_symm_apply x] at this
    rw [this]
    exact (j.symm_apply_apply _).symm
  · have := h.2 (jx⁻¹ x)
    rw [show jx (jx⁻¹ x) = x from jx.apply_symm_apply x] at this
    exact this.symm

theorem std_top [NumberField E] [StarRing E] (hn : n = a + 1) (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ cpy E n (a + 0) x ∈ stdAt E (a + 0) P ∧ IntAt P (atNL E n a x) := by
  rw [mem_std, mem_std, atNL_lt _ (by omega : a < n)]
  constructor
  · intro h
    refine ⟨fun l => ?_, h _⟩
    rw [cpy_apply, atNL_lt _ (by have := l.2; omega : l.1 < n)]
    exact h _
  · rintro ⟨h1, h2⟩ l
    by_cases h : l.1 < a
    · have := h1 ⟨l.1, h⟩
      rwa [cpy_apply, atNL_lt _ l.2] at this
    · have hl : l = ⟨a, by omega⟩ := Fin.ext (by have := l.2; simp only; omega)
      rw [hl]
      exact h2

end Top

section Levels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

structure Hyp : Prop where
  hX : T.X.Ok
  hP : T.Pr.Ok
  hs : IsSel T.X T.sel
  hg : ∀ k, T.Pr.g k ∈ T.S
  hT : T.Pr.T T.w ∈ T.S
  hL : T.L.Ok T.Ch T.sel T.xi T.cst T.G (D.R.m - 2)
  hTop : T.TopTie

theorem Nm (D : D7) : D.R.N D.R.m = (D.R.N D.R.m - 1) + 1 := N_m_succ D.R

open Classical in

def topM (i : ℕ) (P : T.SB) : AddSubgroup (Sp T.X.E (D.R.N i)) where
  carrier := {y | T.InTopLat i P y}
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, by rw [map_zero]; simpa using IntAt.coe P.1 0⟩
  add_mem' := fun hx hy => ⟨by rw [map_add]; exact add_mem hx.1 hy.1, by rw [map_add]; exact hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨by rw [map_neg]; exact neg_mem hx.1, by rw [map_neg]; exact intAt_neg hx.2⟩

open Classical in

def topK (i : ℕ) (P : T.SB) : Subgroup (T.AutX i) :=
  congSub (topM T i P) (((qOf P.1 : ℕ) : T.X.E) ^ (if P.1 ∈ T.Pr.vGs then 1 else T.depth P))

def LocB (i : ℕ) (b : Option (T.L.β i)) (P : T.SB) (κ : T.AutX i) (v : T.X.K) : Prop :=
  match b with
  | some al => ∃ r : AutY T.X D.R i, (r ∈ Loc.Cbe (Jat (Pr := T.Pr) T.cst.sharp i P.1) (T.L.h i al P) ∧
        ∀ x, r (Loc.inX T.X.E (D.R.N i) (cOf D.R i) x) = Loc.inX T.X.E (D.R.N i) (cOf D.R i) (κ x)) ∧
      v = chiInv T.Ch T.sel T.xi T.cst i P (T.L.h i al P) r
  | none => ∃ (j : T.XP ≃ₗ[T.X.E] T.XP) (jx k : T.AutX i),
      (j ∈ T.Jtop P ∧ (∀ x, jx (cpy T.X.E _ _ x) = cpy T.X.E _ _ (j x)) ∧
        jx (Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1)) = Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1) ∧
        T.InTopCong i P k ∧ κ = jx * k) ∧ v = T.lamM P j

theorem inLev_iff (i : ℕ) (b : Option (T.L.β i)) (κ : T.SB → T.AutX i) (a : ℂ) :
    T.InLev i b κ a ↔ ∃ v : T.SB → T.X.K, (∀ P, LocB T i b P (κ P) (v P)) ∧ a = (T.s.σ₀ (∏ P, v P))⁻¹ := by
  cases b with
  | some al =>
    constructor
    · rintro ⟨r, h, rfl⟩
      exact ⟨_, fun P => ⟨r P, h P, rfl⟩, rfl⟩
    · rintro ⟨v, h, rfl⟩
      choose r h1 h2 using h
      obtain rfl := funext h2
      exact ⟨r, h1, rfl⟩
  | none =>
    constructor
    · rintro ⟨j, jx, k, h, rfl⟩
      exact ⟨_, fun P => ⟨j P, jx P, k P, h P, rfl⟩, rfl⟩
    · rintro ⟨v, h, rfl⟩
      choose j jx k h1 h2 using h
      obtain rfl := funext h2
      exact ⟨j, jx, k, h1, rfl⟩

theorem locB_top (P : T.SB) (κ : T.AutX D.R.m) (v : T.X.K) :
    LocB T D.R.m none P κ v ↔ ∃ j ∈ T.Jtop P, ∃ jx : T.AutX D.R.m, ∃ k ∈ topK T D.R.m P,
      Ext (D.R.N D.R.m - 1) jx j ∧ κ = jx * k ∧ v = T.lamM P j := by
  constructor
  · rintro ⟨j, jx, k, ⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨j, h1, jx, k, h4, (ext_iff' (Nm D) jx j).2 ⟨h2, h3⟩, h5, h6⟩
  · rintro ⟨j, h1, jx, k, h4, h, h5, h6⟩
    obtain ⟨h2, h3⟩ := (ext_iff' (Nm D) jx j).1 h
    exact ⟨j, jx, k, ⟨h1, h2, h3, h4, h5⟩, h6⟩

variable {T}

theorem Hyp.stab (H : Hyp T) {P : T.SB} {j : T.XP ≃ₗ[T.X.E] T.XP} (hj : j ∈ T.Jtop P) {jx : T.AutX D.R.m}
    (h : Ext (D.R.N D.R.m - 1) jx j) (x : Sp T.X.E (D.R.N D.R.m)) : jx x ∈ topM T D.R.m P ↔ x ∈ topM T D.R.m P := by
  classical
  show T.InTopLat _ P _ ↔ T.InTopLat _ P _
  unfold ChainData.InTopLat
  rw [h.1, h.2]
  refine and_congr_left fun _ => ?_
  by_cases hw : P.1 ∈ T.Pr.vGs
  · rw [if_pos hw]
    unfold ChainData.Jtop at hj
    rw [if_pos hw] at hj
    split_ifs at hj
    · rw [← lamY_zero (qOf P.1) (fun i => i + 1), ← lamY_zero (qOf P.1) (fun i => i + 1)]
      exact (Subgroup.mem_inf.1 hj).1 _
    · rw [← lamY_zero (qOf P.1) (fun i => i + 1), ← lamY_zero (qOf P.1) (fun i => i + 1)]
      exact (Subgroup.mem_inf.1 hj).1 _
  · rw [if_neg hw]
    have h2 := (H.hTop P hw).2.1
    refine ⟨fun hx => ?_, h2 j hj _⟩
    have := h2 j⁻¹ (inv_mem hj) _ hx
    rwa [show j⁻¹ (j _) = _ from j.symm_apply_apply _] at this

theorem lamM_inv (P : T.SB) {j : T.XP ≃ₗ[T.X.E] T.XP} (hj : j ∈ T.Jtop P) : T.lamM P j * T.lamM P j⁻¹ = 1 := by
  classical
  have hr := rank_X'_eq D.R
  unfold ChainData.Jtop at hj
  unfold ChainData.lamM
  split_ifs at hj ⊢
  · refine GlobalTheory.T.lambda_char_sym_mul_inv_eq_one _ _ P.1 _ (qOf_ne _) (qOf_mem _) _ _ _ D.R.rS _ _ _ _ ?_ hr.ge j hj
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  · exact GlobalTheory.T.lambda_char_mul_inv_eq_one _ _ P.1 _ (qOf_ne _) (qOf_mem _) _ _ _ _ _ _ _ hr.ge j hj
  · exact GlobalTheory.T.lambda_quotient_char_mul_inv_eq_one _ _ P.1 _ (qOf_ne _) (qOf_mem _) _ _ _ j hj

theorem locB_one (i : ℕ) (b : Option (T.L.β i)) (P : T.SB) : ∃ v, LocB T i b P 1 v := by
  cases b with
  | some al => exact ⟨_, 1, ⟨one_mem _, fun _ => rfl⟩, rfl⟩
  | none => exact ⟨_, 1, 1, 1, ⟨one_mem _, fun _ => rfl, rfl, one_mem (topK T i P), rfl⟩, rfl⟩

theorem locB_some {i : ℕ} (al : T.L.β i) (P : T.SB) (κ : T.AutX i) :
    (∃ v, LocB T i (some al) P κ v) ↔ κ ∈ prCat (Pr := T.Pr) T.cst.sharp i P.1 (T.L.h i al P) :=
  ⟨fun ⟨_, r, h, _⟩ => ⟨r, h.1, h.2⟩, fun ⟨r, h1, h2⟩ => ⟨_, r, ⟨h1, h2⟩, rfl⟩⟩

theorem Hyp.locB_div (H : Hyp T) {i : ℕ} {b : Option (T.L.β i)} (hb : b = none → i = D.R.m) {P : T.SB}
    {κ κ' : T.AutX i} (h : ∃ v, LocB T i b P κ v) (h' : ∃ v, LocB T i b P κ' v) : ∃ v, LocB T i b P (κ⁻¹ * κ') v := by
  cases b with
  | some al =>
    rw [locB_some] at h h' ⊢
    exact mul_mem (inv_mem h) h'
  | none =>
    obtain rfl := hb rfl
    obtain ⟨v, h⟩ := h
    obtain ⟨v', h'⟩ := h'
    obtain ⟨j, hj, jx, k, hk, he, rfl, -⟩ := (locB_top T P κ v).1 h
    obtain ⟨j', hj', jx', k', hk', he', rfl, -⟩ := (locB_top T P κ' v').1 h'
    have hJ : (j⁻¹ * j')⁻¹ ∈ T.Jtop P := inv_mem (mul_mem (inv_mem hj) hj')
    have hE := (he.inv.mul he').inv
    refine ⟨_, (locB_top T P _ _).2 ⟨j⁻¹ * j', mul_mem (inv_mem hj) hj', jx⁻¹ * jx',
      (jx⁻¹ * jx')⁻¹ * k⁻¹ * ((jx⁻¹ * jx')⁻¹)⁻¹ * k', mul_mem (congSub_conj (H.stab hJ hE) (inv_mem hk)) hk',
      he.inv.mul he', by group, rfl⟩⟩

end Levels

section Points

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev APt (i : ℕ) : Type := AmbientLatticeAvoidance.Pt (R := D.R) T.sel T.xi T.L T.w i

abbrev inG (w : T.Pr.vGs) : T.SB := by classical exact ⟨w.1, Finset.mem_union_left _ w.2⟩

abbrev inQ (P : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) : T.SB := by classical exact ⟨P.1, Finset.mem_union_right _ P.2⟩

structure Over (i : ℕ) (a : APt T i) (p : T.Lab i) : Prop where
  idx : p.1 = a.2.1
  lat : p.2.1.deco.1.N = a.1.deco.1.N
  fT : p.2.1.deco.1.f = a.1.deco.1.f
  frG : ∀ w : T.Pr.vGs, ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, a.1.deco.1.be w (p.2.1.fr (inG T w) x) = redV w.1 x
  frQ : ∀ P, p.2.1.fr (inQ T P) = a.1.fr P
  cos : i + 1 = D.R.m → p.2.2 = a.2.2
  cos' : i + 1 ≠ D.R.m → a.2.2 = ∅ ∧ p.2.2 = Set.univ

theorem frsF_spec {i : ℕ} (a : ChPt (R := D.R) T.sel T.xi T.w i) (P : T.SB) (x : Sp T.X.E (D.R.N i)) :
    frsF T.sel T.xi a P x ∈ a.deco.1.at P.1 ↔ x ∈ stdAt T.X.E (D.R.N i) P.1 := by
  classical
  unfold frsF
  split_ifs with h
  · exact (GlobalTheory.T.decoration_lift_std_lattice_reduction _ _ _ _ a.deco ⟨P.1, h⟩).1 x
  · exact a.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

open Classical in

def up (i : ℕ) (a : APt T i) : T.Lab i :=
  (a.2.1, ⟨(a.1.deco.res (Finset.empty_subset _), frsF T.sel T.xi a.1), frsF_spec T a.1⟩,
    if i + 1 = D.R.m then a.2.2 else Set.univ)

variable {T}

theorem Hyp.disj (H : Hyp T) (P : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) : P.1 ∉ T.Pr.vGs :=
  KFormsCmp.disj H.hP H.hs T.xi H.hg P.2

theorem sb_cases (P : T.SB) : (∃ w, P = inG T w) ∨ ∃ Q, P = inQ T Q := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact Or.inl ⟨⟨P.1, h⟩, rfl⟩
  · exact Or.inr ⟨⟨P.1, h⟩, rfl⟩

theorem Hyp.over_up (H : Hyp T) {i : ℕ} (a : APt T i) (ha : i + 1 ≠ D.R.m → a.2.2 = ∅) : Over T i a (up T i a) where
  idx := rfl
  lat := rfl
  fT := rfl
  frG w x hx := by
    show a.1.deco.1.be w (frsF T.sel T.xi a.1 (inG T w) x) = _
    unfold frsF
    rw [dif_pos w.2]
    exact (GlobalTheory.T.decoration_lift_std_lattice_reduction _ _ _ _ a.1.deco w).2 x hx
  frQ P := by
    show frsF T.sel T.xi a.1 (inQ T P) = _
    unfold frsF
    rw [dif_neg (H.disj P)]
  cos h := if_pos h
  cos' h := ⟨ha h, if_neg h⟩

theorem exists_down {i : ℕ} (p : T.Lab i) (hp : i + 1 ≠ D.R.m → p.2.2 = Set.univ) : ∃ a, Over T i a p := by
  classical
  obtain ⟨d, h1, h2, h3⟩ := GlobalTheory.T.exists_decoration_extension_at_primes _ _ _ T.Pr.vGs p.2.1.deco (fun w => p.2.1.fr (inG T w))
    fun w x => p.2.1.2 (inG T w) x
  refine ⟨(⟨(d, fun P => p.2.1.fr (inQ T P)), fun P x => ?_⟩, p.1, if i + 1 = D.R.m then p.2.2 else ∅),
    rfl, h1.symm, h2.symm, h3, fun _ => rfl, fun h => (if_pos h).symm, fun h => ⟨if_neg h, hp h⟩⟩
  show _ ∈ localization₂ P.1.asIdeal d.1.N ↔ _
  rw [h1]
  exact p.2.1.2 (inQ T P) x

theorem fr_spec {i : ℕ} (p : T.Pt i) (P : T.SB) (x : Sp T.X.E (D.R.N i)) :
    p.fr P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt T.X.E (D.R.N i) P.1 := p.2 P x

theorem glint_of {i : ℕ} {p p' : T.Pt i} {γ : UF T.X.E (D.R.N i)} (hN : p'.deco.1.N = gmap γ.1 p.deco.1.N)
    {P : T.SB} {κ : T.AutX i} (h : p'.fr P = γ.1 * p.fr P * κ) : κ ∈ GLint T.X.E (D.R.N i) P.1 := by
  intro x
  rw [← fr_spec p P, ← fr_spec p' P x, hN, mem_localization_gmap, h]
  show _ ↔ γ.1.symm (γ.1 (p.fr P (κ x))) ∈ _
  rw [LinearEquiv.symm_apply_apply]

theorem act_iff {i : ℕ} {a a' : APt T i} {p p' : T.Lab i} (h : Over T i a p) (h' : Over T i a' p')
    (γ : UF T.X.E (D.R.N i)) (g : GLG T.X.E (D.R.N i) T.Pr.vGs)
    (c : GLQ T.X.E (D.R.N i) (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K))) (κ : T.SB → T.AutX i)
    (hκ : ∀ P, p'.2.1.fr P = γ.1 * p.2.1.fr P * κ P) :
    a'.1 = ((γ, g, c) : UF T.X.E (D.R.N i) × GLG T.X.E (D.R.N i) T.Pr.vGs ×
        GLQ T.X.E (D.R.N i) (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K))) • a.1 ↔
      p'.2.1.deco = (γ, (1 : GLG T.X.E (D.R.N i) ∅)) • p.2.1.deco ∧
      (∀ w : T.Pr.vGs, ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, redV w.1 x = (g w).1.mulVec (redV w.1 (κ (inG T w) x))) ∧
      ∀ P, κ (inQ T P) = ((c P)⁻¹).1 := by
  constructor
  · intro e
    have e1 : a'.1.deco.1 = a.1.deco.1.act γ.1 g := congrArg (fun q => (DecoF.deco q).1) e
    have e2 : ∀ P, a'.1.fr P = γ.1 * a.1.fr P * ((c P)⁻¹).1 := fun P => congrArg (fun q => DecoF.fr q P) e
    have hN : p'.2.1.deco.1.N = gmap γ.1 p.2.1.deco.1.N := by rw [h'.lat, h.lat, e1]; rfl
    refine ⟨Subtype.ext (Deco.ext hN ?_ ?_), fun w x hx => ?_, fun P => ?_⟩
    · rw [h'.fT, e1]
      show _ = fun P x => p.2.1.deco.1.f P (γ.1.symm x)
      rw [h.fT]
      rfl
    · funext w
      exact absurd w.2 (Finset.notMem_empty _)
    · rw [← h'.frG w x hx, e1, hκ]
      show (g w).1.mulVec (a.1.deco.1.be w (γ.1.symm (γ.1 (p.2.1.fr (inG T w) (κ (inG T w) x))))) = _
      rw [LinearEquiv.symm_apply_apply, h.frG w (κ (inG T w) x) ((glint_of hN (hκ (inG T w)) x).2 hx)]
    · have := hκ (inQ T P)
      rw [h'.frQ, h.frQ, e2] at this
      exact (mul_left_cancel this).symm
  · rintro ⟨e, hG, hQ⟩
    have hN : p'.2.1.deco.1.N = gmap γ.1 p.2.1.deco.1.N := by rw [e]; rfl
    have hN' : a'.1.deco.1.N = gmap γ.1 a.1.deco.1.N := by rw [← h'.lat, ← h.lat, hN]
    refine Subtype.ext (Prod.ext (Subtype.ext (Deco.ext hN' ?_ ?_)) ?_)
    · show a'.1.deco.1.f = fun P x => a.1.deco.1.f P (γ.1.symm x)
      rw [← h'.fT, ← h.fT, e]
      rfl
    · funext w y
      show a'.1.deco.1.be w y = (g w).1.mulVec (a.1.deco.1.be w (γ.1.symm y))
      by_cases hy : y ∈ a'.1.deco.1.at w.1
      · obtain ⟨x, rfl⟩ := (p'.2.1.fr (inG T w)).surjective y
        have hx : x ∈ stdAt T.X.E (D.R.N i) w.1 := by
          rw [← fr_spec p'.2.1 (inG T w) x, h'.lat]
          exact hy
        rw [h'.frG w x hx, hκ]
        show _ = (g w).1.mulVec (a.1.deco.1.be w (γ.1.symm (γ.1 (p.2.1.fr (inG T w) (κ (inG T w) x)))))
        rw [LinearEquiv.symm_apply_apply, h.frG w (κ (inG T w) x) ((glint_of hN (hκ (inG T w)) x).2 hx)]
        exact hG w x hx
      · rw [a'.1.deco.2.be_off w y hy, a.1.deco.2.be_off w _ fun hh => hy (by
          show y ∈ localization₂ w.1.asIdeal a'.1.deco.1.N
          rw [hN', mem_localization_gmap]
          exact hh), Matrix.mulVec_zero]
    · funext P
      show a'.1.fr P = γ.1 * a.1.fr P * ((c P)⁻¹).1
      rw [← h'.frQ, ← h.frQ, hκ, hQ]

end Points

section Moves

theorem piChar_val {K ι : Type} [Field K] [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ∀ i, G i) (hx : x ∈ Subgroup.pi Set.univ H) :
    ((piChar H lam ⟨x, hx⟩ : Kˣ) : K) = ∏ i, ((lam i ⟨x i, hx i (Set.mem_univ _)⟩ : Kˣ) : K) := by
  rw [piChar, MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)
  (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
  (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ)

def TopSame : Prop := ∀ P : T.SB, T.lamTop P = abelian₂ P.1 ∧ T.depth P = dep P.1

def LocG (i : ℕ) (b : Option (T.L.β i)) (w : T.Pr.vGs) (h : GL (Fin (D.R.N i)) (𝓞 T.X.E ⧸ w.1.asIdeal)) (z : T.X.K) : Prop :=
  match b with
  | some al => ∃ hh : h ∈ (T.L.levG i al w).H, z = (((T.L.levG i al w).lam ⟨h, hh⟩ : T.X.Kˣ) : T.X.K)
  | none => ∃ κ : T.AutX i,
      AmbientLatticeAvoidance.TopLev T.Ch T.xi (D.R.N i) ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) abelian₂ dep T.cst.sharp w.1 κ z ∧
        ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, redV w.1 (κ x) = h.1.mulVec (redV w.1 x)

def LocQ (i : ℕ) (b : Option (T.L.β i)) (P : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) (c : GLint T.X.E (D.R.N i) P.1)
    (z : T.X.K) : Prop :=
  match b with
  | some al => ∃ hc : c ∈ (T.L.levQ i al P).H, z = (((T.L.levQ i al P).lam ⟨c, hc⟩ : T.X.Kˣ) : T.X.K)
  | none => AmbientLatticeAvoidance.TopLev T.Ch T.xi (D.R.N i) ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) abelian₂ dep T.cst.sharp P.1 c.1 z

theorem mov_iff_loc {i : ℕ} (γ : UF T.X.E (D.R.N i)) (a a' : APt T i) (z : T.X.K) :
    AmbientLatticeAvoidance.Mov T.Ch T.sel T.xi T.cst T.L abelian₂ dep γ a a' z ↔
      a'.2.1 = a.2.1 ∧ a'.2.2 = (fun v => γ.1 v) '' a.2.2 ∧
      ∃ (g : GLG T.X.E (D.R.N i) T.Pr.vGs) (c : GLQ T.X.E (D.R.N i) (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K))),
        a'.1 = ((γ, g, c) : UF T.X.E (D.R.N i) × GLG T.X.E (D.R.N i) T.Pr.vGs ×
          GLQ T.X.E (D.R.N i) (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K))) • a.1 ∧
        ∃ (zG : T.Pr.vGs → T.X.K) (zQ : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K) → T.X.K),
          (∀ w, LocG T abelian₂ dep i a.2.1 w (g w) (zG w)) ∧ (∀ P, LocQ T abelian₂ dep i a.2.1 P (c P) (zQ P)) ∧
          z = (∏ w, zG w) * ∏ P, zQ P := by
  unfold AmbientLatticeAvoidance.Mov
  refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun g => exists_congr fun c =>
    and_congr_right fun _ => ?_
  generalize a.2.1 = b
  cases b with
  | none => exact ⟨fun h => h.2 rfl, fun h => ⟨fun _ hb => (Option.some_ne_none _ hb.symm).elim, fun _ => h⟩⟩
  | some al =>
    have e : ∀ (hh : g ∈ (T.L.levG i al).grp) (hc : c ∈ (T.L.levQ i al).grp),
        (((T.L.levG i al).chr ⟨g, hh⟩ * (T.L.levQ i al).chr ⟨c, hc⟩ : T.X.Kˣ) : T.X.K) =
        (∏ w, (((T.L.levG i al w).lam ⟨g w, hh w (Set.mem_univ _)⟩ : T.X.Kˣ) : T.X.K)) *
          ∏ P, (((T.L.levQ i al P).lam ⟨c P, hc P (Set.mem_univ _)⟩ : T.X.Kˣ) : T.X.K) := fun hh hc => by
      rw [Units.val_mul]
      exact congrArg₂ (· * ·) (piChar_val (fun w => (T.L.levG i al w).H) (fun w => (T.L.levG i al w).lam) g hh)
        (piChar_val (fun w => (T.L.levQ i al w).H) (fun w => (T.L.levQ i al w).lam) c hc)
    constructor
    · rintro ⟨h, -⟩
      obtain ⟨hh, hc, rfl⟩ := h al rfl
      exact ⟨_, _, fun w => ⟨_, rfl⟩, fun P => ⟨_, rfl⟩, e hh hc⟩
    · rintro ⟨zG, zQ, h1, h2, rfl⟩
      choose hh h1 using h1
      choose hc h2 using h2
      obtain rfl := funext h1
      obtain rfl := funext h2
      refine ⟨fun b hb => ?_, fun hb => (Option.some_ne_none _ hb).elim⟩
      obtain rfl := Option.some.inj hb
      have hh' : g ∈ (T.L.levG i al).grp := fun w _ => hh w
      have hc' : c ∈ (T.L.levQ i al).grp := fun P _ => hc P
      exact ⟨hh', hc', (e hh' hc').symm⟩

variable {T abelian₂ dep}

theorem Hyp.pi (H : Hyp T) (P : T.SB) : T.Pr.piT T.w ∉ P.1.asIdeal := pi_notMem H.hP H.hs T.xi T.w H.hT P

theorem Hyp.topM_G (H : Hyp T) (P : T.SB) (hw : P.1 ∈ T.Pr.vGs) :
    topM T D.R.m P = (stdAt T.X.E (D.R.N D.R.m) P.1).toAddSubgroup := by
  ext x
  show T.InTopLat _ P x ↔ x ∈ stdAt T.X.E (D.R.N D.R.m) P.1
  unfold ChainData.InTopLat
  rw [if_pos hw, std_top (Nm D)]

theorem Hyp.latTop (H : Hyp T) (hS : TopSame T abelian₂ dep) (P : T.SB) (x : Sp T.X.E (D.R.N D.R.m)) :
    x ∈ AmbientLatticeAvoidance.latTop T.Pr D.R (D.R.N D.R.m) ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) abelian₂ P.1 ↔ x ∈ topM T D.R.m P := by
  classical
  unfold AmbientLatticeAvoidance.latTop
  split_ifs with hw
  · rw [H.topM_G P hw]
    rfl
  · show _ ↔ T.InTopLat _ P x
    unfold ChainData.InTopLat
    rw [if_neg hw, (hS P).1]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · have h0 : ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) ≠ 0 := fun h0 => H.pi P (by
        rw [show T.Pr.piT T.w = 0 from RingOfIntegers.ext h0]
        exact zero_mem _)
      have := (IntAt.coe P.1 (T.Pr.piT T.w)).mul h
      rwa [show algebraMap (𝓞 T.X.E) T.X.E (T.Pr.piT T.w) = ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) from rfl,
        mul_inv_cancel_left₀ h0] at this
    · have := h.div_of_notMem (H.pi P)
      rwa [div_eq_inv_mul] at this

theorem Hyp.topLev (H : Hyp T) (hS : TopSame T abelian₂ dep) (P : T.SB) (κ : T.AutX D.R.m) (z : T.X.K) :
    AmbientLatticeAvoidance.TopLev T.Ch T.xi (D.R.N D.R.m) ((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E) abelian₂ dep T.cst.sharp P.1 κ z ↔
      LocB T D.R.m none P κ z := by
  rw [locB_top]
  unfold AmbientLatticeAvoidance.TopLev
  simp only [H.latTop hS P, ← (hS P).2]
  constructor
  · rintro ⟨j, hj, jx, k, h1, h2, h3, h4, h5, h6⟩
    exact ⟨j, hj, jx, k, ⟨h3, h4⟩, ⟨h1, h2⟩, h5, h6⟩
  · rintro ⟨j, hj, jx, k, ⟨h3, h4⟩, ⟨h1, h2⟩, h5, h6⟩
    exact ⟨j, hj, jx, k, h1, h2, h3, h4, h5, h6⟩

theorem Hyp.top_inv (H : Hyp T) {P : T.SB} {κ k₀ : T.AutX D.R.m} {v : T.X.K} (h : LocB T D.R.m none P κ v)
    (h₀ : k₀ ∈ topK T D.R.m P) : ∃ v', LocB T D.R.m none P (κ⁻¹ * k₀) v' ∧ v * v' = 1 := by
  obtain ⟨j, hj, jx, k, hk, he, rfl, rfl⟩ := (locB_top T P κ v).1 h
  exact ⟨_, (locB_top T P _ _).2 ⟨j⁻¹, inv_mem hj, jx⁻¹, jx * k⁻¹ * jx⁻¹ * k₀,
    mul_mem (congSub_conj (H.stab hj he) (inv_mem hk)) h₀, he.inv, by group, rfl⟩, lamM_inv P hj⟩

theorem Hyp.top_glint (H : Hyp T) {P : T.SB} (hw : P.1 ∈ T.Pr.vGs) {κ : T.AutX D.R.m} {v : T.X.K}
    (h : LocB T D.R.m none P κ v) : κ ∈ GLint T.X.E (D.R.N D.R.m) P.1 := by
  obtain ⟨j, hj, jx, k, hk, he, rfl, rfl⟩ := (locB_top T P κ v).1 h
  intro x
  have h1 := (H.stab hj he (k x)).trans (hk.1 x)
  rwa [H.topM_G P hw] at h1

theorem Hyp.mem_topK (H : Hyp T) {P : T.SB} (hw : P.1 ∈ T.Pr.vGs) {k : T.AutX D.R.m}
    (h1 : k ∈ GLint T.X.E (D.R.N D.R.m) P.1) (h2 : ∀ x ∈ stdAt T.X.E (D.R.N D.R.m) P.1, redV P.1 (k x) = redV P.1 x) :
    k ∈ topK T D.R.m P := by
  unfold topK
  rw [if_pos hw, pow_one, H.topM_G P hw]
  exact (cong_iff (GlobalTheory.T.integral_div_uniformizer_of_red_zero _ _ H.hX H.hP _ hw) k).2 ⟨h1, h2⟩

theorem Hyp.mem_prC (H : Hyp T) {i : ℕ} (al : T.L.β i) {P : T.SB} (hw : P.1 ∈ T.Pr.vGs) {k : T.AutX i}
    (h1 : k ∈ GLint T.X.E (D.R.N i) P.1) (h2 : ∀ x ∈ stdAt T.X.E (D.R.N i) P.1, redV P.1 (k x) = redV P.1 x) :
    k ∈ prCat (Pr := T.Pr) T.cst.sharp i P.1 (T.L.h i al P) :=
  GlobalTheory.T.mem_parahoric_of_trivial_reduction _ _ _ _ _ _ hw (GlobalTheory.T.integral_div_uniformizer_of_red_zero _ _ H.hX H.hP _ hw) _ (H.hL.stabG i al P hw) k h1 h2

theorem mulVec_inv {R : Type} [CommRing R] {n : ℕ} (h : GL (Fin n) R) {x y : Fin n → R} (e : x = h.1.mulVec y) :
    y = (h⁻¹).1.mulVec x := by
  rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem Hyp.locG (H : Hyp T) (hS : TopSame T abelian₂ dep) {i : ℕ} {b : Option (T.L.β i)} (hb : b = none → i = D.R.m)
    (w : T.Pr.vGs) (h : GL (Fin (D.R.N i)) (𝓞 T.X.E ⧸ w.1.asIdeal)) {κ : T.AutX i}
    (hκ : κ ∈ GLint T.X.E (D.R.N i) w.1)
    (hr : ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, redV w.1 x = h.1.mulVec (redV w.1 (κ x))) :
    (∀ z, LocG T abelian₂ dep i b w h z → ∃ v, LocB T i b (inG T w) κ v ∧ v * z = 1) ∧
      ∀ v, LocB T i b (inG T w) κ v → ∃ z, LocG T abelian₂ dep i b w h z ∧ v * z = 1 := by
  have hr' : ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, redV w.1 (κ x) = (h⁻¹).1.mulVec (redV w.1 x) :=
    fun x hx => mulVec_inv h (hr x hx)
  cases b with
  | some al =>
    have key : ∀ (hh : h ∈ (T.L.levG i al w).H) (r : AutY T.X D.R i),
        r ∈ Loc.Cbe (Jat (Pr := T.Pr) T.cst.sharp i w.1) (T.L.h i al (inG T w)) →
        (∀ x, r (Loc.inX T.X.E (D.R.N i) (cOf D.R i) x) = Loc.inX T.X.E (D.R.N i) (cOf D.R i) (κ x)) →
        chiInv T.Ch T.sel T.xi T.cst i (inG T w) (T.L.h i al (inG T w)) r *
          (((T.L.levG i al w).lam ⟨h, hh⟩ : T.X.Kˣ) : T.X.K) = 1 := fun hh r h1 h2 => by
      rw [← H.hL.chrG i al w (⟨h, hh⟩ : (T.L.levG i al w).H)⁻¹ κ r h1 h2 hr', ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one]
    constructor
    · rintro z ⟨hh, rfl⟩
      obtain ⟨g, hg, hgr⟩ := (H.hL.grpG i al w h⁻¹).1 (inv_mem hh)
      have hgi : g ∈ GLint T.X.E (D.R.N i) w.1 := H.hL.int i al (inG T w) hg
      have hk : κ * g⁻¹ ∈ prCat (Pr := T.Pr) T.cst.sharp i w.1 (T.L.h i al (inG T w)) :=
        H.mem_prC al (P := inG T w) w.2 (mul_mem hκ (inv_mem hgi)) fun x hx => by
          have hx' : g⁻¹ x ∈ stdAt T.X.E (D.R.N i) w.1 := (inv_mem hgi x).2 hx
          show redV w.1 (κ (g⁻¹ x)) = _
          rw [hr' _ hx', ← hgr _ hx', show g (g⁻¹ x) = x from g.apply_symm_apply x]
      have hκ' := mul_mem hk hg
      rw [inv_mul_cancel_right] at hκ'
      obtain ⟨r, h1, h2⟩ := hκ'
      exact ⟨_, ⟨r, ⟨h1, h2⟩, rfl⟩, key hh r h1 h2⟩
    · rintro v ⟨r, ⟨h1, h2⟩, rfl⟩
      have hh : h ∈ (T.L.levG i al w).H := inv_mem_iff.1 ((H.hL.grpG i al w h⁻¹).2 ⟨κ, ⟨r, h1, h2⟩, hr'⟩)
      exact ⟨_, ⟨hh, rfl⟩, key hh r h1 h2⟩
  | none =>
    obtain rfl := hb rfl
    constructor
    · rintro z ⟨κ₀, h1, h2⟩
      replace h1 := (H.topLev hS (inG T w) κ₀ z).1 h1
      have hk : κ₀ * κ ∈ topK T D.R.m (inG T w) :=
        H.mem_topK (P := inG T w) w.2 (mul_mem (H.top_glint (P := inG T w) w.2 h1) hκ) fun x hx => by
          show redV w.1 (κ₀ (κ x)) = _
          rw [h2 _ ((hκ x).2 hx), ← hr x hx]
      obtain ⟨v, h3, h4⟩ := H.top_inv h1 hk
      rw [inv_mul_cancel_left] at h3
      exact ⟨v, h3, by rw [mul_comm, h4]⟩
    · intro v h1
      obtain ⟨z, h3, h4⟩ := H.top_inv h1 (one_mem _)
      rw [mul_one] at h3
      refine ⟨z, ⟨κ⁻¹, (H.topLev hS (inG T w) _ z).2 h3, fun x hx => ?_⟩, h4⟩
      rw [hr _ ((inv_mem hκ x).2 hx), show κ (κ⁻¹ x) = x from κ.apply_symm_apply x]

theorem Hyp.locQ (H : Hyp T) (hS : TopSame T abelian₂ dep) {i : ℕ} {b : Option (T.L.β i)} (hb : b = none → i = D.R.m)
    (P : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) (c : GLint T.X.E (D.R.N i) P.1) :
    (∀ z, LocQ T abelian₂ dep i b P c z → ∃ v, LocB T i b (inQ T P) (c⁻¹).1 v ∧ v * z = 1) ∧
      ∀ v, LocB T i b (inQ T P) (c⁻¹).1 v → ∃ z, LocQ T abelian₂ dep i b P c z ∧ v * z = 1 := by
  cases b with
  | some al =>
    have key : ∀ (hc : c ∈ (T.L.levQ i al P).H) (r : AutY T.X D.R i),
        r ∈ Loc.Cbe (Jat (Pr := T.Pr) T.cst.sharp i P.1) (T.L.h i al (inQ T P)) →
        (∀ x, r (Loc.inX T.X.E (D.R.N i) (cOf D.R i) x) = Loc.inX T.X.E (D.R.N i) (cOf D.R i) ((c⁻¹).1 x)) →
        chiInv T.Ch T.sel T.xi T.cst i (inQ T P) (T.L.h i al (inQ T P)) r *
          (((T.L.levQ i al P).lam ⟨c, hc⟩ : T.X.Kˣ) : T.X.K) = 1 := fun hc r h1 h2 => by
      rw [← H.hL.chrQ i al P (⟨c, hc⟩ : (T.L.levQ i al P).H)⁻¹ r h1 h2, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one]
    constructor
    · rintro z ⟨hc, rfl⟩
      have h0 := inv_mem hc
      rw [H.hL.grpQ i al P, Subgroup.mem_subgroupOf] at h0
      obtain ⟨r, h1, h2⟩ := h0
      exact ⟨_, ⟨r, ⟨h1, h2⟩, rfl⟩, key hc r h1 h2⟩
    · rintro v ⟨r, ⟨h1, h2⟩, rfl⟩
      have hc : c ∈ (T.L.levQ i al P).H := by
        rw [← inv_mem_iff, H.hL.grpQ i al P, Subgroup.mem_subgroupOf]
        exact ⟨r, h1, h2⟩
      exact ⟨_, ⟨hc, rfl⟩, key hc r h1 h2⟩
  | none =>
    obtain rfl := hb rfl
    constructor
    · intro z h1
      replace h1 := (H.topLev hS (inQ T P) c.1 z).1 h1
      obtain ⟨v, h3, h4⟩ := H.top_inv h1 (one_mem _)
      rw [mul_one] at h3
      exact ⟨v, h3, by rw [mul_comm, h4]⟩
    · intro v h1
      obtain ⟨z, h3, h4⟩ := H.top_inv h1 (one_mem _)
      rw [mul_one, Subgroup.coe_inv, inv_inv] at h3
      exact ⟨z, (H.topLev hS (inQ T P) _ z).2 h3, h4⟩

theorem Hyp.prod_eq (H : Hyp T) {v : T.SB → T.X.K} {zG : T.Pr.vGs → T.X.K}
    {zQ : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K) → T.X.K} (h1 : ∀ w, v (inG T w) * zG w = 1)
    (h2 : ∀ P, v (inQ T P) * zQ P = 1) : (T.s.σ₀ (∏ P, v P))⁻¹ = T.s.σ₀ ((∏ w, zG w) * ∏ P, zQ P) := by
  classical
  have hd : Disjoint T.Pr.vGs (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) :=
    Finset.disjoint_right.2 fun P hP => H.disj ⟨P, hP⟩
  have e : (∏ P, v P) * ((∏ w, zG w) * ∏ P, zQ P) = 1 := by
    rw [prod_union_sub hd v, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun w _ => h1 w, Finset.prod_eq_one fun w _ => h2 w, mul_one]
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, e, map_one]

theorem Hyp.moves_iff (H : Hyp T) (hS : TopSame T abelian₂ dep) {i : ℕ} {a a' : APt T i} {p p' : T.Lab i}
    (h : Over T i a p) (h' : Over T i a' p') (hb : a.2.1 = none → i = D.R.m) (γ : UF T.X.E (D.R.N i)) (α : ℂ) :
    T.Moves i p p' γ α ↔ ∃ z, AmbientLatticeAvoidance.Mov T.Ch T.sel T.xi T.cst T.L abelian₂ dep γ a a' z ∧ α = T.s.σ₀ z := by
  classical
  have hc : p'.2.2 = (fun v => γ.1 v) '' p.2.2 ↔ a'.2.2 = (fun v => γ.1 v) '' a.2.2 := by
    by_cases hm : i + 1 = D.R.m
    · rw [h.cos hm, h'.cos hm]
    · rw [(h.cos' hm).1, (h.cos' hm).2, (h'.cos' hm).1, (h'.cos' hm).2, Set.image_empty, Set.image_univ,
        γ.1.surjective.range_eq]
      exact iff_of_true rfl rfl
  simp only [mov_iff_loc]
  unfold ChainData.Moves
  rw [hc, h.idx, h'.idx]
  constructor
  · rintro ⟨h1, h2, h3, κ, h4, h5⟩
    obtain ⟨v, hv, rfl⟩ := (inLev_iff T i _ κ α).1 h4
    have hN : p'.2.1.deco.1.N = gmap γ.1 p.2.1.deco.1.N := by rw [h2]; rfl
    have hκ : ∀ P, κ P ∈ GLint T.X.E (D.R.N i) P.1 := fun P => glint_of hN (h5 P)
    choose g hg using fun w : T.Pr.vGs => GlobalTheory.T.integral_gl_reduction_mod_prime _ _ w.1 (κ (inG T w))⁻¹ (inv_mem (hκ (inG T w)))
    have hg' : ∀ w : T.Pr.vGs, ∀ x ∈ stdAt T.X.E (D.R.N i) w.1,
        redV w.1 x = (g w).1.mulVec (redV w.1 (κ (inG T w) x)) := fun w x hx => by
      rw [← hg w _ ((hκ (inG T w) x).2 hx), show (κ (inG T w))⁻¹ (κ (inG T w) x) = x from LinearEquiv.symm_apply_apply _ x]
    let c : GLQ T.X.E (D.R.N i) (QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) := fun P => (⟨κ (inQ T P), hκ (inQ T P)⟩)⁻¹
    have hcq : ∀ P, κ (inQ T P) = ((c P)⁻¹).1 := fun P => by simp only [c, inv_inv]
    choose zG hz1 hz2 using fun w => (H.locG hS hb w (g w) (hκ (inG T w)) (hg' w)).2 _ (hv (inG T w))
    choose zQ hz3 hz4 using fun P => (H.locQ hS hb P (c P)).2 (v (inQ T P)) (hcq P ▸ hv (inQ T P))
    exact ⟨_, ⟨h1, h3, g, c, (act_iff h h' γ g c κ h5).2 ⟨h2, hg', hcq⟩, zG, zQ, hz1, hz3, rfl⟩, H.prod_eq hz2 hz4⟩
  · rintro ⟨z, ⟨h1, h3, g, c, h2, zG, zQ, hz1, hz3, rfl⟩, rfl⟩
    let κ : T.SB → T.AutX i := fun P => (γ.1 * p.2.1.fr P)⁻¹ * p'.2.1.fr P
    have h5 : ∀ P, p'.2.1.fr P = γ.1 * p.2.1.fr P * κ P := fun P => by simp only [κ, mul_inv_cancel_left]
    obtain ⟨e, hG, hQ⟩ := (act_iff h h' γ g c κ h5).1 h2
    have hN : p'.2.1.deco.1.N = gmap γ.1 p.2.1.deco.1.N := by rw [e]; rfl
    have hκ : ∀ P, κ P ∈ GLint T.X.E (D.R.N i) P.1 := fun P => glint_of hN (h5 P)
    choose vG hv1 hv2 using fun w => (H.locG hS hb w (g w) (hκ (inG T w)) (hG w)).1 _ (hz1 w)
    choose vQ hv3 hv4 using fun P => (H.locQ hS hb P (c P)).1 _ (hz3 P)
    let v : T.SB → T.X.K := fun P => if hw : P.1 ∈ T.Pr.vGs then vG ⟨P.1, hw⟩
      else vQ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hw⟩
    have e1 : ∀ w, v (inG T w) = vG w := fun w => dif_pos w.2
    have e2 : ∀ P, v (inQ T P) = vQ P := fun P => dif_neg (H.disj P)
    refine ⟨h1, e, h3, κ, (inLev_iff T i _ κ _).2 ⟨v, fun P => ?_,
      (H.prod_eq (fun w => by rw [e1, hv2]) fun P => by rw [e2, hv4]).symm⟩, h5⟩
    rcases sb_cases P with ⟨w, rfl⟩ | ⟨Q, rfl⟩
    · rw [e1]
      exact hv1 w
    · rw [e2, hQ]
      exact hv3 Q

end Moves

section Classes

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}

theorem moves_refl {i : ℕ} (x : T.Lab i) : ∃ a, T.Moves i x x 1 a := by
  choose v hv using fun P => locB_one (T := T) i x.1 P
  refine ⟨_, rfl, (one_smul _ x.2.1.deco).symm, (Set.image_id _).symm, fun _ => 1,
    (inLev_iff T i _ _ _).2 ⟨v, hv, rfl⟩, fun P => rfl⟩

theorem Hyp.moves_eucl (H : Hyp T) {i : ℕ} {x x' y : T.Lab i} (hb : x.1 = none → i = D.R.m)
    {γ γ' : UF T.X.E (D.R.N i)} {a a' : ℂ} (h : T.Moves i x y γ a) (h' : T.Moves i x' y γ' a') :
    ∃ a'', T.Moves i x x' (γ'⁻¹ * γ) a'' := by
  obtain ⟨h1, h2, h3, κ, h4, h5⟩ := h
  obtain ⟨h1', h2', h3', κ', h4', h5'⟩ := h'
  obtain ⟨v, hv, -⟩ := (inLev_iff T i _ κ a).1 h4
  obtain ⟨v', hv', -⟩ := (inLev_iff T i _ κ' a').1 h4'
  have e : x'.1 = x.1 := h1'.symm.trans h1
  rw [e] at hv'
  have hl : ∀ P, ∃ w, LocB T i x.1 P (κ P * (κ' P)⁻¹) w := fun P => by
    have := H.locB_div hb (H.locB_div hb ⟨_, hv P⟩ (locB_one i _ P)) (H.locB_div hb ⟨_, hv' P⟩ (locB_one i _ P))
    rwa [mul_one, mul_one, inv_inv] at this
  choose w hw using hl
  refine ⟨_, e, ?_, ?_, fun P => κ P * (κ' P)⁻¹, (inLev_iff T i _ _ _).2 ⟨w, hw, rfl⟩, fun P => ?_⟩
  · have : ((γ'⁻¹ * γ, 1) : UF T.X.E (D.R.N i) × GLG T.X.E (D.R.N i) ∅) = (γ', 1)⁻¹ * (γ, 1) := by simp
    rw [this, mul_smul, ← h2, h2', inv_smul_smul]
  · have : (fun v => (γ'⁻¹ * γ).1 v) '' x.2.2 = (fun v => γ'.1.symm v) '' ((fun v => γ.1 v) '' x.2.2) := by
      rw [Set.image_image]
      rfl
    rw [this, ← h3, h3', Set.image_image]
    simp
  · have := (h5' P).symm.trans (h5 P)
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x'.2.1.fr P = γ'.1⁻¹ * (γ'.1 * x'.2.1.fr P * κ' P) * (κ' P)⁻¹ := by group
      _ = _ := by rw [this]; group

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 T.X.E) (Sp T.X.E n)} {Y : Set (Sp T.X.E n)}
    (hY : Y ∈ ybSet T.sel T.xi T.cst N) {P : T.SB} (hw : P.1 ∈ T.Pr.vGs) :
    (qOf P.1 : T.X.E) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hYd⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun z => z ∈ Y) ⟨y, by simp [hYd]⟩
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 (hYd.le h0) P
  rw [if_pos hw] at h1 h2
  rw [zpow_neg, zpow_one, inv_inv] at h1
  rw [zpow_zero, inv_one, one_smul] at h2
  have h3 := Submodule.smul_mem _ ((qOf P.1 : ℕ) : 𝓞 T.X.E) h2
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul T.X.E] at h3
  have := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at this

theorem Hyp.psi_eq (H : Hyp T) {a : APt T (D.R.m - 2 + 1)} {p : T.Lab (D.R.m - 2 + 1)} (h : Over T _ a p)
    {Y : Set (Sp T.X.E (D.R.N (D.R.m - 2 + 1)))} (hY : Y ∈ ybSet T.sel T.xi T.cst a.1.deco.1.N) (P : T.SB)
    (al : T.L.β (D.R.m - 2)) (x₀ : HomE T.X.E (D.R.N (D.R.m - 2)) (D.R.N (D.R.m - 2 + 1))) :
    PsiAt T.Ch T.sel T.xi T.cst (D.R.m - 2) P (T.L.h (D.R.m - 2) al P) x₀ ((frsF T.sel T.xi a.1 P).symm (repY Y)) =
      PsiAt T.Ch T.sel T.xi T.cst (D.R.m - 2) P (T.L.h (D.R.m - 2) al P) x₀ ((p.2.1.fr P).symm (repY Y)) := by
  classical
  rcases sb_cases P with ⟨w, rfl⟩ | ⟨Q, rfl⟩
  · have hf : frsF T.sel T.xi a.1 (inG T w) = a.1.deco.1.liftFr w := dif_pos w.2
    obtain ⟨s1, s2⟩ := GlobalTheory.T.decoration_lift_std_lattice_reduction _ _ _ _ a.1.deco w
    have hq0 : (qOf w.1 : T.X.E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_ne w.1)
    let k : T.AutX (D.R.m - 2 + 1) := (a.1.deco.1.liftFr w)⁻¹ * p.2.1.fr (inG T w)
    have hk0 : ∀ x, a.1.deco.1.liftFr w (k x) = p.2.1.fr (inG T w) x := fun x => LinearEquiv.apply_symm_apply _ _
    have hk1 : k ∈ GLint T.X.E _ w.1 := fun x => by
      rw [← s1, hk0, ← fr_spec p.2.1 (inG T w) x, h.lat]
    have hk := (cong_iff (GlobalTheory.T.integral_div_uniformizer_of_red_zero _ _ H.hX H.hP _ w.2) k).2 ⟨hk1, fun x hx => by
      rw [← s2 _ ((hk1 x).2 hx), hk0, h.frG w x hx]⟩
    have hx : (qOf w.1 : T.X.E) • (p.2.1.fr (inG T w)).symm (repY Y) ∈ stdAt T.X.E _ w.1 := by
      rw [← fr_spec p.2.1 (inG T w), map_smul, LinearEquiv.apply_symm_apply, h.lat]
      exact repY_mem hY (P := inG T w) w.2
    have h3 := hk.2 _ hx
    rw [map_smul, ← smul_sub, inv_smul_smul₀ hq0] at h3
    have h4 : k ((p.2.1.fr (inG T w)).symm (repY Y)) = (a.1.deco.1.liftFr w).symm (repY Y) := by
      rw [LinearEquiv.eq_symm_apply, hk0, LinearEquiv.apply_symm_apply]
    rw [h4] at h3
    have h5 := H.hL.psiInv al (inG T w) x₀ ((p.2.1.fr (inG T w)).symm (repY Y)) _ fun l => by
      rw [if_pos w.2, pow_zero, inv_one, one_mul]
      exact (mem_std _).1 h3 l
    rw [add_sub_cancel] at h5
    rw [hf, h5]
  · have hf : frsF T.sel T.xi a.1 (inQ T Q) = a.1.fr Q := dif_neg (H.disj Q)
    rw [hf, h.frQ]

theorem Hyp.valid_iff (H : Hyp T) {i : ℕ} (hi : i ≤ D.R.m) {a : APt T i} {p : T.Lab i} (h : Over T i a p) :
    AmbientLatticeAvoidance.Pt.Valid T.Ch T.sel T.xi T.cst T.L a ↔ T.Admissible i p := by
  have hm := D.R.two_le_m
  have key : i + 1 = D.R.m → (AmbientLatticeAvoidance.YbOk T.Ch T.sel T.xi T.cst T.L a.1 a.2.2 ↔
      p.2.2 ∈ ybSet T.sel T.xi T.cst p.2.1.deco.1.N ∧
      ∀ P : T.SB, ∃ (al : T.L.β (D.R.m - 2)) (x₀ : HomE T.X.E (D.R.N (D.R.m - 2)) (D.R.N (D.R.m - 2 + 1))),
        PsiAt T.Ch T.sel T.xi T.cst (D.R.m - 2) P (T.L.h (D.R.m - 2) al P) x₀
          (cpy T.X.E _ _ ((p.2.1.fr P).symm (repY p.2.2))) ≠ 0) := fun h1 => by
    have h2 := h.cos h1
    obtain rfl : i = D.R.m - 2 + 1 := by omega
    unfold AmbientLatticeAvoidance.YbOk
    rw [h2, h.lat]
    refine and_congr_right fun hY => forall_congr' fun P => exists_congr fun al => exists_congr fun x₀ => ?_
    rw [cpy_self, ← H.psi_eq h hY P al x₀, show ∀ y, AmbientLatticeAvoidance.reix T.X.E _ _ y = cpy T.X.E _ _ y from fun _ => rfl, cpy_self]
  unfold AmbientLatticeAvoidance.Pt.Valid ChainData.Admissible
  rw [h.idx, Option.isSome_iff_ne_none]
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨h1, fun e => h2 e.ge, fun e => (h.cos' e).2, fun e => (key e).1 (h3 e)⟩
  · rintro ⟨h1, h2, -, h4⟩
    exact ⟨h1, fun e => h2 (le_antisymm hi e), fun e => (key e).2 (h4 e), fun e => (h.cos' e).1⟩

theorem none_top {i : ℕ} (hi : i ≤ D.R.m) {p : T.Lab i} (h : T.Admissible i p) (e : p.1 = none) : i = D.R.m := by
  by_contra hn
  have := h.1 (lt_of_le_of_ne hi hn)
  rw [e] at this
  simp at this

variable (T) in

def RepOver (rep : ∀ i, (D.chTw u μ).cls i → APt T i) : Prop := ∀ i ≤ D.R.m, ∀ c, Over T i (rep i c) (T.rep i c)

variable {rep : ∀ i, (D.chTw u μ).cls i → APt T i}

theorem Hyp.cls_iff (H : Hyp T) (hS : TopSame T abelian₂ dep) (hr : RepOver T rep) :
    AmbientLatticeAvoidance.ClsTie T.Ch T.sel T.xi T.cst T.L abelian₂ dep (D.chTw u μ) T.w rep ↔
      ∀ i ≤ D.R.m, (∀ c, T.Admissible i (T.rep i c)) ∧
        ∀ x, T.Admissible i x → ∃! c, ∃ γ a, T.Moves i (T.rep i c) x γ a := by
  refine forall₂_congr fun i hi => ?_
  have hv : (∀ c, AmbientLatticeAvoidance.Pt.Valid T.Ch T.sel T.xi T.cst T.L (rep i c)) ↔ ∀ c, T.Admissible i (T.rep i c) :=
    forall_congr' fun c => H.valid_iff hi (hr i hi c)
  rw [hv]
  refine and_congr_right fun hA => ?_
  have hb : ∀ c, (rep i c).2.1 = none → i = D.R.m := fun c e => none_top hi (hA c) ((hr i hi c).idx.trans e)
  constructor
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, ha⟩ := exists_down x hx.2.2.1
    obtain ⟨c, γ, z, hc⟩ := h2 a ((H.valid_iff hi ha).2 hx)
    have hc' := (H.moves_iff hS (hr i hi c) ha (hb c) γ _).2 ⟨z, hc, rfl⟩
    refine ⟨c, ⟨γ, _, hc'⟩, ?_⟩
    rintro c' ⟨γ', a', h'⟩
    obtain ⟨a'', h''⟩ := H.moves_eucl (none_top hi (hA c')) h' hc'
    obtain ⟨z', hz, -⟩ := (H.moves_iff hS (hr i hi c') (hr i hi c) (hb c') _ _).1 h''
    exact h1 _ _ _ _ hz
  · intro h
    refine ⟨fun c c' γ z hz => ?_, fun a ha => ?_⟩
    · exact (h _ (hA c')).unique ⟨γ, _, (H.moves_iff hS (hr i hi c) (hr i hi c') (hb c) γ _).2 ⟨z, hz, rfl⟩⟩
        ⟨1, moves_refl _⟩
    · have ho := H.over_up a ha.2.2.2
      obtain ⟨c, ⟨γ, α, hc⟩, -⟩ := h _ ((H.valid_iff hi ho).1 ha)
      obtain ⟨z, hz, -⟩ := (H.moves_iff hS (hr i hi c) ho (hb c) γ α).1 hc
      exact ⟨c, γ, z, hz⟩

variable (T abelian₂ dep rep) in

def StabCard : Prop := ∀ i ≤ D.R.m, ∀ c, Nat.card ((D.chTw u μ).stab i c) =
  Nat.card {γ : UF T.X.E (D.R.N i) // ∃ z, AmbientLatticeAvoidance.Mov T.Ch T.sel T.xi T.cst T.L abelian₂ dep γ (rep i c) (rep i c) z}

end Classes

section Kernels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {rep : ∀ i, (D.chTw u μ).cls i → APt T i}

variable (T rep) in

def RepUp : Prop := ∀ i c, T.rep i c = up T i (rep i c)

variable (T) in

def LatTie : Prop := ∀ i ≤ D.R.m, ∀ c, (T.O.lat i c).1 = T.s.lat (T.rep i c).2.1.deco.1.N

variable (T) in

def ThetaCalc : Prop :=
  ∀ i < D.R.m, T.amb.IndTieD (D.R.N i) (D.R.N (i + 1)) (Sall T.sel T.xi T.w) (cAof T.sel T.xi T.cst * cBof T.sel T.xi T.cst T.w) ∧
    ∀ N N', IsSdLat N → IsSdLat N' →
      0 < volC (a := D.R.N i) (b := D.R.N (i + 1)) T.amb.AA (Sall T.sel T.xi T.w) N N'

variable {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}

def ChainA (T : ChainData D u μ) (Tw : TwForms D)
    (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
    (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ) (rep : ∀ i, (D.chTw u μ).cls i → APt T i) : Prop :=
  AmbientLatticeAvoidance.TopOk T.sel T.xi T.cst abelian₂ dep ∧
  AmbientLatticeAvoidance.ClsTie T.Ch T.sel T.xi T.cst T.L abelian₂ dep (D.chTw u μ) T.w rep ∧ StabCard T abelian₂ dep rep ∧
  AmbientLatticeAvoidance.FiTie T.s T.Ch T.sel T.xi T.cst T.L abelian₂ dep (D.chTw u μ) T.w rep T.O.frm (Tw.fm u μ) ∧
  AmbientLatticeAvoidance.RhoTie T.s T.Ch T.sel T.xi T.cst T.L (D.chTw u μ) T.w rep (TaylorLogMetric.chiRec D T.idl) ∧
  AmbientLatticeAvoidance.UnfTie T.s T.Ch T.sel T.xi T.cst T.L (D.chTw u μ) T.w rep T.O.frm T.amb T.O.dgen

end Kernels

end GlobalTheory.KFormsCmp
