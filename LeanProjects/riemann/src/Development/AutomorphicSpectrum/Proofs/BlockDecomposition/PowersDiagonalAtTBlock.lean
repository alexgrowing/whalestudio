import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (muAt MOk MatchLMB2)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMB2

section Scale

theorem avg_smul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun x => c * u x) = c * avg u := by
  by_cases hc : c = 0
  · subst hc
    simp [avg]
  · have key : ∀ S : Subgroup H, S = rStab u →
        ((S.index : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, c * u q.out =
          c * (((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out) := by
      rintro S rfl
      have h : (∑ᶠ q : H ⧸ rStab u, c * u q.out) = c * ∑ᶠ q : H ⧸ rStab u, u q.out := by
        simpa only [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ rStab u => u q.out)).symm
      rw [h]
      ring
    exact key _ (GlobalTheory.CompanionTheory.TailLocPow.rStab_smul c hc u)

theorem twOrb_smul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (y : G) (c : ℂ) (f : G → ℂ) :
    twOrb θ K y (fun z => c * f z) = c * twOrb θ K y f := by
  unfold twOrb
  simp only [avg_smul (H := K) c]
  have := (smul_finsum c (fun q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) =>
    (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
      avg fun k : K => f ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)))).symm
  simp only [smul_eq_mul] at this
  rw [← this]
  exact finsum_congr fun q => by ring

theorem clSum_smul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ)
    (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun z => c * f z) = c * clSum θ K S wt f := by
  unfold clSum
  have := (smul_finsum c (fun t : TwCl θ => if t.rep ∈ S then wt t.rep * twOrb θ K t.rep f else 0)).symm
  simp only [smul_eq_mul] at this
  rw [← this]
  refine finsum_congr fun t => ?_
  split_ifs
  · rw [twOrb_smul]
    ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem match_smul {n a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ} {f : UL n w → ℂ}
    {φ : GLw a w × GLw b w → ℂ} (c : ℂ) (h : Match n a b w μ f φ) :
    Match n a b w μ (fun γ => c * f γ) (fun y => c * φ y) := by
  intro Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂
  have e := h Q₁ Q₂ m₁ m₂ d₁ d₂ hs c₁ c₂
  unfold stTw2 kapOrb at e ⊢
  rw [clSum_smul, clSum_smul, e]
  ring

theorem lconv_smul {n : ℕ} {w : Pl E} (c c' : ℂ) (f g : UL n w → ℂ) :
    lconv (fun y => c * f y) (fun y => c' * g y) = fun y => (c * c') * lconv f g y := by
  funext y
  unfold lconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem mconv_smul {a b : ℕ} {w : Pl E} (c c' : ℂ) (f g : GLw a w × GLw b w → ℂ) :
    mconv (fun y => c * f y) (fun y => c' * g y) = fun y => (c * c') * mconv f g y := by
  funext y
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem lpow_smul {n : ℕ} {w : Pl E} (K' : Subgroup (UL n w)) (c : ℂ) (g : UL n w → ℂ) (k : ℕ) :
    lpow K' (fun y => c * g y) (k + 1) = fun y => c ^ (k + 1) * lpow K' g (k + 1) y := by
  induction k with
  | zero =>
    funext y
    have := congrFun (lconv_smul c 1 g (lpow K' g 0)) y
    simp only [one_mul, mul_one] at this
    rw [zero_add, pow_one]
    exact this
  | succ k ih =>
    show lconv _ (lpow K' _ (k + 1)) = _
    rw [ih, lconv_smul]
    funext y
    show _ * lconv g (lpow K' g (k + 1)) y = _ * lconv g (lpow K' g (k + 1)) y
    ring

theorem mpow_smul {a b : ℕ} (w : Pl E) (c : ℂ) (f : GLw a w × GLw b w → ℂ) (k : ℕ) :
    MT.mpow w (fun y => c * f y) (k + 1) = fun y => c ^ (k + 1) * MT.mpow w f (k + 1) y := by
  induction k with
  | zero =>
    funext y
    have := congrFun (mconv_smul c 1 f (MT.mpow w f 0)) y
    simp only [one_mul, mul_one] at this
    rw [zero_add, pow_one]
    exact this
  | succ k ih =>
    show mconv _ (MT.mpow w _ (k + 1)) = _
    rw [ih, mconv_smul]
    funext y
    show _ * mconv f (MT.mpow w f (k + 1)) y = _ * mconv f (MT.mpow w f (k + 1)) y
    ring

end Scale

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_left {a b : ℕ} {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} {f : LF a b w} (g : LF a b w)
    (hf : ∀ u ∈ U, ∀ x, f (u * x) = f x) {u : GLw a w × GLw b w} (hu : u ∈ U) (m : GLw a w × GLw b w) :
    mconv f g (u * m) = mconv f g m := by
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.CtMulSplit.hint_left _ u]
  congr 1
  funext z
  rw [hf u hu z]
  congr 2
  group

theorem pw_left {κ : Pl E → Type} [∀ w, Fintype (κ w)] {a b : ℕ} (L : LM κ a b) {w : Pl E}
    {U : Subgroup (GLw a w × GLw b w)} (S : ∀ _ : κ w, Prop)
    (hL : ∀ x y, S x → S y → ∀ u ∈ U, ∀ g, L.m w x y (u * g) = L.m w x y g) (hS : ∀ x, S x) (k : ℕ) (x y : κ w)
    {u : GLw a w × GLw b w} (hu : u ∈ U) (g : GLw a w × GLw b w) :
    (PositivityTheory.Rg.BcB.F.MLM.pw L k).m w x y (u * g) = (PositivityTheory.Rg.BcB.F.MLM.pw L k).m w x y g := by
  cases k with
  | zero => exact hL x y (hS x) (hS y) u hu g
  | succ k =>
    show (∑ z, mconv (L.m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw L k).m w z y)) (u * g) =
      (∑ z, mconv (L.m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw L k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ =>
      mconv_left _ (fun v hv t => hL x z (hS x) (hS z) v hv t) hu g

theorem tr_one (d : LocData E n) {a : ℕ} (L : LM d.kap a (n - a)) {w : Pl E} (hw : w ∈ d.P) :
    L.tr d.P d.one w = ∑ x, L.m w x x := by
  unfold LM.tr
  rw [if_pos hw]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp [LocData.one]
  · intro y _ hy
    simp [LocData.one, hy]
  · simp

theorem sum_kap_alt (d : LocData E n) {w : Pl E} (hT : w ∈ d.T) {M : Type} [AddCommMonoid M]
    (F : Finset (Fin (n / 2)) → M) : ∑ x : d.kap w, F x.1.1 = ∑ s, F s := by
  have e : d.idx w = Finset.univ ×ˢ {1} := by
    unfold LocData.idx
    rw [if_pos hT]
  rw [Finset.sum_coe_sort (d.idx w) (fun p => F p.1), e, Finset.sum_product]
  simp

theorem sum_kap_S (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) {M : Type} [AddCommMonoid M]
    (F : GLw n w → M) : ∑ x : d.kap w, F x.1.2 = ∑ x ∈ d.X w, F x := by
  have e : d.idx w = {∅} ×ˢ d.X w := by
    unfold LocData.idx
    rw [if_neg hT, if_pos hS]
  rw [Finset.sum_coe_sort (d.idx w) (fun p => F p.2), e, Finset.sum_product]
  simp

end Alg

section TPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem qT_eq (d : LocData E n) {a : ℕ} (w : Pl E) (s : Finset (Fin (n / 2))) (y : GLw a w × GLw (n - a) w) :
    d.qT a w s y = (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
      MT.entT n w (d.ϖ w) a (fun j : (d.c w).support => d.c w j.1) (fun j => j.1) s y := by
  unfold LocData.qT MT.entT
  by_cases h : LocData.admitted n a s
  · have h' : MT.admitted n a s := ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
    rw [dif_pos h, dif_pos h', Finset.mul_sum]
    unfold Finsupp.sum
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold dc2
    ring
  · have h' : ¬ MT.admitted n a s := fun g => h ⟨⟨g.1, g.2.1, g.2.2.1⟩, g.2.2.2.1, g.2.2.2.2⟩
    rw [dif_neg h, dif_neg h', mul_zero]

theorem g₀_eq (d : LocData E n) {w : Pl E} (hT : w ∈ d.T) (y : UL n w) :
    d.g₀ w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
      ∑ j : (d.c w).support, d.c w j.1 * fU n w (d.b w) (d.ϖ w) (lOf j.1) y := by
  unfold LocData.g₀
  rw [if_pos hT, Finset.mul_sum]
  unfold Finsupp.sum
  rw [← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem qT_mpow_left (d : LocData E n) {a : ℕ} (w : Pl E) (s : Finset (Fin (n / 2))) (k : ℕ)
    {u : GLw a w × GLw (n - a) w} (hu : u ∈ I2 a (n - a) w) (g : GLw a w × GLw (n - a) w) :
    MT.mpow w (d.qT a w s) (k + 1) (u * g) = MT.mpow w (d.qT a w s) (k + 1) g :=
  mconv_left _ (fun _ hv t => (GlobalTheory.CompanionTheory.MatchId.qT_inv d s hv t).1) hu g

theorem powers_diagonal_at_T_block (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (k : ℕ) (x y : d.kap w) :
    (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w x y = d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) x y := by
  have hb : ∀ x y : d.kap w, (d.betaL a ha).m w x y = d.diag (fun x => d.qT a w x.1.1) x y := fun x y => by
    show (if w ∈ d.T then _ else _) = _
    rw [if_pos hT]
  induction k generalizing x y with
  | zero =>
    show (d.betaL a ha).m w x y = _
    rw [hb]
    unfold LocData.diag
    split_ifs
    · exact (GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w)
        (d.qT a w x.1.1) fun u hu g => (GlobalTheory.CompanionTheory.MatchId.qT_inv d _ hu g).2).symm
    · rfl
  | succ k ih =>
    show ∑ z, mconv ((d.betaL a ha).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w z y) = _
    simp only [hb, ih]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) z y)]
    unfold LocData.diag
    split_ifs with h
    · rfl
    · exact GlobalTheory.CompanionTheory.MatchId.mconv_zero_right _

theorem trace_test_function_eq (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (m : ℕ) :
    ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w =
      fun y => ∑ s, MT.mpow w (d.qT a w s) (m + 1) y := by
  have hP : w ∈ d.P := Finset.mem_union_left _ hT
  have hlev : d.lev a w = I2 a (n - a) w := by
    unfold LocData.lev
    rw [if_pos hT]
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).m w x x =
      MT.mpow w (d.qT a w x.1.1) (m + 1) := by
    intro x
    show ∑ z, mconv ((d.fixL a).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x) = _
    have e : ∀ z, (d.fixL a).m w x z = d.diag (fun _ => PositivityTheory.Rg.BcB.F.idem (I2 a (n - a) w)) x z := fun z => by
      show d.diag (fun _ => if w ∈ d.T then PositivityTheory.Rg.BcB.F.idem (d.lev a w) else d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.lev a w)) x z = _
      rw [if_pos hT, hlev]
    simp only [e]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x), powers_diagonal_at_T_block d ha hT]
    unfold LocData.diag
    rw [if_pos rfl]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w) _
      fun u hu g => qT_mpow_left d w _ m hu g
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent]
  exact sum_kap_alt d hT (fun s => MT.mpow w (d.qT a w s) (m + 1) y)

theorem matching_at_T (hMT : MT.MatchT) (hE : Unr E) (d : LocData E n) (hm : MOk d) {a : ℕ} (ha : a ≤ n) (m : ℕ) {w : Pl E}
    (hT : w ∈ d.T) : Match n a (n - a) w 1 (d.gU (m + 1) w)
      (((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w) := by
  obtain ⟨hns, hW, hϖ, hcone⟩ := hm.T w hT
  have hcj : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hE w).1
  have hidx : (iwU n w (d.b w)).relIndex (KL n w) ≠ 0 :=
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w (d.b w)) (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hns n hcj)
  have h := match_smul ((((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1))
    (hMT E hE w hns n a ha (d.b w) hW (d.ϖ w) hϖ (d.c w).support (fun j => d.c w j.1) (fun j => j.1)
      (fun j => hcone j.1 j.2) (m + 1) (by omega))
  have e1 : d.gU (m + 1) w = fun γ => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      lpow (iwU n w (d.b w)) (fun γ => ∑ j : (d.c w).support, d.c w j.1 * fU n w (d.b w) (d.ϖ w) (lOf j.1) γ) (m + 1) γ := by
    have hKU : d.KU w = iwU n w (d.b w) := by
      unfold LocData.KU
      rw [if_pos hT]
    have hg : d.g₀ w = fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
        ∑ j : (d.c w).support, d.c w j.1 * fU n w (d.b w) (d.ϖ w) (lOf j.1) y := funext (g₀_eq d hT)
    unfold LocData.gU
    rw [hKU, hg, lpow_smul]
  have hc : (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * MT.cR n a w (d.b w) =
      (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) := by
    have h0 : (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
    unfold MT.cR
    rw [show I2 a (n - a) w = (iwGL a w).prod (iwGL (n - a) w) from rfl,
      show K2 a (n - a) w = (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) from rfl, GlobalTheory.CompanionTheory.MatchPow.relIndex_prod,
      Nat.cast_mul]
    field_simp
  have e2 : ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w =
      fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) * (MT.cR n a w (d.b w) ^ (m + 1) *
        ∑ s, MT.mpow w (MT.entT n w (d.ϖ w) a (fun j : (d.c w).support => d.c w j.1) (fun j => j.1) s) (m + 1) y) := by
    rw [trace_test_function_eq d ha hT]
    funext y
    have eq : ∀ s, d.qT a w s = fun y => (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
        MT.entT n w (d.ϖ w) a (fun j : (d.c w).support => d.c w j.1) (fun j => j.1) s y := fun s => funext (qT_eq d w s)
    simp only [eq, mpow_smul]
    rw [← Finset.mul_sum, ← mul_assoc, ← mul_pow, hc]
  rw [e1, e2]
  exact h

end TPlace

section SPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def chi {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : ℂ :=
  (μ (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ)

theorem chi_ne {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : chi μ m ≠ 0 :=
  Units.ne_zero _

theorem chi_mul {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (x y : GLw a w × GLw b w) :
    chi μ (x * y) = chi μ x * chi μ y := by
  unfold chi
  rw [← Units.val_mul, ← map_mul]
  congr 2
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
  exact mul_mul_mul_comm _ _ _ _

theorem sign_chi (d : LocData E n) {a : ℕ} (w : Pl E) (m : GLw a w × GLw (n - a) w) :
    ((d.μ w ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) : ℂˣ) : ℂ) =
      d.sgn a w * chi (d.μ w) m := by
  unfold LocData.sgn chi
  rw [mul_assoc, map_mul, Units.val_mul]

theorem mac_eq (d : LocData E n) {a : ℕ} (ha : a ≤ n) (w : Pl E) (x y : GLw n w) :
    d.mac a ha w (d.e w) x y = fun m => chi (d.μ w) m *
      (((d.X w).card : ℂ)⁻¹ * phi3 (Nat.add_sub_of_le ha) w (d.e w) x y m) := by
  funext m
  unfold LocData.mac phiMu
  rw [sign_chi]
  have hs : d.sgn a w ≠ 0 := Units.ne_zero _
  rw [mul_inv]
  field_simp

theorem pw_S (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) (k : ℕ) (x y : d.kap w) :
    (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w x y = fun m => chi (d.μ w) m *
      (((d.X w).card : ℂ)⁻¹ * MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k x.1.2 y.1.2 m) := by
  have hb : ∀ x y : d.kap w, (d.betaL a ha).m w x y = d.mac a ha w (d.e w) x.1.2 y.1.2 := fun x y => by
    show (if w ∈ d.T then _ else _) = _
    rw [if_neg hT]
  induction k generalizing x y with
  | zero =>
    show (d.betaL a ha).m w x y = _
    rw [hb, mac_eq]
    rfl
  | succ k ih =>
    show ∑ z, mconv ((d.betaL a ha).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w z y) = _
    funext m
    rw [Finset.sum_apply]
    simp only [hb, ih, mac_eq]
    have e : ∀ z : d.kap w, mconv (fun m => chi (d.μ w) m *
        (((d.X w).card : ℂ)⁻¹ * phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z.1.2 m))
        (fun m => chi (d.μ w) m * (((d.X w).card : ℂ)⁻¹ *
          MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z.1.2 y.1.2 m)) m =
        chi (d.μ w) m * ((((d.X w).card : ℂ)⁻¹ * ((d.X w).card : ℂ)⁻¹) *
          mconv (phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z.1.2)
            (MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z.1.2 y.1.2) m) := fun z => by
      rw [GlobalTheory.CompanionTheory.CtMulSplit.mconv_twist (chi (d.μ w)) (chi_ne _) (chi_mul _)]
      rw [mconv_smul]
    simp only [e]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_kap_S d hT hS (fun z => mconv (phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z)
      (MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z y.1.2) m)]
    show _ = chi (d.μ w) m * (((d.X w).card : ℂ)⁻¹ * (((d.X w).card : ℂ)⁻¹ * _))
    ring

theorem tr_S (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) (m : ℕ) :
    ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w =
      MS.splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w (d.μ w) (d.X w) (d.e w) m := by
  have hP : w ∈ d.P := Finset.mem_union_right _ hS
  have hlev : d.lev a w = d.L a w := by
    simp only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_left _ hS)]
  have mem : ∀ x : d.kap w, x.1.2 ∈ d.X w := fun x => by
    have := x.2
    simp only [LocData.idx, if_neg hT, if_pos hS] at this
    exact (Finset.mem_product.1 this).2
  obtain ⟨ho, hle⟩ := GlobalTheory.CompanionTheory.MatchId.L_ok hd ha (Finset.mem_union_left _ hS)
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).m w x x =
      fun y => d.sgn a w * (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w x x y := by
    intro x
    show ∑ z, mconv ((d.fixL a).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x) = _
    have e : ∀ z, (d.fixL a).m w x z = d.diag (fun _ => d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.L a w)) x z := fun z => by
      show d.diag (fun _ => if w ∈ d.T then PositivityTheory.Rg.BcB.F.idem (d.lev a w) else d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.lev a w)) x z = _
      rw [if_neg hT, hlev]
    simp only [e]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x)]
    have hleft : mconv (PositivityTheory.Rg.BcB.F.idem (d.L a w)) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w x x) =
        (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w x x := GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left ho hle _
      fun u hu g => pw_left (d.betaL a ha) (U := d.L a w) (fun _ => True) (fun p q _ _ v hv t => by
        have hb : ∀ p q : d.kap w, (d.betaL a ha).m w p q = d.mac a ha w (d.e w) p.1.2 q.1.2 := fun p q => by
          show (if w ∈ d.T then _ else _) = _
          rw [if_neg hT]
        rw [hb]
        exact ((GlobalTheory.CompanionTheory.MatchId.mac_hecke hd ha hS (mem p) (mem q)).2 v hv t).1) (fun _ => trivial) m x x hu g
    have e2 : (d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.L a w) : LF a (n - a) w) =
        fun y => d.sgn a w * PositivityTheory.Rg.BcB.F.idem (d.L a w) y := rfl
    have e3 := mconv_smul (d.sgn a w) 1 (PositivityTheory.Rg.BcB.F.idem (d.L a w)) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w x x)
    simp only [one_mul, mul_one] at e3
    rw [e2]
    refine e3.trans ?_
    rw [hleft]
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent, pw_S d ha hT hS]
  rw [sum_kap_S d hT hS (fun x => d.sgn a w * (chi (d.μ w) y * (((d.X w).card : ℂ)⁻¹ *
    MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) m x x y)))]
  unfold MS.splitPlaceMackeyTraceTwist
  rw [sign_chi]
  simp only [← Finset.mul_sum]
  ring

theorem gU_S (hE : Unr E) (d : LocData E n) (hd : d.Ok) (hm : MOk d) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) (k : ℕ) :
    d.gU (k + 1) w = fun u : UL n w => MS.gpow (d.e w) k u.1 := by
  obtain ⟨hsp, hall, hlv⟩ := hm.S w hS
  obtain ⟨-, -, -, -, -, hf⟩ := hd.K' w hS
  have hU : UL n w = ⊤ := if_pos hsp
  have hKU : d.KU w = (d.K' w).subgroupOf (UL n w) := by
    unfold LocData.KU
    rw [if_neg hT, if_pos hS]
  have hg : d.g₀ w = fun y => d.e w y.1 := by
    unfold LocData.g₀
    rw [if_neg hT, if_pos hS]
  unfold LocData.gU
  rw [hKU, hg]
  induction k with
  | zero =>
    funext y
    have hidx : ((d.K' w).subgroupOf (UL n w)).relIndex (KL n w) ≠ 0 :=
      GlobalTheory.CompanionTheory.FmPowP.relIndex_ne_of_open hlv.1 (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w)
    exact GlobalTheory.CompanionTheory.MatchPow.conv_unit hlv.2.1 hidx (f := fun y : UL n w => d.e w y.1) (fun k hk x => by
      have h2 : (k : GLw n w) ∈ d.K' w := Subgroup.mem_subgroupOf.1 hk
      simpa using hf.2.2.2 1 (Subgroup.one_mem _) _ h2 x.1) y
  | succ k ih =>
    show lconv _ (lpow _ _ (k + 1)) = _
    rw [ih]
    funext u
    have h := congrFun (GlobalTheory.CompanionTheory.CtMulSplit.lconv_eq_gconv hU (fun y : UL n w => d.e w y.1)
      (fun v : UL n w => MS.gpow (d.e w) k (v : GLw n w))) u.1
    rw [GlobalTheory.CompanionTheory.CtMulSplit.toSub_val hU] at h
    simp only [GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU] at h
    exact h

theorem match_S (hMS : MS.MatchSplitPlace) (hE : Unr E) (d : LocData E n) (hd : d.Ok) (hm : MOk d) {a : ℕ} (ha : a ≤ n) (m : ℕ)
    {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : Match n a (n - a) w (d.μ w) (d.gU (m + 1) w)
      (((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w) := by
  obtain ⟨hsp, hall, hlv⟩ := hm.S w hS
  obtain ⟨ho, hle, hN, hX, hun, hf⟩ := hd.K' w hS
  rw [gU_S hE d hd hm hT hS, tr_S d hd ha hT hS]
  exact hMS E hE n a w hsp hall (d.μ w) (d.K' w) ho hle hN hlv (d.X w) hX hun (d.e w) hf ha m

end SPlace

section BadPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tr_Bad (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∉ d.S₀) (hB : w ∈ d.Bad)
    (m : ℕ) : ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w = d.fix a w := by
  have hP : w ∉ d.P := by simp [LocData.P, hT, hS]
  have hlev : d.lev a w = d.L a w := by
    simp only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_right _ hB)]
  obtain ⟨ho, hle⟩ := GlobalTheory.CompanionTheory.MatchId.L_ok hd ha (Finset.mem_union_right _ hB)
  have hs : ∀ k, (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).s w = PositivityTheory.Rg.BcB.F.idem (d.L a w) := by
    intro k
    induction k with
    | zero =>
      show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
      rw [hlev]
    | succ k ih =>
      show mconv ((d.betaL a ha).s w) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).s w) = _
      rw [ih]
      show mconv (PositivityTheory.Rg.BcB.F.idem (d.lev a w)) _ = _
      rw [hlev]
      exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_idem ho hle
  unfold LM.tr
  rw [if_neg hP]
  show mconv ((d.fixL a).s w) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).s w) = _
  rw [hs]
  have e : (d.fixL a).s w = d.fix a w := by
    show (if w ∈ d.Bad then d.fix a w else _) = _
    rw [if_pos hB]
  rw [e]
  exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right ho hle _ fun u hu g => ((hd.fix a ha w hB).2 u hu g).2

theorem gU_Bad (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∉ d.S₀) (hB : w ∈ d.Bad) (k : ℕ) :
    d.gU k w = lpow (d.KB w) (lone (d.KB w)) k := by
  have hKU : d.KU w = d.KB w := by
    unfold LocData.KU
    rw [if_neg hT, if_neg hS, if_pos hB]
  have hg : d.g₀ w = lone (d.KB w) := by
    unfold LocData.g₀
    rw [if_neg hT, if_neg hS, hKU]
  unfold LocData.gU
  rw [hKU, hg]

end BadPlace

theorem matchLMB2 : MT.MatchT → MS.MatchSplitPlace → MB.MatchBadS → MB.MatchBadI → MB.FixIdem → IdemAlg → MatchLMB2 := by
  intro hMT hMS hBS hBI _ _ E _ _ _ hE n d hd hm a ha m w hw
  obtain ⟨d₁, d₂, d₃⟩ := hd.disj
  by_cases hT : w ∈ d.T
  · have hS : w ∉ d.S₀ := Finset.disjoint_left.1 d₁ hT
    have hB : w ∉ d.Bad := Finset.disjoint_left.1 d₂ hT
    have hμ : muAt d w = 1 := by
      unfold muAt
      rw [if_neg (by simp [hS, hB])]
    rw [hμ]
    exact matching_at_T hMT hE d hm ha m hT
  · by_cases hS : w ∈ d.S₀
    · have hμ : muAt d w = d.μ w := by
        unfold muAt
        rw [if_pos (Or.inl hS)]
      rw [hμ]
      exact match_S hMS hE d hd hm ha m hT hS
    · have hB : w ∈ d.Bad := by
        simpa [LocData.B, hT, hS] using hw
      rw [gU_Bad d hT hS hB, tr_Bad d hd ha hT hS hB]
      by_cases hsp : IsSplitAt w
      · have hμ : muAt d w = d.μ w := by
          unfold muAt
          rw [if_pos (Or.inr ⟨hB, hsp⟩)]
        obtain ⟨hlv, hfix⟩ := hm.badS w hB hsp
        rw [hμ, hfix a ha]
        exact hBS E n a ha w hsp (d.μ w) (d.KB w) hlv (m + 1)
      · have hμ : muAt d w = 1 := by
          unfold muAt
          rw [if_neg (by simp [hS, hsp])]
        obtain ⟨k, hk, hlv, hmem, hfix⟩ := hm.badI w hB hsp
        rw [hμ, hfix a ha]
        exact hBI E hE w hsp n a (n - a) k (Nat.add_sub_of_le ha) hk (d.KB w) hlv hmem (m + 1)

end GlobalTheory.CompanionTheory.MatchLMB2

end
