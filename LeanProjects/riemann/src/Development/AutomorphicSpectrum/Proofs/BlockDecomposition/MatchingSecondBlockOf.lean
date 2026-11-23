import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMPlaces

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcN.F2 (mconv phi3 gconv leviOf IsHk)
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem L_open_le (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, e, h₁, h₂⟩ := hd.L a ha w hw
  rw [e]
  refine ⟨?_, Subgroup.prod_mono h₁.2.1 h₂.2.1⟩
  rw [Subgroup.coe_prod]
  exact h₁.1.prod h₂.1

theorem stabilizerDilationWeights_dualIsotropicVector (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∉ d.T) (hw : w ∈ d.S₀ ∪ d.Bad)
    (m : ℕ) : (pw (d.betaL a ha) m).s w = idem (d.L a w) := by
  have hl : d.lev a w = d.L a w := by simp [LocData.lev, hT, hw]
  obtain ⟨ho, hle⟩ := L_open_le d hd ha hw
  induction m with
  | zero => show idem (d.lev a w) = _; rw [hl]
  | succ m ih =>
    show PositivityTheory.Rg.BcN.F2.mconv (idem (d.lev a w)) ((pw (d.betaL a ha) m).s w) = _
    rw [ih, hl]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_idem ho hle

theorem tr_bad (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.Bad) (m : ℕ) :
    ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w = d.fix a w := by
  have hT : w ∉ d.T := fun h => Finset.disjoint_left.1 hd.disj.2.1 h hw
  have hS : w ∉ d.S₀ := fun h => Finset.disjoint_left.1 hd.disj.2.2 h hw
  have hP : w ∉ d.P := by simp [LocData.P, hT, hS]
  have hw' : w ∈ d.S₀ ∪ d.Bad := Finset.mem_union_right _ hw
  obtain ⟨ho, hle⟩ := L_open_le d hd ha hw'
  have e : ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w =
      PositivityTheory.Rg.BcN.F2.mconv (d.fix a w) ((pw (d.betaL a ha) m).s w) := by
    unfold LM.tr
    rw [if_neg hP]
    show PositivityTheory.Rg.BcN.F2.mconv (if w ∈ d.Bad then d.fix a w else idem (d.lev a w)) _ = _
    rw [if_pos hw]
  rw [e, stabilizerDilationWeights_dualIsotropicVector d hd ha hT hw' m]
  exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right ho hle _ fun u hu g => ((hd.fix a ha w hw).2 u hu g).2

theorem gU_bad (d : LocData E n) (hd : d.Ok) {w : Pl E} (hw : w ∈ d.Bad) (k : ℕ) :
    d.gU k w = U.lpow (d.KB w) (U.lone (d.KB w)) k := by
  have hT : w ∉ d.T := fun h => Finset.disjoint_left.1 hd.disj.2.1 h hw
  have hS : w ∉ d.S₀ := fun h => Finset.disjoint_left.1 hd.disj.2.2 h hw
  have hK : d.KU w = d.KB w := by simp [LocData.KU, hT, hS, hw]
  have hg : d.g₀ w = U.lone (d.KU w) := by simp [LocData.g₀, hT, hS]
  unfold LocData.gU
  rw [hg, hK]

theorem bad_split (hS : MB.MatchBadS) (d : LocData E n) (hd : d.Ok) (hm : MOk d) {a : ℕ} (ha : a ≤ n) {w : Pl E}
    (hw : w ∈ d.Bad) (hs : IsSplitAt w) (m : ℕ) :
    Match n a (n - a) w (d.μ w) (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w) := by
  rw [tr_bad d hd ha hw, gU_bad d hd hw, ((hm.badS w hw hs).2 a ha)]
  exact hS E n a ha w hs _ _ (hm.badS w hw hs).1 _

theorem bad_inert (hI : MB.MatchBadI) (hU : Unr E) (d : LocData E n) (hd : d.Ok) (hm : MOk d) {a : ℕ} (ha : a ≤ n)
    {w : Pl E} (hw : w ∈ d.Bad) (hs : ¬ IsSplitAt w) (m : ℕ) :
    Match n a (n - a) w 1 (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w) := by
  obtain ⟨k, hk, hl, hc, hf⟩ := hm.badI w hw hs
  rw [tr_bad d hd ha hw, gU_bad d hd hw, hf a ha]
  exact hI E hU w hs n a (n - a) k (Nat.add_sub_cancel' ha) hk _ hl hc _

theorem mconv_mul_mul {a b : ℕ} {w : Pl E} (r s : ℂ) (u v : GLw a w × GLw b w → ℂ) :
    mconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * mconv u v y := by
  funext y
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem lconv_mul_mul {w : Pl E} (r s : ℂ) (u v : UL n w → ℂ) :
    lconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * lconv u v y := by
  funext y
  unfold lconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem mconv_left {a b : ℕ} {w : Pl E} {u v : GLw a w × GLw b w → ℂ} {l : GLw a w × GLw b w}
    (hu : ∀ m, u (l * m) = u m) (m : GLw a w × GLw b w) : mconv u v (l * m) = mconv u v m := by
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.CtMulSplit.hint_left _ l]
  congr 1
  funext z
  rw [hu, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

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

theorem sum_diag (d : LocData E n) {a : ℕ} {w : Pl E} (f g : d.kap w → LF a (n - a) w) (x : d.kap w) :
    ∑ z, mconv (d.diag f x z) (g z) = mconv (f x) (g x) := by
  refine (Finset.sum_eq_single x ?_ ?_).trans ?_
  · intro z _ hz
    have h : d.diag f x z = 0 := if_neg (Ne.symm hz)
    rw [h]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_zero_left _
  · simp
  · have h : d.diag f x x = f x := if_pos rfl
    rw [h]

section S0

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

def chi (d : LocData E n) (a : ℕ) (w : Pl E) (m : GLw a w × GLw (n - a) w) : ℂ :=
  (d.μ w (Matrix.GeneralLinearGroup.det m.1 ^ (n - a) * Matrix.GeneralLinearGroup.det m.2 ^ a) : ℂˣ)

theorem chi_ne (m : GLw a w × GLw (n - a) w) : chi d a w m ≠ 0 := Units.ne_zero _

theorem chi_mul (x y : GLw a w × GLw (n - a) w) : chi d a w (x * y) = chi d a w x * chi d a w y := by
  unfold chi
  rw [← Units.val_mul, ← map_mul]
  congr 2
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
  exact mul_mul_mul_comm _ _ _ _

theorem sign_chi (m : GLw a w × GLw (n - a) w) :
    (d.μ w ((-1) ^ (a * (n - a)) * Matrix.GeneralLinearGroup.det m.1 ^ (n - a) *
      Matrix.GeneralLinearGroup.det m.2 ^ a) : ℂ) = d.sgn a w * chi d a w m := by
  unfold LocData.sgn chi
  rw [mul_assoc, map_mul, Units.val_mul]

theorem index_set_at_S0 (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.idx w = {∅} ×ˢ d.X w := by
  simp [LocData.idx, hT, hS]

theorem sum_over_index_set_S0 (hT : w ∉ d.T) (hS : w ∈ d.S₀) {M : Type} [AddCommMonoid M] (F : GLw n w → M) :
    ∑ x : d.kap w, F x.1.2 = ∑ x ∈ d.X w, F x := by
  have := Finset.sum_coe_sort (d.idx w) (fun p => F p.2)
  rw [this, index_set_at_S0 d hT hS, Finset.sum_product]
  simp

theorem mem_X (hT : w ∉ d.T) (hS : w ∈ d.S₀) (x : d.kap w) : x.1.2 ∈ d.X w := by
  have h : ∀ p ∈ d.idx w, p.2 ∈ d.X w := by
    rw [index_set_at_S0 d hT hS]
    exact fun p hp => (Finset.mem_product.1 hp).2
  exact h _ x.2

theorem mackey_matrix_at_S0 (hT : w ∉ d.T) (x y : d.kap w) :
    (d.betaL a ha).m w x y = fun m => ((d.X w).card : ℂ)⁻¹ *
      (chi d a w m * phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 y.1.2 m) := by
  funext m
  have h1 : (d.betaL a ha).m w x y = d.mac a ha w (d.e w) x.1.2 y.1.2 := by
    simp [LocData.betaL, hT]
  rw [h1]
  unfold LocData.mac Tail.phiMu
  rw [sign_chi]
  have hs : d.sgn a w ≠ 0 := Units.ne_zero _
  rw [mul_inv]
  field_simp

theorem mackey_powers_at_S0 (hT : w ∉ d.T) (hS : w ∈ d.S₀) (k : ℕ) (x y : d.kap w) :
    (pw (d.betaL a ha) k).m w x y = fun m => ((d.X w).card : ℂ)⁻¹ *
      (chi d a w m * MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k x.1.2 y.1.2 m) := by
  induction k generalizing x y with
  | zero => exact mackey_matrix_at_S0 d ha hT x y
  | succ k ih =>
    funext m
    show (∑ z, mconv ((d.betaL a ha).m w x z) ((pw (d.betaL a ha) k).m w z y)) m = _
    rw [Finset.sum_apply]
    have step : ∀ z : d.kap w, mconv ((d.betaL a ha).m w x z) ((pw (d.betaL a ha) k).m w z y) m =
        ((d.X w).card : ℂ)⁻¹ * ((d.X w).card : ℂ)⁻¹ * (chi d a w m *
          mconv (phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z.1.2)
            (MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z.1.2 y.1.2) m) := fun z => by
      rw [mackey_matrix_at_S0 d ha hT, ih]
      have e := congrFun (mconv_mul_mul (w := w) ((d.X w).card : ℂ)⁻¹ ((d.X w).card : ℂ)⁻¹
        (fun m => chi d a w m * phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z.1.2 m)
        (fun m => chi d a w m * MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z.1.2 y.1.2 m)) m
      rw [e, GlobalTheory.CompanionTheory.CtMulSplit.mconv_twist _ (chi_ne d) (chi_mul d)]
    simp only [step]
    rw [sum_over_index_set_S0 d hT hS (fun z => ((d.X w).card : ℂ)⁻¹ * ((d.X w).card : ℂ)⁻¹ * (chi d a w m *
      mconv (phi3 (Nat.add_sub_of_le ha) w (d.e w) x.1.2 z)
        (MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k z y.1.2) m))]
    show _ = ((d.X w).card : ℂ)⁻¹ * (chi d a w m * (((d.X w).card : ℂ)⁻¹ * ∑ z ∈ d.X w, mconv _ _ m))
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring

theorem mpow_left (hd : d.Ok) (hS : w ∈ d.S₀) (k : ℕ) {x y : GLw n w} (hx : x ∈ d.X w) (hy : y ∈ d.X w)
    {l : GLw a w × GLw (n - a) w} (hl : l ∈ leviOf (Nat.add_sub_of_le ha) w (d.K' w)) (m : GLw a w × GLw (n - a) w) :
    MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k x y (l * m) =
      MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) k x y m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd.K' w hS
  have hΦ : ∀ x ∈ d.X w, ∀ y ∈ d.X w, ∀ m, phi3 (Nat.add_sub_of_le ha) w (d.e w) x y (l * m) =
      phi3 (Nat.add_sub_of_le ha) w (d.e w) x y m := fun x hx y hy m => by
    have h1l : (1 : GLw a w × GLw (n - a) w) ∈ leviOf (Nat.add_sub_of_le ha) w (d.K' w) := by
      show blk (Nat.add_sub_of_le ha) w 1 0 ∈ d.K' w
      rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, map_one]
      exact (d.K' w).one_mem
    have := (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_locally_constant E n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) h1 h2 h3 (d.X w) h4 h5
      (d.e w) h6 x hx y hy).2.2 l hl 1 h1l m
    rwa [mul_one] at this
  induction k generalizing y m with
  | zero => exact hΦ x hx y hy m
  | succ k ih =>
    show ((d.X w).card : ℂ)⁻¹ * ∑ z ∈ d.X w, mconv _ _ (l * m) = ((d.X w).card : ℂ)⁻¹ * ∑ z ∈ d.X w, mconv _ _ m
    congr 1
    exact Finset.sum_congr rfl fun z hz => mconv_left (hΦ x hx z hz) m

theorem trace_at_S0_matches (hd : d.Ok) (hT : w ∉ d.T) (hS : w ∈ d.S₀) (m : ℕ) :
    ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w =
      MS.splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w (d.μ w) (d.X w) (d.e w) m := by
  have hP : w ∈ d.P := by simp [LocData.P, hS]
  have hw' : w ∈ d.S₀ ∪ d.Bad := Finset.mem_union_left _ hS
  have hl : d.lev a w = d.L a w := by simp [LocData.lev, hT, hw']
  obtain ⟨ho, hle⟩ := L_open_le d hd ha hw'
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (pw (d.betaL a ha) m)).m w x x =
      fun y => d.sgn a w * (((d.X w).card : ℂ)⁻¹ * (chi d a w y *
        MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) m x.1.2 x.1.2 y)) := fun x => by
    have hf : (d.fixL a).m w = d.diag (fun _ y => d.sgn a w * idem (d.L a w) y) := by
      show d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) = _
      simp only [if_neg hT, hl]
      rfl
    have e1 : ((d.fixL a).mul (pw (d.betaL a ha) m)).m w x x =
        mconv (fun y => d.sgn a w * idem (d.L a w) y) ((pw (d.betaL a ha) m).m w x x) := by
      show ∑ z, mconv ((d.fixL a).m w x z) ((pw (d.betaL a ha) m).m w z x) = _
      rw [hf]
      exact sum_diag d _ (fun z => (pw (d.betaL a ha) m).m w z x) x
    have e2 := mconv_mul_mul (w := w) (d.sgn a w) 1 (idem (d.L a w)) ((pw (d.betaL a ha) m).m w x x)
    simp only [one_mul, mul_one] at e2
    have hinv : ∀ u ∈ d.L a w, ∀ g, (pw (d.betaL a ha) m).m w x x (u * g) = (pw (d.betaL a ha) m).m w x x g := by
      intro u hu g
      have hu' := hd.LS a ha w hS u hu
      have hc : chi d a w u = 1 := by
        unfold chi
        rw [hu'.2]
        rfl
      rw [mackey_powers_at_S0 d ha hT hS]
      show ((d.X w).card : ℂ)⁻¹ * (chi d a w (u * g) * _) = ((d.X w).card : ℂ)⁻¹ * (chi d a w g * _)
      rw [chi_mul, hc, one_mul, mpow_left d ha hd hS m (mem_X d hT hS x) (mem_X d hT hS x) hu'.1]
    have e3 : mconv (idem (d.L a w)) ((pw (d.betaL a ha) m).m w x x) = (pw (d.betaL a ha) m).m w x x :=
      GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left ho hle _ hinv
    rw [e1, e2, e3]
    funext y
    rw [mackey_powers_at_S0 d ha hT hS]
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent]
  rw [sum_over_index_set_S0 d hT hS (fun x => d.sgn a w * (((d.X w).card : ℂ)⁻¹ * (chi d a w y *
    MS.mpow (d.X w) (phi3 (Nat.add_sub_of_le ha) w (d.e w)) m x x y)))]
  unfold MS.splitPlaceMackeyTraceTwist
  rw [sign_chi, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem unitary_function_powers_S0 (hU : Unr E) (hd : d.Ok) (hm : MOk d) (hT : w ∉ d.T) (hS : w ∈ d.S₀) (k : ℕ) :
    d.gU (k + 1) w = fun u : UL n w => MS.gpow (d.e w) k (u : GLw n w) := by
  obtain ⟨hs, hall, hlev⟩ := hm.S w hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd.K' w hS
  have hUT : UL n w = ⊤ := eq_top_iff.2 fun g _ => hall g
  have hK : d.KU w = (d.K' w).subgroupOf (UL n w) := by simp [LocData.KU, hT, hS]
  have hg : d.g₀ w = fun y => d.e w y.1 := by simp [LocData.g₀, hT, hS]
  unfold LocData.gU
  rw [hg, hK]
  have hidx : ((d.K' w).subgroupOf (UL n w)).relIndex (KL n w) ≠ 0 :=
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hlev.1 (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hU n w)
  induction k with
  | zero =>
    funext y
    refine GlobalTheory.CompanionTheory.MatchPow.conv_unit hlev.2.1 hidx (f := fun y : UL n w => d.e w y.1) (fun k hk x => ?_) y
    exact by
      have := h6.2.2.2 1 (d.K' w).one_mem k.1 hk x.1
      simpa using this
  | succ k ih =>
    have e := GlobalTheory.CompanionTheory.CtMulSplit.lconv_eq_gconv hUT (fun y : UL n w => d.e w y.1)
      (lpow ((d.K' w).subgroupOf (UL n w)) (fun y => d.e w y.1) (k + 1))
    funext y
    have e2 := congrFun e y.1
    rw [GlobalTheory.CompanionTheory.CtMulSplit.toSub_val hUT] at e2
    show lconv _ _ y = _
    rw [e2, ih]
    show _ = gconv _ _ _
    congr 1
    · funext z
      show d.e w (toSub (UL n w) z).1 = _
      rw [GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hUT]
    · funext z
      show MS.gpow (d.e w) k (toSub (UL n w) z).1 = _
      rw [GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hUT]

theorem matching_at_S0 (hMS : MS.MatchSplitPlace) (hU : Unr E) (hd : d.Ok) (hm : MOk d) (hT : w ∉ d.T) (hS : w ∈ d.S₀) (m : ℕ) :
    Match n a (n - a) w (d.μ w) (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w) := by
  obtain ⟨hs, hall, hlev⟩ := hm.S w hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd.K' w hS
  rw [trace_at_S0_matches d ha hd hT hS, unitary_function_powers_S0 d hU hd hm hT hS]
  exact hMS E hU n a w hs hall _ _ h1 h2 h3 hlev _ h4 h5 _ h6 ha m

end S0

section T

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

theorem index_set_at_T (hT : w ∈ d.T) : d.idx w = Finset.univ ×ˢ {1} := by
  simp [LocData.idx, hT]

theorem sum_kap_alt (hT : w ∈ d.T) {M : Type} [AddCommMonoid M] (F : Finset (Fin (n / 2)) → M) :
    ∑ x : d.kap w, F x.1.1 = ∑ s, F s := by
  have := Finset.sum_coe_sort (d.idx w) (fun p => F p.1)
  rw [this, index_set_at_T d hT, Finset.sum_product]
  simp

abbrev cc (d : LocData E n) (w : Pl E) : ↥(d.c w).support → ℂ := fun j => d.c w j.1

abbrev xx (d : LocData E n) (w : Pl E) : ↥(d.c w).support → Fin n → ℤ := fun j => j.1

theorem qT_eq (s : Finset (Fin (n / 2))) :
    d.qT a w s = fun y => (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
      MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s y := by
  funext y
  unfold LocData.qT MT.entT
  by_cases h : LocData.admitted n a s
  · have h' : MT.admitted n a s := ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
    rw [dif_pos h, dif_pos h', Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Tail.dc2
    ring
  · have h' : ¬ MT.admitted n a s := fun h' => h ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2.1, h'.2.2.2.2⟩
    rw [dif_neg h, dif_neg h', mul_zero]

theorem mpow_scale {b : ℕ} (r : ℂ) (u : GLw a w × GLw b w → ℂ) (k : ℕ) :
    MT.mpow w (fun y => r * u y) k = fun y => r ^ k * MT.mpow w u k y := by
  induction k with
  | zero =>
    funext y
    simp [MT.mpow]
  | succ k ih =>
    show mconv _ (MT.mpow w _ k) = _
    rw [ih, mconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * mconv u (MT.mpow w u k) y
    ring

theorem lpow_scale (K : Subgroup (UL n w)) (r : ℂ) (g : UL n w → ℂ) (k : ℕ) :
    lpow K (fun y => r * g y) k = fun y => r ^ k * lpow K g k y := by
  induction k with
  | zero =>
    funext y
    simp [U.lpow]
  | succ k ih =>
    show lconv _ (lpow K _ k) = _
    rw [ih, lconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * lconv g (lpow K g k) y
    ring

theorem qT_hecke (s : Finset (Fin (n / 2))) : IsHecke (Tail.I2 a (n - a) w) (d.qT a w s) := by
  rw [qT_eq]
  exact GlobalTheory.CompanionTheory.MatchPow.isHecke_const_mul _ (GlobalTheory.CompanionTheory.MatchPow.entT_hecke n w _ a _ _ s)

theorem beta_m_alt (hT : w ∈ d.T) : (d.betaL a ha).m w = d.diag (fun x => d.qT a w x.1.1) := by
  funext x y
  simp [LocData.betaL, hT]

theorem powers_diagonal_at_T (hT : w ∈ d.T) (k : ℕ) (x y : d.kap w) :
    (pw (d.betaL a ha) k).m w x y = d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) x y := by
  induction k generalizing x y with
  | zero =>
    have h1 : ∀ s, MT.mpow w (d.qT a w s) 1 = d.qT a w s := fun s =>
      GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w) _
        fun u hu g => ((qT_hecke d s).2 u hu g).2
    show (d.betaL a ha).m w x y = _
    rw [beta_m_alt d ha hT]
    simp only [zero_add, h1]
  | succ k ih =>
    show ∑ z, mconv ((d.betaL a ha).m w x z) ((pw (d.betaL a ha) k).m w z y) = _
    rw [beta_m_alt d ha hT, sum_diag d _ (fun z => (pw (d.betaL a ha) k).m w z y), ih]
    by_cases h : x = y
    · have e1 : ∀ f : d.kap w → LF a (n - a) w, d.diag f x y = f x := fun f => if_pos h
      rw [e1, e1]
      rfl
    · have e1 : ∀ f : d.kap w → LF a (n - a) w, d.diag f x y = 0 := fun f => if_neg h
      rw [e1, e1]
      exact GlobalTheory.CompanionTheory.FmPowP.mconv_zero_right _

theorem trace_test_function_eq (hT : w ∈ d.T) (m : ℕ)
    (hH : ∀ s, ∀ u ∈ Tail.I2 a (n - a) w, ∀ g, MT.mpow w (d.qT a w s) (m + 1) (u * g) = MT.mpow w (d.qT a w s) (m + 1) g) :
    ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w = fun y => ∑ s, MT.mpow w (d.qT a w s) (m + 1) y := by
  have hP : w ∈ d.P := by simp [LocData.P, hT]
  have hl : d.lev a w = Tail.I2 a (n - a) w := by simp [LocData.lev, hT]
  have hf : (d.fixL a).m w = d.diag (fun _ => idem (Tail.I2 a (n - a) w)) := by
    show d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) = _
    simp only [if_pos hT, hl]
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (pw (d.betaL a ha) m)).m w x x = MT.mpow w (d.qT a w x.1.1) (m + 1) := fun x => by
    show ∑ z, mconv ((d.fixL a).m w x z) ((pw (d.betaL a ha) m).m w z x) = _
    rw [hf, sum_diag d _ (fun z => (pw (d.betaL a ha) m).m w z x), powers_diagonal_at_T d ha hT]
    have e1 : ∀ f : d.kap w → LF a (n - a) w, d.diag f x x = f x := fun f => if_pos rfl
    rw [e1]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w) _ (hH _)
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent]
  exact sum_kap_alt d hT (fun s => MT.mpow w (d.qT a w s) (m + 1) y)

theorem unitary_function_at_T (hT : w ∈ d.T) : d.g₀ w = fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
    ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) y := by
  have h : d.g₀ w = fun y => (d.c w).sum fun x t =>
      t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y := by
    unfold LocData.g₀
    rw [if_pos hT]
  rw [h]
  funext y
  rw [Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem matching_at_T (hMT : MT.MatchT) (hLin : MT.MatchLin) (hU : Unr E) (hm : MOk d) (hT : w ∈ d.T) (m : ℕ) :
    Match n a (n - a) w 1 (d.gU (m + 1) w) (((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w) := by
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (xx d w j) ∧ Cone (lOf (xx d w j)) := fun j => hx j.1 j.2
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  have hoU := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w (d.b w)
  have hoG := GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w
  obtain ⟨J', _, c', x', -, e1, e2⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs a
    hb hϖ (cc d w) (xx d w) hx' m
  have hHU : IsHecke (iwU n w (d.b w)) (lpow (iwU n w (d.b w))
      (fun γ => ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) γ) (m + 1)) := by
    rw [e1]
    exact GlobalTheory.CompanionTheory.MatchPow.isHecke_const_mul _ (GlobalTheory.CompanionTheory.MatchPow.isHecke_sum fun j =>
      GlobalTheory.CompanionTheory.MatchPow.isHecke_const_mul _ (GlobalTheory.CompanionTheory.MatchPow.fU_hecke hs _ _ _ hc))
  have hHE : ∀ s, IsHecke (Tail.I2 a (n - a) w) (MT.mpow w (MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s) (m + 1)) := fun s => by
    rw [e2]
    exact GlobalTheory.CompanionTheory.MatchPow.isHecke_const_mul _ (GlobalTheory.CompanionTheory.MatchPow.entT_hecke n w _ a _ _ s)
  have hHφ : IsHecke (Tail.I2 a (n - a) w) (fun y => MT.cR n a w (d.b w) ^ (m + 1) *
      ∑ s, MT.mpow w (MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s) (m + 1) y) :=
    GlobalTheory.CompanionTheory.MatchPow.isHecke_const_mul _ (GlobalTheory.CompanionTheory.MatchPow.isHecke_sum hHE)
  have hIne : (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hoU (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hs n hc))
  have hIR : (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * MT.cR n a w (d.b w) =
      (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) := by
    unfold MT.cR
    rw [GlobalTheory.CompanionTheory.MatchPow.relIndex_prod, Nat.cast_mul]
    field_simp
  have hq : ∀ s, MT.mpow w (d.qT a w s) (m + 1) = fun y =>
      (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) ^ (m + 1) *
        MT.mpow w (MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s) (m + 1) y := fun s => by
    rw [qT_eq, mpow_scale]
  have hLeft : ∀ s, ∀ u ∈ Tail.I2 a (n - a) w, ∀ g, MT.mpow w (d.qT a w s) (m + 1) (u * g) =
      MT.mpow w (d.qT a w s) (m + 1) g := fun s u hu g => by
    rw [hq]
    show _ * _ = _ * _
    rw [((hHE s).2 u hu g).1]
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hL := hLin E n a (n - a) w 1 Unit (fun _ => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1))
    (fun _ => lpow (iwU n w (d.b w)) (fun γ => ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) γ) (m + 1))
    (fun _ y => MT.cR n a w (d.b w) ^ (m + 1) * ∑ s, MT.mpow w (MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s) (m + 1) y)
    (fun _ => ⟨GlobalTheory.CompanionTheory.MatchPow.isHecke_continuous hoU hHU, hHU.1, GlobalTheory.CompanionTheory.MatchPow.isHecke_continuous hoG hHφ, hHφ.1⟩)
    (fun _ => hMT E hU w hs n a ha (d.b w) hb (d.ϖ w) hϖ _ (cc d w) (xx d w) hx' (m + 1) (Nat.succ_pos m))
  have hG : d.gU (m + 1) w = fun γ => ∑ _j : Unit, (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      lpow (iwU n w (d.b w)) (fun γ => ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) γ) (m + 1) γ := by
    unfold LocData.gU
    rw [hKU, unitary_function_at_T d hT, lpow_scale]
    simp
  have hR : ((d.fixL a).mul (pw (d.betaL a ha) m)).tr d.P d.one w = fun y => ∑ _j : Unit,
      (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) * (MT.cR n a w (d.b w) ^ (m + 1) *
        ∑ s, MT.mpow w (MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s) (m + 1) y) := by
    rw [trace_test_function_eq d ha hT m hLeft]
    funext y
    simp only [hq, Finset.univ_unique, Finset.sum_singleton]
    rw [← mul_assoc, ← mul_pow, hIR, ← Finset.mul_sum]
  rw [hG, hR]
  exact hL

end T

theorem matchLMB2Of : MatchLMB2Of := by
  intro hMT hLin hMS hBS hBI _ _ E _ _ _ hU n d hd hm a ha m w hw
  have hdisj := hd.disj
  have hc : w ∈ d.T ∨ w ∈ d.S₀ ∨ w ∈ d.Bad := by
    simpa [LocData.B, or_assoc] using hw
  rcases hc with hT | hS | hB
  · have hS : w ∉ d.S₀ := fun h => Finset.disjoint_left.1 hdisj.1 hT h
    have hB : w ∉ d.Bad := fun h => Finset.disjoint_left.1 hdisj.2.1 hT h
    have hμ : muAt d w = 1 := by simp [muAt, hS, hB]
    rw [hμ]
    exact matching_at_T d ha hMT hLin hU hm hT m
  · have hT : w ∉ d.T := fun h => Finset.disjoint_left.1 hdisj.1 h hS
    have hμ : muAt d w = d.μ w := by simp [muAt, hS]
    rw [hμ]
    exact matching_at_S0 d ha hMS hU hd hm hT hS m
  · have hS : w ∉ d.S₀ := fun h => Finset.disjoint_left.1 hdisj.2.2 h hB
    by_cases hs : IsSplitAt w
    · have hμ : muAt d w = d.μ w := by simp [muAt, hB, hs]
      rw [hμ]
      exact bad_split hBS d hd hm ha hB hs m
    · have hμ : muAt d w = 1 := by simp [muAt, hS, hs]
      rw [hμ]
      exact bad_inert hBI hU d hd hm ha hB hs m

end GlobalTheory.CompanionTheory.MatchLMPlaces

end
