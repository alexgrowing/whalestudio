import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BorelApproximation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZeroContDiffOnSupported

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LocOk

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G}

theorem hk_zero (K : Subgroup G) : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem hk_zero' (K : Subgroup G) : IsHecke K (fun _ : G => (0 : ℂ)) := hk_zero K

theorem hk_add {f g : G → ℂ} (hf : IsHecke K f) (hg : IsHecke K g) : IsHecke K (f + g) :=
  ⟨hf.1.add hg.1, fun k hk x => ⟨by simp only [Pi.add_apply, (hf.2 k hk x).1, (hg.2 k hk x).1],
    by simp only [Pi.add_apply, (hf.2 k hk x).2, (hg.2 k hk x).2]⟩⟩

theorem hk_cmul (c : ℂ) {f : G → ℂ} (hf : IsHecke K f) : IsHecke K (fun y => c * f y) :=
  ⟨hf.1.mono fun y hy h0 => hy (by simp [h0]), fun k hk x => ⟨by simp only [(hf.2 k hk x).1],
    by simp only [(hf.2 k hk x).2]⟩⟩

theorem hk_smul (c : ℂ) {f : G → ℂ} (hf : IsHecke K f) : IsHecke K (c • f) := hk_cmul c hf

theorem hk_sum {α : Type*} (s : Finset α) (F : α → G → ℂ) (h : ∀ x ∈ s, IsHecke K (F x)) :
    IsHecke K (fun y => ∑ x ∈ s, F x y) := by
  have := Finset.sum_induction F (IsHecke K) (fun f g hf hg => hk_add hf hg) (hk_zero K) h
  convert this using 1
  funext y
  rw [Finset.sum_apply]

theorem hk_fsum {α : Type*} (c : α →₀ ℂ) (F : α → ℂ → G → ℂ) (h : ∀ x t, IsHecke K (F x t)) :
    IsHecke K (fun y => c.sum fun x t => F x t y) :=
  hk_sum c.support (fun x => F x (c x)) fun x _ => h x (c x)

theorem hk_dite {p : Prop} [Decidable p] {g : p → G → ℂ} (hg : ∀ h, IsHecke K (g h)) :
    IsHecke K (fun y => if h : p then g h y else 0) := by
  by_cases hp : p
  · simpa only [dif_pos hp] using hg hp
  · simpa only [dif_neg hp] using hk_zero' K

theorem hcs_of_fin [IsTopologicalGroup G] [T2Space G] (hK : IsCompact (K : Set G)) {f : G → ℂ}
    (hf : FinDosetSupp K f) : HasCompactSupport f := by
  obtain ⟨S, hS⟩ := hf
  refine HasCompactSupport.intro (K := ⋃ s ∈ S, (fun p : G × G => p.1 * s * p.2) '' ((K : Set G) ×ˢ (K : Set G)))
    (S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)) fun g hg => ?_
  by_contra h0
  obtain ⟨s, hs, a, b, rfl⟩ := hS g h0
  exact hg (Set.mem_biUnion hs ⟨((a : G), (b : G)), ⟨a.2, b.2⟩, rfl⟩)

end Gen

section Levels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isOpen_KGL (w : Pl E) (a : ℕ) : IsOpen (GlobalTheory.LFun.KGL w a : Set (GLw a w)) := by
  rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem isCompact_KGL (w : Pl E) (a : ℕ) : IsCompact (GlobalTheory.LFun.KGL w a : Set (GLw a w)) :=
  GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a

theorem thL_KGL (a : ℕ) (w : Pl E) (k : GLw a w) (hk : k ∈ GlobalTheory.LFun.KGL w a) : thL a w k ∈ GlobalTheory.LFun.KGL w a := by
  unfold thL
  split_ifs
  · exact hk
  · exact GlobalTheory.CompanionTheory.IwFacts.thetaGL_mem_KGL w a hk

theorem thL_iw (a : ℕ) (w : Pl E) (k : GLw a w) (hk : k ∈ iwGL a w) : thL a w k ∈ iwGL a w := by
  unfold thL
  split_ifs
  · exact hk
  · exact GlobalTheory.CompanionTheory.IwFacts.thetaGL_mem_iwGL w a hk

theorem lev_K (a : ℕ) (w : Pl E) : IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (GlobalTheory.LFun.KGL w a) :=
  ⟨isOpen_KGL w a, le_rfl, thL_KGL a w⟩

theorem lev_iw (a : ℕ) (w : Pl E) : IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) :=
  ⟨GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _, GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a, thL_iw a w⟩

theorem prod_open_le {a b : ℕ} {w : Pl E} {K₁ : Subgroup (GLw a w)} {K₂ : Subgroup (GLw b w)}
    (h₁ : IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁) (h₂ : IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂) :
    IsOpen ((K₁.prod K₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ∧ K₁.prod K₂ ≤ K2 a b w :=
  ⟨by rw [Subgroup.coe_prod]; exact h₁.1.prod h₂.1, Subgroup.prod_mono h₁.2.1 h₂.2.1⟩

theorem idempotent_maximal_pair_indicator (a b : ℕ) (w : Pl E) :
    idem (K2 a b w) = ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)).indicator 1 := by
  unfold idem
  rw [Subgroup.relIndex_self, Nat.cast_one]
  rfl

abbrev IsLv {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : Prop :=
  ∃ K₁ : Subgroup (GLw a w), ∃ K₂ : Subgroup (GLw b w), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ ∧
    IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂ ∧ L = K₁.prod K₂

theorem idem_of_lv (h1 : IdemAlg) {a b : ℕ} {w : Pl E} {L : Subgroup (GLw a w × GLw b w)} (he : IsLv L) :
    IsHecke L (idem L) := by
  obtain ⟨K₁, K₂, h₁, h₂, rfl⟩ := he
  exact (h1 E a b w _ (prod_open_le h₁ h₂).1 (prod_open_le h₁ h₂).2).1

theorem maximal_pair_is_level (a b : ℕ) (w : Pl E) : IsLv (K2 a b w) := ⟨_, _, lev_K a w, lev_K b w, rfl⟩

theorem isTestFunction_of (h1 : IdemAlg) {a b : ℕ} (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (Q : Finset (Pl E))
    (hloc : ∀ w, ∃ L : Subgroup (GLw a w × GLw b w), IsLv L ∧ IsHecke L (φ w))
    (hout : ∀ w ∉ Q, φ w = idem (K2 a b w)) : IsTestP φ := by
  choose L hL hH using hloc
  choose K₁ K₂ h₁ h₂ he using hL
  let K₁' : ∀ w : Pl E, Subgroup (GLw a w) := fun w => if w ∈ Q then K₁ w else GlobalTheory.LFun.KGL w a
  let K₂' : ∀ w : Pl E, Subgroup (GLw b w) := fun w => if w ∈ Q then K₂ w else GlobalTheory.LFun.KGL w b
  have hcof : ∀ p : Pl E → Prop, (∀ w ∉ Q, p w) → ∀ᶠ w in Filter.cofinite, p w := fun p hp =>
    Filter.eventually_cofinite.2 (Q.finite_toSet.subset fun w hw => Classical.by_contradiction fun h => hw (hp w h))
  unfold IsTestP GlobalTheory.BCT.IsLevelFam GlobalTheory.BCT.IsTest
  refine ⟨K₁', K₂', ⟨fun w => ?_, hcof _ fun w hw => if_neg hw⟩, ⟨fun w => ?_, hcof _ fun w hw => if_neg hw⟩,
    fun w => ?_, hcof _ fun w hw => ?_⟩
  · by_cases hw : w ∈ Q
    · rw [show K₁' w = K₁ w from if_pos hw]; exact h₁ w
    · rw [show K₁' w = _ from if_neg hw]; exact lev_K a w
  · by_cases hw : w ∈ Q
    · rw [show K₂' w = K₂ w from if_pos hw]; exact h₂ w
    · rw [show K₂' w = _ from if_neg hw]; exact lev_K b w
  · show IsHecke ((K₁' w).prod (K₂' w)) (φ w)
    by_cases hw : w ∈ Q
    · rw [show K₁' w = K₁ w from if_pos hw, show K₂' w = K₂ w from if_pos hw, ← he w]; exact hH w
    · rw [show K₁' w = _ from if_neg hw, show K₂' w = _ from if_neg hw, hout w hw]
      exact idem_of_lv h1 (maximal_pair_is_level a b w)
  · rw [hout w hw, idempotent_maximal_pair_indicator]

end Levels

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem dcos_left {m : ℕ} {w : Pl E} (t k g : GLw m w) (hk : k ∈ iwGL m w) :
    dcos m w t (k * g) = dcos m w t g :=
  _root_.UpperTheory.Reformulated.B.BorelApproximation.dcos_left t k g hk

theorem dcos_right {m : ℕ} {w : Pl E} (t k g : GLw m w) (hk : k ∈ iwGL m w) :
    dcos m w t (g * k) = dcos m w t g :=
  _root_.UpperTheory.Reformulated.B.H23.dcos_right t k g hk

theorem isHecke_iwahori_pair_double_coset {a b : ℕ} (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    IsHecke (I2 a b w) (dc2 w ϖ x y) := by
  refine ⟨HasCompactSupport.intro ((GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w a (tdiag ϖ x)).prod
    (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w b (tdiag ϖ y))) fun m hm => ?_, fun k hk g => ?_⟩
  · simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_not] at hm
    rcases hm with h | h <;> simp [dc2, h]
  · obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    simp only [dc2, Prod.fst_mul, Prod.snd_mul]
    exact ⟨by rw [dcos_left _ _ _ hk1, dcos_left _ _ _ hk2], by rw [dcos_right _ _ _ hk1, dcos_right _ _ _ hk2]⟩

theorem ordL_of_v_one {w : Pl E} (x : w.adicCompletion E) (hx : Valued.v x = 1) : ordL x = 0 := by
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact one_ne_zero
  unfold ordL
  rw [dif_neg h0]
  have : WithZero.unzero h0 = 1 := WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, hx]; rfl)
  rw [this]
  rfl

theorem unifV {w : Pl E} (x : w.adicCompletion E) (h : ordL x = 1) : IsUnifV E w x := by
  unfold ordL at h
  by_cases h0 : Valued.v x = 0
  · rw [dif_pos h0] at h; exact absurd h (by norm_num)
  · rw [dif_neg h0] at h
    show Valued.v x = _
    rw [← WithZero.coe_unzero h0]
    congr 1
    have : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by omega
    rw [← this]
    rfl

theorem mu_det {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) {m : ℕ} (k : GLw m w)
    (hk : k ∈ GlobalTheory.LFun.KGL w m) : μ (GeneralLinearGroup.det k) = 1 :=
  hμ _ (ordL_of_v_one _ (GlobalTheory.BCT.AbsHalfInv.v_det_KGL hk))

theorem mu_left {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (k m : GLw a w × GLw b w) :
    μ ((-1) ^ (a * b) * GeneralLinearGroup.det (k * m).1 ^ b * GeneralLinearGroup.det (k * m).2 ^ a) =
      μ (GeneralLinearGroup.det k.1 ^ b * GeneralLinearGroup.det k.2 ^ a) *
        μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) := by
  rw [← map_mul]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
  ac_rfl

theorem mu_right {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (k m : GLw a w × GLw b w) :
    μ ((-1) ^ (a * b) * GeneralLinearGroup.det (m * k).1 ^ b * GeneralLinearGroup.det (m * k).2 ^ a) =
      μ (GeneralLinearGroup.det k.1 ^ b * GeneralLinearGroup.det k.2 ^ a) *
        μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) := by
  rw [← map_mul]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
  ac_rfl

theorem dgM_KGL {a b m : ℕ} (hh : a + b = m) (w : Pl E) (k : GLw a w × GLw b w) (hk : k ∈ K2 a b w) :
    GlobalTheory.BCT.CtLevel.dgM hh w k ∈ GlobalTheory.LFun.KGL w m := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
  obtain ⟨e1, f1⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h1
  obtain ⟨e2, f2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h2
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact GlobalTheory.BCT.CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ hh _ _ e1 e2 i j
  · rw [← map_inv]
    exact GlobalTheory.BCT.CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ hh _ _ f1 f2 i j

theorem maximal_pair_mem_levi {a b m : ℕ} (hh : a + b = m) (w : Pl E) (k : GLw a w × GLw b w) (hk : k ∈ K2 a b w) :
    k ∈ leviOf hh w (GlobalTheory.LFun.KGL w m) := by
  show blk hh w k 0 ∈ GlobalTheory.LFun.KGL w m
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
  exact dgM_KGL hh w k hk

end Place

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) {a : ℕ}

theorem lev_lv (hd : d.Ok) (ha : a ≤ n) (w : Pl E) : IsLv (d.lev a w) := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact ⟨_, _, lev_iw a w, lev_iw (n - a) w, rfl⟩
  · obtain ⟨L₁, L₂, hL, hL₁, hL₂⟩ := hd.L a ha w h2
    exact ⟨L₁, L₂, hL₁, hL₂, hL⟩
  · exact maximal_pair_is_level a (n - a) w

theorem lev₂_lv (hd : d.Ok) (ha : a ≤ n) (w : Pl E) : IsLv (d.lev₂ a w) := by
  unfold LocData.lev₂
  split_ifs with h2
  · obtain ⟨L₁, L₂, hL, hL₁, hL₂⟩ := hd.L a ha w h2
    exact ⟨L₁, L₂, hL₁, hL₂, hL⟩
  · exact maximal_pair_is_level a (n - a) w

theorem level_eq_iwahori_pair_at_bad_places {w : Pl E} (h : w ∈ d.T) : d.lev a w = I2 a (n - a) w := by
  unfold LocData.lev; rw [if_pos h]

theorem lev_S {w : Pl E} (hT : w ∉ d.T) (h : w ∈ d.S₀ ∪ d.Bad) : d.lev a w = d.L a w := by
  unfold LocData.lev; rw [if_neg hT, if_pos h]

theorem lev_out {w : Pl E} (hT : w ∉ d.T) (h : w ∉ d.S₀ ∪ d.Bad) : d.lev a w = K2 a (n - a) w := by
  unfold LocData.lev; rw [if_neg hT, if_neg h]

theorem lev₂_out {w : Pl E} (h : w ∉ d.S₀ ∪ d.Bad) : d.lev₂ a w = K2 a (n - a) w := by
  unfold LocData.lev₂; rw [if_neg h]

theorem out3 {w : Pl E} (hw : w ∉ d.T ∪ d.S₀ ∪ d.Bad) : w ∉ d.T ∧ w ∉ d.S₀ ∪ d.Bad := by
  simp only [Finset.mem_union, not_or] at hw ⊢
  tauto

theorem wirtinger_sub : d.P ⊆ d.T ∪ d.S₀ ∪ d.Bad := fun w hw => by
  simp only [LocData.P, Finset.mem_union] at hw ⊢
  tauto

theorem idemH (h1 : IdemAlg) (hd : d.Ok) (ha : a ≤ n) (w : Pl E) : IsHecke (d.lev a w) (idem (d.lev a w)) :=
  idem_of_lv h1 (lev_lv d hd ha w)

theorem idemH₂ (h1 : IdemAlg) (hd : d.Ok) (ha : a ≤ n) (w : Pl E) : IsHecke (d.lev₂ a w) (idem (d.lev₂ a w)) :=
  idem_of_lv h1 (lev₂_lv d hd ha w)

theorem diagH {w : Pl E} {K : Subgroup (GLw a w × GLw (n - a) w)} (f : d.kap w → LF a (n - a) w)
    (hf : ∀ z, IsHecke K (f z)) (x y : d.kap w) : IsHecke K (d.diag f x y) := by
  unfold LocData.diag
  split_ifs
  · exact hf x
  · exact hk_zero K

theorem lm_ok (h1 : IdemAlg) (hd : d.Ok) (ha : a ≤ n) (L : LM d.kap a (n - a)) (Q : Finset (Pl E)) (hQ : d.P ⊆ Q)
    (hm : ∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) (L.m w x y))
    (hs : ∀ w ∉ d.P, IsHecke (d.lev a w) (L.s w))
    (ht : ∀ w, IsHecke (d.lev₂ a w) (L.t w))
    (hso : ∀ w ∉ Q, L.s w = idem (K2 a (n - a) w))
    (hto : ∀ w ∉ Q, L.t w = idem (K2 a (n - a) w)) : L.Ok d.P := by
  refine ⟨fun x y => isTestFunction_of h1 _ Q (fun w => ⟨_, lev_lv d hd ha w, ?_⟩) fun w hw => ?_,
    isTestFunction_of h1 _ Q (fun w => ⟨_, lev₂_lv d hd ha w, ht w⟩) hto⟩
  · unfold LM.ent
    split_ifs with h
    · exact hm w h _ _
    · exact hs w h
  · unfold LM.ent
    rw [dif_neg fun h => hw (hQ h)]
    exact hso w hw

theorem kap_X {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) (x : d.kap w) : x.1.2 ∈ d.X w := by
  obtain ⟨p, hp⟩ := x
  have e : d.idx w = {∅} ×ˢ d.X w := by unfold LocData.idx; rw [if_neg hT, if_pos hS]
  rw [e] at hp
  exact (Finset.mem_product.1 hp).2

theorem kap_ne (hd : d.Ok) (w : Pl E) : Nonempty (d.kap w) := by
  by_cases hT : w ∈ d.T
  · exact ⟨⟨(∅, 1), by unfold LocData.idx; rw [if_pos hT]; simp⟩⟩
  · by_cases hS : w ∈ d.S₀
    · obtain ⟨x, ⟨hx, -⟩, -⟩ := (hd.K' w hS).2.2.2.2.1 1 (one_mem _)
      exact ⟨⟨(∅, x), by unfold LocData.idx; rw [if_neg hT, if_pos hS]; simp [hx]⟩⟩
    · exact ⟨⟨(∅, 1), by unfold LocData.idx; rw [if_neg hT, if_neg hS]; simp⟩⟩

theorem qT_H (w : Pl E) (s : Finset (Fin (n / 2))) : IsHecke (I2 a (n - a) w) (d.qT a w s) := by
  unfold LocData.qT
  exact hk_dite fun h => hk_fsum _ _ fun x t => hk_cmul _ (isHecke_iwahori_pair_double_coset _ _ _ _)

end Data

section Ops

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) {a : ℕ}

theorem mac_H (h2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) (hd : d.Ok) (ha : a ≤ n)
    {w : Pl E} (hw : w ∈ d.S₀) {x y : GLw n w} (hx : x ∈ d.X w) (hy : y ∈ d.X w) :
    IsHecke (d.L a w) (d.mac a ha w (d.e w) x y) := by
  obtain ⟨hO, hle, hN, hX, hU, hHk⟩ := hd.K' w hw
  obtain ⟨c1, -, -, -⟩ := h2 E n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) hO hle hN (d.X w) hX hU
  obtain ⟨-, hcs, hbi⟩ := c1 (d.e w) hHk x hx y hy
  have hLS := hd.LS a ha w hw
  have h1L := (hLS 1 (one_mem _)).1
  refine ⟨hcs.mono fun m hm h0 => hm ?_, fun k hk g => ?_⟩
  · simp only [LocData.mac, phiMu, h0, mul_zero]
  · obtain ⟨hkl, hkμ⟩ := hLS k hk
    have e1 := hbi k hkl 1 h1L g
    have e2 := hbi 1 h1L k hkl g
    rw [mul_one] at e1
    rw [one_mul] at e2
    constructor
    · simp only [LocData.mac, phiMu, e1, mu_left, hkμ, one_mul]
    · simp only [LocData.mac, phiMu, e2, mu_right, hkμ, one_mul]

theorem hc_H (h2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) {w : Pl E} (hg : d.Good w)
    (hu : ordL (d.ϖ w : w.adicCompletion E) = 1) (ha : a ≤ n) (j : ℕ) :
    IsHecke (K2 a (n - a) w) (d.hc a ha w j) := by
  obtain ⟨hs, -, -, -, hμ⟩ := hg
  have hϖ : IsUnifV E w (d.ϖ w : w.adicCompletion E) := unifV _ hu
  have hT := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j
  let F : GLw n w → ℂ := fun y => Tj ℂ n (Ov E w) (d.ϖ w : w.adicCompletion E) j ((toSub (UL n w) y : UL n w) : GLw n w)
  have hF : F = Tj ℂ n (Ov E w) (d.ϖ w : w.adicCompletion E) j := by
    funext y
    have hy : y ∈ UL n w := by unfold UL; rw [if_pos hs]; exact Subgroup.mem_top y
    simp only [F, toSub, dif_pos hy]
  have hHk : IsHk (GlobalTheory.LFun.KGL w n) F := by
    rw [hF]
    exact ⟨isOpen_KGL w n, isCompact_KGL w n, hcs_of_fin (isCompact_KGL w n) hT.2,
      fun k₁ hk₁ k₂ hk₂ g => hT.1 ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ g⟩
  obtain ⟨c1, c2, -, -⟩ := h2 E n a (n - a) (Nat.add_sub_of_le ha) w (GlobalTheory.LFun.KGL w n) (isOpen_KGL w n) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) {1} (by simp)
    (fun k hk => ⟨1, ⟨Finset.mem_singleton_self 1, by simpa using hk⟩, fun z hz => Finset.mem_singleton.1 hz.1⟩)
  obtain ⟨-, hcs, hbi⟩ := c1 F hHk 1 (Finset.mem_singleton_self 1) 1 (Finset.mem_singleton_self 1)
  have hct : ∀ m, ct (Nat.add_sub_of_le ha) w F m = phi3 (Nat.add_sub_of_le ha) w F 1 1 m := fun m => by
    simpa using c2 F hHk m
  have hval : ∀ m, d.hc a ha w j m = (d.sgn a w)⁻¹ * ((d.μ w ((-1) ^ (a * (n - a)) *
      GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
      phi3 (Nat.add_sub_of_le ha) w F 1 1 m) := fun m => by
    rw [← hct]
    rfl
  have hμK : ∀ k ∈ K2 a (n - a) w,
      d.μ w (GeneralLinearGroup.det k.1 ^ (n - a) * GeneralLinearGroup.det k.2 ^ a) = 1 := fun k hk => by
    obtain ⟨k1, k2⟩ := Subgroup.mem_prod.1 hk
    rw [map_mul, map_pow, map_pow, mu_det _ hμ _ k1, mu_det _ hμ _ k2, one_pow, one_pow, one_mul]
  have h1l := maximal_pair_mem_levi (Nat.add_sub_of_le ha) w 1 (one_mem _)
  refine ⟨hcs.mono fun m hm h0 => hm ?_, fun k hk g => ?_⟩
  · rw [hval, h0, mul_zero, mul_zero]
  · have e1 := hbi k (maximal_pair_mem_levi _ w k hk) 1 h1l g
    have e2 := hbi 1 h1l k (maximal_pair_mem_levi _ w k hk) g
    rw [mul_one] at e1
    rw [one_mul] at e2
    constructor
    · rw [hval, hval, mu_left, hμK k hk, one_mul, e1]
    · rw [hval, hval, mu_right, hμK k hk, one_mul, e2]

end Ops

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) {a : ℕ}

theorem eL_ok (h1 : IdemAlg) (hd : d.Ok) (ha : a ≤ n) : (d.eL a).Ok d.P :=
  lm_ok d h1 hd ha _ _ (wirtinger_sub d) (fun w _ x y => diagH d _ (fun _ => idemH d h1 hd ha w) x y)
    (fun w _ => idemH d h1 hd ha w) (fun w => idemH₂ d h1 hd ha w)
    (fun w hw => by show idem (d.lev a w) = _; rw [lev_out d (out3 d hw).1 (out3 d hw).2])
    (fun w hw => by show idem (d.lev₂ a w) = _; rw [lev₂_out d (out3 d hw).2])

theorem betaL_ok (h1 : IdemAlg) (h2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E)
    (hd : d.Ok) (ha : a ≤ n) : (d.betaL a ha).Ok d.P := by
  refine lm_ok d h1 hd ha _ _ (wirtinger_sub d) (fun w hw x y => ?_) (fun w _ => idemH d h1 hd ha w)
    (fun w => idemH₂ d h1 hd ha w)
    (fun w hw => by show idem (d.lev a w) = _; rw [lev_out d (out3 d hw).1 (out3 d hw).2])
    (fun w hw => by show idem (d.lev₂ a w) = _; rw [lev₂_out d (out3 d hw).2])
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [level_eq_iwahori_pair_at_bad_places d hT]
    exact diagH d _ (fun z => qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [lev_S d hT (Finset.mem_union_left _ hS)]
    exact mac_H d h2 hd ha hS (kap_X d hT hS x) (kap_X d hT hS y)

theorem fixL_ok (h1 : IdemAlg) (hd : d.Ok) (ha : a ≤ n) : (d.fixL a).Ok d.P := by
  refine lm_ok d h1 hd ha _ _ (wirtinger_sub d) (fun w hw x y => ?_) (fun w hw => ?_)
    (fun w => idemH₂ d h1 hd ha w) (fun w hw => ?_)
    (fun w hw => by show idem (d.lev₂ a w) = _; rw [lev₂_out d (out3 d hw).2])
  · show IsHecke _ (d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) x y)
    refine diagH d _ (fun _ => ?_) x y
    split_ifs
    · exact idemH d h1 hd ha w
    · exact hk_smul _ (idemH d h1 hd ha w)
  · show IsHecke _ (if w ∈ d.Bad then d.fix a w else idem (d.lev a w))
    split_ifs with hB
    · have hT : w ∉ d.T := fun h => hw (by simp [LocData.P, h])
      rw [lev_S d hT (Finset.mem_union_right _ hB)]
      exact hd.fix a ha w hB
    · exact idemH d h1 hd ha w
  · have hB : w ∉ d.Bad := fun h => hw (by simp [h])
    show (if w ∈ d.Bad then d.fix a w else idem (d.lev a w)) = _
    rw [if_neg hB, lev_out d (out3 d hw).1 (out3 d hw).2]

theorem hL_ok (h1 : IdemAlg) (h2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E)
    (hd : d.Ok) (ha : a ≤ n) {w₀ : Pl E} (hg : d.Good w₀) (j : ℕ) (intersection_update_fsHerm_neg_one : Bool) :
    (d.hL a ha w₀ j intersection_update_fsHerm_neg_one).Ok d.P := by
  have hH := hc_H d h2 hg (hd.unif w₀) ha j
  obtain ⟨-, hT0, hS0, hB0, -⟩ := hg
  have hSB0 : w₀ ∉ d.S₀ ∪ d.Bad := by simp [Finset.mem_union, hS0, hB0]
  have hl : d.lev a w₀ = K2 a (n - a) w₀ := lev_out d hT0 hSB0
  have hl₂ : d.lev₂ a w₀ = K2 a (n - a) w₀ := lev₂_out d hSB0
  have hQ : d.P ⊆ insert w₀ (d.T ∪ d.S₀ ∪ d.Bad) := fun w hw => Finset.mem_insert_of_mem (wirtinger_sub d hw)
  have hout : ∀ w ∉ insert w₀ (d.T ∪ d.S₀ ∪ d.Bad), w ≠ w₀ ∧ w ∉ d.T ∪ d.S₀ ∪ d.Bad := fun w hw =>
    ⟨fun h => hw (h ▸ Finset.mem_insert_self _ _), fun h => hw (Finset.mem_insert_of_mem h)⟩
  cases intersection_update_fsHerm_neg_one
  · refine lm_ok d h1 hd ha _ _ hQ (fun w _ x y => diagH d _ (fun _ => idemH d h1 hd ha w) x y) (fun w _ => ?_)
      (fun w => idemH₂ d h1 hd ha w) (fun w hw => ?_)
      (fun w hw => by show idem (d.lev₂ a w) = _; rw [lev₂_out d (out3 d (hout w hw).2).2])
    · show IsHecke _ (Function.update (fun w => idem (d.lev a w)) w₀ (d.hc a ha w₀ j) w)
      by_cases h : w = w₀
      · subst h; rw [Function.update_self, hl]; exact hH
      · rw [Function.update_of_ne h]; exact idemH d h1 hd ha w
    · show Function.update (fun w => idem (d.lev a w)) w₀ (d.hc a ha w₀ j) w = _
      rw [Function.update_of_ne (hout w hw).1, lev_out d (out3 d (hout w hw).2).1 (out3 d (hout w hw).2).2]
  · refine lm_ok d h1 hd ha _ _ hQ (fun w _ x y => diagH d _ (fun _ => idemH d h1 hd ha w) x y)
      (fun w _ => idemH d h1 hd ha w) (fun w => ?_)
      (fun w hw => by show idem (d.lev a w) = _; rw [lev_out d (out3 d (hout w hw).2).1 (out3 d (hout w hw).2).2])
      (fun w hw => ?_)
    · show IsHecke _ (Function.update (fun w => idem (d.lev₂ a w)) w₀ (d.hc a ha w₀ j) w)
      by_cases h : w = w₀
      · subst h; rw [Function.update_self, hl₂]; exact hH
      · rw [Function.update_of_ne h]; exact idemH₂ d h1 hd ha w
    · show Function.update (fun w => idem (d.lev₂ a w)) w₀ (d.hc a ha w₀ j) w = _
      rw [Function.update_of_ne (hout w hw).1, lev₂_out d (out3 d (hout w hw).2).2]

end Fam

end PositivityTheory.Rg.BcB.F.LocOk

namespace PositivityTheory.Rg.BcB.F

theorem locOk (h1 : IdemAlg) (h2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) : LocOk := by
  intro E _ _ _ n d hd a ha
  refine ⟨LocOk.kap_ne d hd, LocOk.betaL_ok d h1 h2 hd ha, LocOk.fixL_ok d h1 hd ha, fun L hL => ?_⟩
  rcases hL with rfl | ⟨w, j, intersection_update_fsHerm_neg_one, hg, rfl⟩
  · exact LocOk.eL_ok d h1 hd ha
  · exact LocOk.hL_ok d h1 h2 hd ha hg j intersection_update_fsHerm_neg_one

end PositivityTheory.Rg.BcB.F

end
