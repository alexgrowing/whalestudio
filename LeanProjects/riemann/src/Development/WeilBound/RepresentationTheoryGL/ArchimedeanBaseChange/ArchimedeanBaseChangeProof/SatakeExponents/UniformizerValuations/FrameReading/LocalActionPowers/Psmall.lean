import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpenLeIsCompact

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Psmall

section Generic

variable {P X : Type} [Group P] [Group X]

theorem hint_smul (K : Subgroup P) (c : ℂ) (v : P → ℂ) : hint K (fun m => c * v m) = c * hint K v := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    exact GlobalTheory.CompanionTheory.FamClP.hint_zero K
  · have hst : rStab (fun m => c * v m) = rStab v := by
      ext r
      show (∀ x, c * v (x * r) = c * v x) ↔ ∀ x, v (x * r) = v x
      exact forall_congr' fun x => mul_right_inj' hc
    unfold hint
    rw [hst, show (∑ᶠ q : P ⧸ (rStab v ⊓ K), c * v q.out) = c * ∑ᶠ q : P ⧸ (rStab v ⊓ K), v q.out from
      (smul_finsum c _).symm]
    ring

theorem act_left (K L : Subgroup P) (c : ℂ) (φ : P →* X) (G : X → ℂ) (z : X) (l : P) (hl : l ∈ L) :
    hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ l * φ m)) =
      hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) := by
  rw [← GlobalTheory.CompanionTheory.FamClP.hint_left K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) l]
  congr 1
  funext m
  have hmem : l * m ∈ L ↔ m ∈ L :=
    ⟨fun h => by simpa using L.mul_mem (L.inv_mem hl) h, fun h => L.mul_mem hl h⟩
  simp only [Set.indicator_apply, SetLike.mem_coe, hmem, map_mul, mul_assoc]

theorem idem_fix_iff (K L : Subgroup P) (hLK : L ≤ K) (hfin : L.relIndex K ≠ 0) (φ : P →* X) (G : X → ℂ) :
    (fun z => hint K (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m))) = G ↔
      ∀ l ∈ L, ∀ z, G (z * φ l) = G z := by
  constructor
  · intro h l hl z
    have h1 := congrFun h (z * φ l)
    have h2 := congrFun h z
    rw [← h1, ← h2]
    exact act_left K L _ φ G z l hl
  · intro h
    funext z
    have hu : (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m)) =
        fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m := by
      funext m
      by_cases hm : m ∈ L
      · simp [hm, h m hm z]
      · simp [hm]
    rw [hu]
    have hst : L ≤ rStab (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m) := by
      intro l hl x
      have : x * l ∈ L ↔ x ∈ L :=
        ⟨fun h' => by simpa using L.mul_mem h' (L.inv_mem hl), fun h' => L.mul_mem h' hl⟩
      simp only [Set.indicator_apply, SetLike.mem_coe, this]
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K L _ hLK hst hfin]
    have hone : ((((1 : P) : P ⧸ L)).out) ∈ L := by
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : P) : P ⧸ L))
      simpa using this
    rw [finsum_eq_single _ ((1 : P) : P ⧸ L)]
    · simp only [Set.indicator_apply, SetLike.mem_coe, hone, if_true]
      have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hfin
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · intro q hq
      have : q.out ∉ L := by
        intro hin
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using hin)
      simp [this]

end Generic

section Generic2

variable {P X : Type} [Group P] [Group X]

theorem hecke_eq [TopologicalSpace P] [IsTopologicalGroup P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (φ : P →* X)
    (f : P → ℂ) (G : X → ℂ) (hf : HasCompactSupport f) (hfK : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (hG : ∀ k ∈ K, ∀ z, G (z * φ k) = G z) :
    (fun z => hint K (fun m => f m * G (z * φ m))) = heckeVec ((rightReg ℂ X ℂ).comp φ) K f G := by
  funext z
  have hst : K ≤ rStab (fun m => f m * G (z * φ m)) := by
    intro k hk x
    show f (x * k) * G (z * φ (x * k)) = f x * G (z * φ x)
    rw [hfK k hk, map_mul, ← mul_assoc, hG k hk]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K K _ le_rfl hst (by simp), Subgroup.relIndex_self, Nat.cast_one, inv_one,
    one_mul]
  have hfin : (Function.support fun c : P ⧸ K => f c.out • ((rightReg ℂ X ℂ).comp φ) c.out G).Finite :=
    (GlobalTheory.TwTrLin.finite_out_support hK hf).subset (Function.support_smul_subset_left (fun c : P ⧸ K => f c.out)
      (fun c : P ⧸ K => ((rightReg ℂ X ℂ).comp φ) c.out G))
  unfold heckeVec
  rw [finsum_apply hfin]
  rfl

end Generic2

end PositivityTheory.Rg.BcB.F.FA.Psmall

namespace PositivityTheory.Rg.BcB.F.FA

open Psmall in
theorem actIdem_holds : ActIdem := by
  intro E _ _ _ a b w L G hL hLK _
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have hfin : L.relIndex (K2 a b w) ≠ 0 := GlobalTheory.relIndex_ne_zero_of_isOpen_le_isCompact _ _ hK hL hLK
  constructor
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embW a w).prodMap (embW b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embT a w).prodMap (embT b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩

end PositivityTheory.Rg.BcB.F.FA

namespace PositivityTheory.Rg.BcB.F.Tail

open PositivityTheory.Rg.BcB.F.FA.Psmall in
theorem actHecke_holds : ActHecke := by
  intro E _ _ _ a b w f G hf hfK
  have hK : IsOpen ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  constructor
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embW a w).prodMap (embW b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embT a w).prodMap (embT b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z

namespace Psmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem actP_smul_fun (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w (c • u) G = c • actP w u G := by
  funext z
  show hint _ (fun m => (c • u) m * _) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem actP_smul_vec (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w u (c • G) = c • actP w u G := by
  funext z
  show hint _ (fun m => u m * pairRt a b w m (c • G) z) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem actP_zero (w : Pl E) (G : H E a b → ℂ) : actP w (0 : GLw a w × GLw b w → ℂ) G = 0 := by
  funext z
  show hint _ (fun m => (0 : GLw a w × GLw b w → ℂ) m * _) = 0
  simp only [Pi.zero_apply, zero_mul]
  exact GlobalTheory.CompanionTheory.FamClP.hint_zero _

theorem locM_iter_smul (w : Pl E) {k : Type} [Fintype k] (c : ℂ) (M : k → k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) :
    (locM w fun x y => c • M x y)^[m] G = c ^ m • (locM w M)^[m] G := by
  have h1 : ∀ Y : k → H E a b → ℂ, (locM w fun x y => c • M x y) Y = c • locM w M Y := by
    intro Y
    funext x
    simp only [locM, actP_smul_fun, Pi.smul_apply, Finset.smul_sum]
  have h2 : ∀ (d : ℂ) (Y : k → H E a b → ℂ), locM w M (d • Y) = d • locM w M Y := by
    intro d Y
    funext x
    simp only [locM, Pi.smul_apply, actP_smul_vec, Finset.smul_sum]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h1, h2, smul_smul, pow_succ']

theorem locM_iter_diag (w : Pl E) {k : Type} [Fintype k] (q : k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) (x : k) :
    (locM w fun x y => if x = y then q x else 0)^[m] G x = (actP w (q x))^[m] (G x) := by
  have h1 : ∀ (Y : k → H E a b → ℂ) (x : k), (locM w fun x y => if x = y then q x else 0) Y x = actP w (q x) (Y x) := by
    intro Y x
    show ∑ y, actP w (if x = y then q x else 0) (Y y) = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg (Ne.symm hy), actP_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, ih]

end Psmall

open Psmall in
theorem locPow_holds : LocPow := by
  intro E _ _ _ a b w k _ U G m _ _
  constructor
  · intro c M hne h0
    apply hne
    rw [locM_iter_smul, h0, smul_zero]
  · intro q hne
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    funext x
    rw [locM_iter_diag]
    exact hall x

end PositivityTheory.Rg.BcB.F.Tail
