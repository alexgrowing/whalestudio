import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintEqOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeAct

theorem hint_mul_const {H : Type} [Group H] (K : Subgroup H) (v : H → ℂ) (c : ℂ) :
    hint K (fun z => v z * c) = hint K v * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hS : rStab (fun z => v z * c) = rStab v := by
    ext k
    constructor
    · intro hk z
      exact mul_right_cancel₀ hc (hk z)
    · intro hk z
      show v (z * k) * c = v z * c
      rw [hk z]
  unfold hint
  rw [hS, mul_assoc]
  congr 1
  have e := smul_finsum c (fun q : H ⧸ rStab v ⊓ K => v q.out)
  simp only [smul_eq_mul] at e
  rw [mul_comm, e]
  exact finsum_congr fun q => mul_comm _ _

theorem relIndex_eq_card {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let φ : {x // x ∈ X} → K ⧸ K'.subgroupOf K := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ K'.subgroupOf K)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
      exact Subtype.ext ((hX y.1 (hXK _ y.2)).unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  show Nat.card (K ⧸ K'.subgroupOf K) = _
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finsum_left {G : Type} [Group G] (K' : Subgroup G) (φ : G → ℂ) (hφ : ∀ g, ∀ k ∈ K', φ (g * k) = φ g) (x : G) :
    ∑ᶠ q : G ⧸ K', φ (x * q.out) = ∑ᶠ q : G ⧸ K', φ q.out := by
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K')))
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K')) q = ((x * q.out : G) : G ⧸ K') := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (x * q.out)
  show φ (x * q.out) = φ ((x * q.out : G) : G ⧸ K').out
  rw [hs, hφ _ _ s.2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ind_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W)
    (u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom))
    (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    u.1.1 (blk h w m Y * g) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) • ρ m (u.1.1 g) := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) (GlobalTheory.LeviFubini.levH_blk h w m Y)
    simpa [GlobalTheory.LeviFubini.levH] using this
  have := GlobalTheory.SmGL.parInd_law _ _ u ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ g
  rw [hl] at this
  rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m]
  simpa using this

theorem hk_ind_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W), ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y)) := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX W _ _ ρ f hf u hu x hx lw
  have hfr : ∀ g, ∀ k ∈ K', f (g * k) = f g := fun g k hk => by
    simpa using hf.2.2.2 1 K'.one_mem k hk g
  have hur : ∀ g, ∀ k ∈ K', u.1.1 (g * k) = u.1.1 g := fun g k hk => by
    have h1 : GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ k u = u := (hu ⟨k, hk⟩).trans (one_smul ℂ u)
    exact congrArg (fun v : GlobalTheory.SmGL.IndSp _ _ => v.1.1 g) h1

  set φ : GLw n w → ℂ := fun g => f (x⁻¹ * g) * lw (u.1.1 g) with hφdef
  have hφr : ∀ g, ∀ k ∈ K', φ (g * k) = φ g := fun g k hk => by
    simp only [hφdef]
    rw [← mul_assoc, hfr _ k hk, hur g k hk]
  have hφc : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun g => f (x⁻¹ * g) := hf.2.2.1.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    exact h1.mul_right
  have hcard : K'.relIndex (GlobalTheory.LFun.KGL w n) = X.card := relIndex_eq_card _ K' X hXK hX
  have hX0 : X.card ≠ 0 := by
    obtain ⟨z, ⟨hz, -⟩, -⟩ := hX 1 (GlobalTheory.LFun.KGL w n).one_mem
    exact (Finset.card_pos.2 ⟨z, hz⟩).ne'
  have hX0' : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX0

  let Ψ : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] ℂ :=
    { toFun := fun v => lw (v.1.1 x)
      map_add' := fun v v' => map_add lw _ _
      map_smul' := fun c v => map_smul lw c _ }
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen f hf.2.2.1
  have e1 : lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ᶠ q : GLw n w ⧸ K', φ (x * q.out) := by
    show Ψ (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u) = _
    unfold hk
    refine (Ψ.toAddMonoidHom.map_finsum (hfin.subset fun q hq h0 => hq (by
      have h0' : f q.out = 0 := h0
      show f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u = 0
      rw [h0', zero_smul]))).trans ?_
    refine finsum_congr fun q => ?_
    show Ψ (f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u) = _
    rw [map_smul]
    simp only [hφdef, inv_mul_cancel_left]
    rfl
  have e2 := GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le (GlobalTheory.LFun.KGL w n) K' φ hle (fun k hk g => hφr g k hk)
    (by rw [hcard]; exact hX0) (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen φ hφc)
  have e3 := GlobalTheory.T.hecke_coset_sum_compact E n a b h w K' hopen hle hnorm X hXK hX φ hφr hφc
  rw [hcard] at e2
  have e4 : ∑ᶠ q : GLw n w ⧸ K', φ q.out =
      ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m =>
        hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
    have := e2.symm.trans e3
    exact mul_left_cancel₀ (inv_ne_zero hX0') this
  rw [e1, finsum_left K' φ hφr x, e4]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  funext m
  have e5 : (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      φ (blk h w m (Multiplicative.toAdd Y) * y)) = fun Y =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y) *
        (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * lw (ρ m (u.1.1 y))) := by
    funext Y
    simp only [hφdef]
    rw [ind_blk h w ρ u m _ y, map_smul, smul_eq_mul, mul_assoc]
  rw [e5, hint_mul_const]
  unfold phi3
  ring

end GlobalTheory.CompanionTheory.HeckeAct
