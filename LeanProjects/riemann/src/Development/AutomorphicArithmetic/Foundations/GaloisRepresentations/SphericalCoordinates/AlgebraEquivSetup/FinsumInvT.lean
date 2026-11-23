import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL satEig heckeVec IsSatVecGL)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E}

private theorem tj_eq {ϖ : w.adicCompletion E} {i : ℕ} (t : GLw n w)
    (ht : t.val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) :
    Tj ℂ n (Ov E w) ϖ i = dosetInd ℂ (KGL w n) t := by
  unfold Tj dosetInd
  congr 1
  ext y
  rw [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [e, Units.val_mul, Units.val_mul, ht]
    rfl
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, ht]
    rfl

private theorem dos_invT (t : GLw n w) (h : invT n _ t⁻¹ = t) (a : GLw n w) :
    dosetInd ℂ (KGL w n) t (invT n _ a) = dosetInd ℂ (KGL w n) t⁻¹ a := by
  have h' : invT n _ t = t⁻¹ := by
    have := congrArg (invT n _) h
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT'] at this
    exact this.symm
  have key : invT n _ a ∈ DoubleCoset.doubleCoset t (KGL w n : Set (GLw n w)) (KGL w n) ↔
      a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w n : Set (GLw n w)) (KGL w n) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨k, hk, l, hl, e⟩
      refine ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, ?_⟩
      have := congrArg (invT n _) e
      rwa [UpperTheory.Gal.CertificateRingHomMap.invT_invT', map_mul, map_mul, h'] at this
    · rintro ⟨k, hk, l, hl, rfl⟩
      exact ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, by rw [map_mul, map_mul, h]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w n : Set (GLw n w)) (KGL w n)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem dos_mul (t a k : GLw n w) (hk : k ∈ KGL w n) :
    dosetInd ℂ (KGL w n) t (a * k) = dosetInd ℂ (KGL w n) t a := by
  have key : a * k ∈ DoubleCoset.doubleCoset t (KGL w n : Set (GLw n w)) (KGL w n) ↔
      a ∈ DoubleCoset.doubleCoset t (KGL w n : Set (GLw n w)) (KGL w n) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨u, hu, l, hl, e⟩
      exact ⟨u, hu, l * k⁻¹, (KGL w n).mul_mem hl ((KGL w n).inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨u, hu, l, hl, rfl⟩
      exact ⟨u, hu, l * k, (KGL w n).mul_mem hl hk, by simp only [mul_assoc]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t (KGL w n : Set (GLw n w)) (KGL w n)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem finsum_invT {M : Type} [AddCommMonoid M] (F : GLw n w → M)
    (hF : ∀ a, ∀ k ∈ KGL w n, F (a * k) = F a) :
    ∑ᶠ c : GLw n w ⧸ KGL w n, F (invT n _ c.out) = ∑ᶠ c : GLw n w ⧸ KGL w n, F c.out := by
  let f : GLw n w ⧸ KGL w n → GLw n w ⧸ KGL w n := fun c => QuotientGroup.mk (invT n _ c.out)
  have hf : Function.Involutive f := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w n) (invT n _ c.out)
    simp only [f]
    rw [hk, map_mul, UpperTheory.Gal.CertificateRingHomMap.invT_invT', QuotientGroup.mk_mul_of_mem _ (UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL k.2),
      QuotientGroup.out_eq']
  have hshift : ∀ c, F (invT n _ c.out) = F ((Function.Involutive.toPerm f hf c).out) := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w n) (invT n _ c.out)
    rw [Function.Involutive.coe_toPerm]
    simp only [f]
    rw [hk, hF _ _ k.2]
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Function.Involutive.toPerm f hf) (f := fun c => F c.out)

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.tEig_of_thLoc :
    UpperTheory.Gal.CertificateRingHomMap.ThLoc → TEig := by
  intro hT E _ _ _ n hn x U w₀ Up V w hw hF i hi t ht z hz B hB g
  obtain ⟨-, s2, -, s4⟩ := V.form.sat w hw hF.2.1 hF.2.2.1 B hB
  obtain ⟨ϖ, hϖ, htd⟩ := ht
  obtain ⟨hT1, hT2⟩ := hT E n
  have hcen := V.kap.cen w hF.2.2.2.1 hF.2.2.2.2 z hz
  have hpow : ∀ (j : ℕ) (G : GUf E n), V.Φ (G * z ^ j) = (((V.κ.val w : ℂˣ) : ℂ)⁻¹ ^ j) • V.Φ G := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih =>
      intro G
      rw [pow_succ, ← mul_assoc, hcen, ih, smul_smul, pow_succ, mul_comm]
  have hinv : invT n _ t⁻¹ = t := by
    apply Units.ext
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_val, inv_inv, htd, Matrix.diagonal_transpose]
  set G' : GUf E n := UpperTheory.Gal.CertificateRingHomMap.th g * z ^ i with hG'
  let Fn : GLw n w → Module.Dual ℂ V.W.Sp := fun a => dosetInd ℂ (KGL w n) t a • V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a)
  have hFn : ∀ a, ∀ k ∈ KGL w n, Fn (a * k) = Fn a := fun a k hk => by
    have h1 : V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a * UpperTheory.Gal.CertificateRingHomMap.loc hw k) = V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a) :=
      congrFun (GlobalTheory.LGrp.mem_fixed.1 s2 k hk) _
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_mul _ _ _ hk, map_mul, ← mul_assoc, h1]
  have hterm : ∀ c : GLw n w ⧸ KGL w n, dosetInd ℂ (KGL w n) t⁻¹ c.out •
      V.Φ (UpperTheory.Gal.CertificateRingHomMap.th (g * (z ^ i)⁻¹ * UpperTheory.Gal.CertificateRingHomMap.loc hw c.out)) = Fn (invT n _ c.out) := fun c => by
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_invT t hinv, map_mul, map_mul, hT1, map_inv, map_pow, hT2 hn x w z hz, inv_pow, inv_inv]
  have hev := congrFun (s4 ϖ hϖ i hi) G'
  unfold heckeVec at hev
  rw [finsum_apply (GlobalTheory.LFun.finite_heckeVec (Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ i) _ V.Φ),
    UpperTheory.Gal.W2.Seed.tj_eq t htd] at hev
  rw [finsum_congr hterm, UpperTheory.Gal.W2.Seed.finsum_invT Fn hFn]
  refine Eq.trans hev ?_
  rw [Pi.smul_apply, hG', hpow, smul_smul]
  rfl
