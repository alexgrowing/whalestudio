import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)
open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

private theorem map_oneP {p : ℕ} [Fact p.Prime] (σ : ℂ ≃+* ℂ) (G : HTGroup p) (x : Gr G 1) :
    σ (oneP G x) = oneP G x := by
  by_cases h : x ∈ (Kp G : Set (Gr G 1))
  · simp [oneP, Set.indicator_of_mem h]
  · simp [oneP, Set.indicator_of_notMem h]

private theorem dTrace_conj {p : ℕ} [Fact p.Prime] (hH : HeckeTraceSemi) (σ : ℂ ≃+* ℂ) (G : HTGroup p)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (ξ' : Representation ℂ (G.Cˣ × ℚˣ) V') (e : V ≃+ V') (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) (K : Subgroup G.GAf) (f : G.GAf → ℂ) :
    dTrace G ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (dTrace G ξ K f (Kp G) (oneP G)) := by
  have hterm : ∀ B : DForm G, B.trace ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (B.trace ξ K f (Kp G) (oneP G)) := by
    intro B
    have h := hH σ (grp G B.β) (G.GAf × Gr G 1) V V' (ξ.comp (grp G B.β).subtype) (ξ'.comp (grp G B.β).subtype) e hs
      (fun g x => hi g.1 x) B.emb (K.prod (Kp G)) (fun h => f h.1 * oneP G h.2)
    have hF : (fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2)) = fun h => σ (f h.1) * oneP G h.2 := by
      funext h
      rw [map_mul, map_oneP]
    rw [hF] at h
    exact h
  unfold dTrace
  have hm := σ.toAddEquiv.map_finsum (fun q : DFCls G => (Quot.out q).trace ξ K f (Kp G) (oneP G))
  calc _ = ∑ᶠ q : DFCls G, σ ((Quot.out q).trace ξ K f (Kp G) (oneP G)) := finsum_congr fun q => hterm _
    _ = _ := hm.symm

theorem UpperTheory.Gal.LocalSmoothExtension.specConj_of :
    TraceSemi → ConjRep → HeckeTraceSemi → GoodConj → SchWConj → PolyFnConj → SpecConj := by
  intro hT hCR hH hG hSW hP σ p _ D G L lam K J ψ θ f hS
  obtain ⟨hcomm, V, i1, i2, i3, ξ, hwt, hsp⟩ := hS
  obtain ⟨V', j1, j2, j3, ξ', e, hse, hint⟩ := hCR σ (G.Cˣ × ℚˣ) V ξ
  have hPf := hP σ G.GAf J K ψ f
  refine ⟨fun j j' w => ?_, V', j1, j2, j3, ξ', ?_, ?_⟩
  · rw [hPf.1, hPf.1, hcomm]
  · intro B y h1 h2
    rw [hSW, ← hwt B y h1 h2]
    exact hT σ V V' e hse (ξ y.1) (ξ' y.1) (fun x => hint y.1 x)
  · intro s' hs'
    obtain ⟨s, rfl⟩ : ∃ s : List J →₀ ℂ, wmap σ.toRingHom s = s' := by
      refine ⟨wmap σ.symm.toRingHom s', ?_⟩
      ext w
      simp [wmap]
    have hw : σ (wop θ s) = wop (fun j => σ (θ j)) (wmap σ.toRingHom s) :=
      UpperTheory.Gal.CertificateRingHomMap.map_wop_wmap σ.toRingHom σ.toRingHom (fun _ => rfl) θ s
    have hne : wop θ s ≠ 0 := by
      intro h0
      apply hs'
      rw [← hw, h0, map_zero]
    obtain ⟨a, hgood, htr⟩ := hsp s hne
    refine ⟨wmap σ.toRingHom a, ?_⟩
    have hc : polyFn K (fun j g => σ (ψ j g)) (wmul (wmap σ.toRingHom a) (wmap σ.toRingHom s)) (fun g => σ (f g)) =
        fun g => σ (polyFn K ψ (wmul a s) f g) := by
      rw [← hPf.2.2, hPf.2.1]
    rw [hc]
    refine ⟨hG σ p G K _ hgood, ?_⟩
    rw [dTrace_conj hH σ G ξ ξ' e hse hint]
    exact fun h0 => htr ((map_eq_zero σ).1 h0)
