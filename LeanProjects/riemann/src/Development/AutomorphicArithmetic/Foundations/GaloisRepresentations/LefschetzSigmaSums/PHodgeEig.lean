import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.HodgeCoh UpperTheory.Gal.CertificateRingHomMap in
theorem UpperTheory.Gal.LocalSmoothExtension.hodgeEig_of :
    HodgeTr → KSProj → HodgeFin → UnifBound → HExpInj → CoeffOcc → EigOf → HopWord → UpperTheory.Gal.G3.HodgeGood → HodgeEig := by
  intro hTr hProj hFin hUnif hInj hCo hEig hWord hGood
  intro p _ D G L hSc lam hlam
  classical
  let κ : ((D.F →+* ℂ) → Fin G.n → ℕ) → Fin D.a → (Fin G.n → ℕ) → ℕ := fun lam' i₀ h =>
    if H : IsHExp (D.tau i₀) (epsOf D) lam' h then (hTr p D G L lam' i₀ h H).choose else 0
  obtain ⟨k, hkB⟩ := hUnif D.F G.n (Fin D.a) D.tau (epsOf D) lam κ
  refine ⟨k, ?_⟩
  intro gb hgb T N σ i₀ h hH J ψ θ f hψ hf hS i
  have hκ : (hTr p D G L (conjWt σ lam) i₀ h hH).choose ≤ k := by
    have := hkB σ i₀ h hH
    simpa only [κ, dif_pos hH] using this
  obtain ⟨c, hc⟩ := (hTr p D G L (conjWt σ lam) i₀ h hH).choose_spec k hκ
  obtain ⟨hproj, d, hd⟩ := hProj p D G L hSc gb k T N
  have hcT := hc hSc gb hgb T N d hd
  have hG : ∀ a b, (UpperTheory.Gal.G3.hodge ℂ a b).Good := fun a b => hGood ℂ a b
  haveI hFD : ∀ b : Fin (d + 1), FiniteDimensional ℂ (hodgeH (qAt T N) (h i) b.1) :=
    fun b => hFin _ _ d hd hproj _ _
  have hWd : ∀ (a b : ℕ) (w : List J), T.X.IsFn (T.lev N) (wordFn (L.KN N.1) ψ w f) ∧
      hk T N (wordFn (L.KN N.1) ψ w f) a b = (w.map fun j => hk T N (ψ j) a b).prod * hk T N f a b := by
    intro a b w
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).1 w
    rw [T.K_eq] at this
    exact this
  have hPoly : ∀ (a b : ℕ) (s : List J →₀ ℂ), T.X.IsFn (T.lev N) (polyFn (L.KN N.1) ψ s f) ∧
      hk T N (polyFn (L.KN N.1) ψ s f) a b = wop (fun j => hk T N (ψ j) a b) s * hk T N f a b := by
    intro a b s
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).2 s
    rw [T.K_eq] at this
    exact this
  obtain ⟨hcomm, V, _, _, _, ξ, hξ, hspec⟩ := hS
  have hcm : ∀ (b : Fin (d + 1)) (j j' : J) (w : List J),
      hk T N (ψ j) (h i) b.1 * hk T N (ψ j') (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 =
        hk T N (ψ j') (h i) b.1 * hk T N (ψ j) (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 := by
    intro b j j' w
    have h1 := (hWd (h i) b.1 (j :: j' :: w)).2
    have h2 := (hWd (h i) b.1 (j' :: j :: w)).2
    rw [hcomm j j' w, h2] at h1
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using h1.symm
  obtain ⟨s, hs1, hs⟩ := hEig (Fin (d + 1)) J (fun b => hodgeH (qAt T N) (h i) b.1)
    (fun b j => hk T N (ψ j) (h i) b.1) (fun b => hk T N f (h i) b.1) θ hcm
  have hne : wop θ s ≠ 0 := by rw [hs1]; exact one_ne_zero
  obtain ⟨a, hgoodF, hdT⟩ := hspec s hne
  have hFfn := (hPoly 0 0 (wmul a s)).1
  have hy := fun y => hcT V ξ hξ _ hFfn hgoodF y
  have hocc := hCo d G.n
    (fun a' => ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
      LinearMap.trace ℂ _ (hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) a' b ∘ₗ cutD T N c a' b)) _ h
    (hInj D.F G.n (D.tau i₀) (epsOf D) (conjWt σ lam) h (fun τ => hlam _) hH) hdT hy i
  obtain ⟨b, hb, hb0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hocc
  have hne0 : hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) (h i) b ≠ 0 := by
    intro e
    apply hb0
    rw [e, LinearMap.zero_comp, map_zero, mul_zero]
  rw [(hPoly _ _ _).2, wop_wmul, mul_assoc] at hne0
  have hu : wop (fun j => hk T N (ψ j) (h i) b) s * hk T N f (h i) b ≠ 0 :=
    fun e => hne0 (by rw [e, mul_zero])
  obtain ⟨x, hx0, hx⟩ := hs ⟨b, Finset.mem_range.1 hb⟩ hu
  exact ⟨b, x, hx0, hx⟩
