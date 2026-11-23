import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

section Basic

variable {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]

theorem apply_mem_idealV (τ : A →+* Module.End K V) {J : Ideal A} {a : A} (ha : a ∈ J) (v : V) :
    τ a v ∈ idealV τ J :=
  Submodule.mem_iSup_of_mem (⟨a, ha⟩ : J) (LinearMap.mem_range_self _ v)

theorem idealV_le (τ : A →+* Module.End K V) {J : Ideal A} {W : Submodule K V}
    (h : ∀ a ∈ J, ∀ v, τ a v ∈ W) : idealV τ J ≤ W :=
  iSup_le fun a => by
    rintro _ ⟨v, rfl⟩
    exact h a a.2 v

theorem apply_mem_of_mul_mem (τ : A →+* Module.End K V) {U J₁ : Ideal A} {t : A}
    (h : ∀ a ∈ U, a * t ∈ J₁) {μ : V} (hμ : μ ∈ idealV τ U) : τ t μ ∈ idealV τ J₁ := by
  have : idealV τ U ≤ (idealV τ J₁).comap (τ t) := idealV_le τ fun a ha v => by
    rw [Submodule.mem_comap]
    show τ t (τ a v) ∈ _
    rw [← Module.End.mul_apply, ← map_mul, mul_comm]
    exact apply_mem_idealV τ (h a ha) v
  exact this hμ

end Basic

section Coord

variable {K A V k : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V] [Field k]
  [Algebra k K] [Algebra k A]

theorem coord_vanish (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (Θ : Fin r → V →ₗ[K] K)
    (l : A →ₗ[k] k)
    (hΘ : ∀ s s' a, Θ s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    {U : Ideal A} (hl : ∀ a ∈ U, l a = 0) (s : Fin r) {y : V} (hy : y ∈ idealV τ U) :
    Θ s y = 0 := by
  have : idealV τ U ≤ LinearMap.ker (Θ s) := idealV_le τ fun u hu v => by
    have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
        (LinearMap.ker (Θ s)).comap (τ u) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨a, s'⟩, rfl⟩
      show Θ s (τ u (τ a (x s'))) = 0
      rw [← Module.End.mul_apply, ← map_mul, hΘ, hl _ (U.mul_mem_right a hu)]
      simp
    exact h (hspan v)
  exact this hy

theorem exists_coords (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (χ : A →ₐ[k] k)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    (v : V) : ∃ d : Fin r → K, v - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) := by
  have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
      Submodule.span K (Set.range x) ⊔ idealV τ (RingHom.ker χ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, s⟩, rfl⟩
    have ha : a - algebraMap k A (χ a) ∈ RingHom.ker χ := by
      simp [RingHom.mem_ker]
    have e : τ a (x s) = algebraMap k K (χ a) • x s + τ (a - algebraMap k A (χ a)) (x s) := by
      rw [map_sub, LinearMap.sub_apply, hc]
      abel
    show τ a (x s) ∈ _
    rw [e]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)) (apply_mem_idealV τ ha _)
  obtain ⟨p, hp, μ, hμ, e⟩ := Submodule.mem_sup.1 (h (hspan v))
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hp
  refine ⟨d, ?_⟩
  rw [hd, ← e, add_sub_cancel_left]
  exact hμ

theorem exists_of_mem_idealV (τ : A →+* Module.End K V) {J₁ J : Ideal A} {t : A}
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) {y : V} (hy : y ∈ idealV τ J) :
    ∃ z, y - τ t z ∈ idealV τ J₁ := by
  have h : idealV τ J ≤ LinearMap.range (τ t) ⊔ idealV τ J₁ := idealV_le τ fun a ha v => by
    obtain ⟨c, hc'⟩ := hJt a ha
    have e : τ a v = τ t (algebraMap k K c • v) + τ (a - algebraMap k A c * t) v := by
      rw [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hc, map_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (apply_mem_idealV τ hc' v)
  obtain ⟨p, ⟨z, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h hy)
  refine ⟨z, ?_⟩
  rw [← e, add_sub_cancel_left]
  exact hw

end Coord

section Local

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {L : C.I → AddSubgroup V} {k A : Type} [Field k] [Algebra k K] [CommRing A] [Algebra k A]

theorem exists_local (τ : A →+* Module.End K V) {r : ℕ} (χ : A →ₐ[k] k) {J₁ J : Ideal A} {t : A}
    (l : A →ₗ[k] k) (hL : IsBun C L)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y) {i : C.I}
    (hF : FreeAt C k τ L r i)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁)
    (hmt : ∀ a ∈ RingHom.ker χ, a * t ∈ J₁) (hl : ∀ a ∈ J₁, l a = 0) (hlt : l t = 1) :
    ∃ P : V →ₗ[K] V, (∀ y ∈ idealV τ J, y - τ t (P y) ∈ idealV τ J₁) ∧
      (∀ w ∈ idealV τ J₁, P w = 0) ∧
      (∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ)) ∧
      ∀ y ∈ L i, P y ∈ L i := by
  obtain ⟨x, Θ', hx, hΘ', hint, hspan⟩ := hF
  have hΘ := hΘ' l
  set Θ := Θ' l with hΘdef
  have hW1 : ∀ s, ∀ w ∈ idealV τ J₁, Θ s w = 0 := fun s w hw =>
    coord_vanish τ x Θ l hΘ hspan hl s hw
  let P : V →ₗ[K] V := ∑ s, (Θ s).smulRight (x s)
  have hPa : ∀ y, P y = ∑ s, Θ s y • x s := fun y => by
    simp [P, LinearMap.sum_apply]
  have hΘT : ∀ s s', Θ s (τ t (x s')) = if s = s' then 1 else 0 := fun s s' => by
    rw [hΘ, hlt, map_one]
  have hP0 : ∀ w ∈ idealV τ J₁, P w = 0 := fun w hw => by
    rw [hPa]
    exact Finset.sum_eq_zero fun s _ => by rw [hW1 s w hw, zero_smul]

  have hPc : ∀ (d : Fin r → K) (y : V), y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ →
      P y = ∑ s, d s • x s := fun d y hy => by
    have h1 : ∀ s, Θ s y = d s := fun s => by
      have h2 := hW1 s _ hy
      rw [map_sub, map_sum, sub_eq_zero] at h2
      rw [h2]
      simp [hΘT]
    rw [hPa]
    exact Finset.sum_congr rfl fun s _ => by rw [h1 s]
  have hT : ∀ z, ∃ d : Fin r → K, z - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) ∧
      τ t z - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := fun z => by
    obtain ⟨d, hd⟩ := exists_coords τ x χ hc hspan z
    refine ⟨d, hd, ?_⟩
    have := apply_mem_of_mul_mem τ hmt hd
    simpa [map_sub, map_sum] using this
  have hPT : ∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ) := fun z => by
    obtain ⟨d, h1, h2⟩ := hT z
    rw [hPc d _ h2, ← neg_sub]
    exact neg_mem h1
  refine ⟨P, fun y hy => ?_, hP0, hPT, fun y hy => ?_⟩
  · obtain ⟨z, hz⟩ := exists_of_mem_idealV τ hc hJt hy
    obtain ⟨d, -, h2⟩ := hT z
    have h3 : y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := by
      have := add_mem hz h2
      simpa using this
    rw [hPc d _ h3]
    simpa [map_sum] using h3
  · rw [hPa]
    exact sum_mem fun s _ => smul_mem_of_isBun C hL i (hint l s y hy) (hx s)

end Local

theorem subDeg_step : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A] [Algebra k A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (J₁ J : Ideal A) (t : A) (l : A →ₗ[k] k), IsBun C L → (∀ a, IsHom C L L (τ a)) → (∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x) → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FreeAt C k τ L r i) → J₁ ≤ J → t ∈ J → (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) → (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) → (∀ a ∈ J₁, l a = 0) → l t = 1 → subDeg C L (idealV τ J) = subDeg C L (idealV τ J₁) + deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  intro K _ C V _ _ _ L k A _ _ _ _ τ r χ J₁ J t l hL hτ hc _ hF hJ ht hJt hmt hl hlt
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hW : idealV τ J₁ ≤ idealV τ J :=
    idealV_le τ fun a ha v => apply_mem_idealV τ (hJ ha) v
  choose P hP1 hP2 hP3 hP4 using fun i =>
    exists_local C τ χ l hL hc (hF i) hJt hmt hl hlt
  let g : idealV τ J →ₗ[K] V ⧸ idealV τ (RingHom.ker χ) :=
    (idealV τ (RingHom.ker χ)).mkQ ∘ₗ P i₀ ∘ₗ (idealV τ J).subtype
  have hg : ∀ y : idealV τ J, g y = Submodule.Quotient.mk (P i₀ y) := fun y => rfl
  have hgT : ∀ z, g ⟨τ t z, apply_mem_idealV τ ht z⟩ = Submodule.Quotient.mk z := fun z => by
    rw [hg]
    exact (Submodule.Quotient.eq _).2 (hP3 i₀ z)
  have hS : ShortExact C (sub C L (idealV τ J₁)) (sub C L (idealV τ J))
      (quot C L (idealV τ (RingHom.ker χ))) (Submodule.inclusion hW) g := by
    refine ⟨Submodule.inclusion_injective hW, fun y => ⟨fun h => ?_, ?_⟩, fun z => ?_,
      fun i x => Iff.rfl, fun i z => ⟨?_, ?_⟩⟩
    · rw [hg, Submodule.Quotient.mk_eq_zero] at h
      have h2 := hP1 i₀ y y.2
      have h3 := apply_mem_of_mul_mem τ hmt h
      have h4 : (y : V) ∈ idealV τ J₁ := by simpa using add_mem h2 h3
      exact ⟨⟨y, h4⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      rw [hg]
      show Submodule.Quotient.mk (P i₀ (w : V)) = 0
      rw [hP2 i₀ w w.2]
      simp
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨_, hgT z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨τ t z, apply_mem_idealV τ ht z⟩, hτ t i z hz, hgT z⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨P i y, hP4 i y hy, ?_⟩
      have h1 : P i₀ (y : V) = P i₀ (τ t (P i y)) := by
        have := hP2 i₀ _ (hP1 i y y.2)
        rwa [map_sub, sub_eq_zero] at this
      rw [hg, h1]
      exact ((Submodule.Quotient.eq _).2 (hP3 i₀ (P i y))).symm
  have hB := (SubQuot.isBun_sub_quot K C V L (idealV τ J) hL).1
  exact (deg_shortExact K C _ _ _ _ _ _ _ _ hB hS).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep
