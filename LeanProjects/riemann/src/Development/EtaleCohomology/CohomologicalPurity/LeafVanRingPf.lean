import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl

theorem sub_C_mem_X {σ R : Type} [CommRing R] (f : MvPolynomial σ R) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p n _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)

theorem chart_nbhd {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ)
    (hc : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJ] at hf
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff f)
    have h1 : ψ (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) ∈ I.map φ := by
      rw [← hJ]; exact Ideal.mem_map_of_mem _ (sub_C_mem_X f)
    have h2 : φ a ∈ I.map φ := by
      have := sub_mem (add_mem (hc a) (sub_mem hf h1)) (0 : I.map φ).2
      rw [map_sub, ← ha] at this
      simpa using this
    have h3 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := sub_C_mem_X f
    rwa [← ha, h3, map_zero, sub_zero] at this
  · intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', ha'⟩ := hφ.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk] at ha' ⊢
    rw [Ideal.Quotient.eq] at ha' ⊢
    rw [hJ]
    have := sub_mem ha' (hc a)
    simpa using this

theorem LeafVanRing_of (hNb : LeafNb) (hTh : LeafThom) : LeafVanRing := by
  intro hH d q _ A _ I hC hq n i hn
  have hA1 : A1 := hH.1
  have hA9 : A9 := hH.2.2.2.2.2.2.1
  obtain ⟨B, _, φ, ψ, hφ, hψ, hI, hc⟩ := hC
  have hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hI, ← Set.range_comp]; rfl
  have hN := chart_nbhd I φ ψ hφ hψ hJ hc
  have e1 := hNb hA1 q φ I (I.map φ) hφ rfl (off_map φ I).le n i
  have e2 := hNb hA1 q ψ _ _ hN rfl (off_map ψ _).le n i
  obtain ⟨th, hth⟩ := hTh hH d
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * d := ⟨n - 2 * d, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  have hm : m < 0 := by omega
  have hsub : Subsingleton (Ht q (sp (A ⧸ I)) m j) := (hA9 (ZMod q) (tw q j)).1 _ m hm
  have h3 := ((hth q).2.2.1 (A ⧸ I) _ rfl hqR m j).2
  have hR : Subsingleton (Hs q (opn (off (MvPolynomial (Fin d) (A ⧸ I))
      (Ideal.span (Set.range MvPolynomial.X)))) (m + 2 * d) (j + d)) := by
    constructor; intro x y
    obtain ⟨a, rfl⟩ := h3 x; obtain ⟨b, rfl⟩ := h3 y; rw [Subsingleton.elim a b]
  have hB : ∀ x y : Hs q (opn (off B ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ))) (m + 2 * d) (j + d), x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := e2.2 x; obtain ⟨b, rfl⟩ := e2.2 y; rw [Subsingleton.elim a b]
  rw [hJ] at hB
  exact ⟨fun x y => e1.1 (hB _ _)⟩

end LateralTheory.CohomologicalPurity.Cl
