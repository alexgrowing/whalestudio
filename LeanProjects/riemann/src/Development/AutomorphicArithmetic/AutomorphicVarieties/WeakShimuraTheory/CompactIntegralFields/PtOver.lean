import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.MonoMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.NonAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_map {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R') {I : Ideal R} {I' : Ideal R'}
    (h : ∀ x ∈ I, f x ∈ I') {F : Γ → R} (hF : AdicCont I F) : AdicCont I' fun g => f (F g) := fun N => by
  have hle : I ^ N ≤ (I' ^ N).comap f := le_trans (Ideal.pow_right_mono h N) (Ideal.le_comap_pow _ N)
  exact (hF N).comp (Ideal.quotientMap _ f hle)

theorem UpperTheory.V.Ws.ptOver :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ¬ D.Fin0 → ∃ (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V), CharP 𝔞.K l ∧ VPt D 𝔞 r ∧ ∃ x ∈ mono r 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro hC Ω _ _ _ l _ c D hD hF
  obtain ⟨U, _, _, _, ρ, W, hpt, hz, hform, hnf⟩ := Po.univGr hC D hD hF
  haveI : IsCO c.O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O _ U W hz
  obtain ⟨hmax, u, hu, hspan⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials c.O _ U W hz
  obtain ⟨𝔞, A, _, _, _, f, s, y, hch, hf, hy, hloc, ⟨b, hb, hb0⟩, hO, hcl⟩ := Po.ambPt c (W.gr 0) hnf
  obtain ⟨A', _, _, _, f', Ξ, hf', hΞ, hext⟩ :=
    Po.ptA 𝔞 A f hf s c.O _ U W hz y (fun b hb => hloc b ((hmax b).2 hb)) hcl
  let Y : U →+* 𝔞.V := f'.comp Ξ
  have hya : ∀ a, y (algebraMap c.O (W.gr 0) a) = 𝔞.a c a := fun a => RingHom.congr_fun hy a
  have hYa : ∀ a, Y (algebraMap c.O U a) = 𝔞.a c a := fun a => by
    have e : ((algebraMap c.O (W.gr 0) a : W.A) : U) = algebraMap c.O U a := by
      simp
    rw [← hya, ← hext, e]
    rfl
  have hYm : ∀ x ∈ maximalIdeal U, Y x ∈ maximalIdeal 𝔞.V := fun x hx => by
    haveI := hf'.loc
    exact map_nonunit f' _ (hΞ x hx)
  refine ⟨𝔞, mapRep Y ρ.hom, hch, ⟨⟨A', inferInstance, inferInstance, inferInstance, f', ⟨mapRep Ξ ρ.hom, fun _ => 1⟩, hf',
    fun i j => cont_map Ξ hΞ (ρ.cont i j), PD.ext rfl (funext fun _ => Matrix.map_one _ (map_zero _) (map_one _))⟩,
    U, inferInstance, inferInstance, inferInstance, ρ, Y, hpt, RingHom.ext hYa, hYm, rfl⟩, ?_⟩
  have hex : ∃ v ∈ u, y v ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hb0 (show b ∈ RingHom.ker y from (?_ : maximalIdeal (W.gr 0) ≤ RingHom.ker y) hb)
    rw [hspan]
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) (Ideal.span_le.2 fun v hv => hn v hv)
    show y _ = 0
    rw [hya, hO a ha]
  obtain ⟨v, hv, hv0⟩ := hex
  obtain ⟨n, -, hn, hvn⟩ := hu v hv
  haveI := (Po.fin_res c).1
  haveI : CharP 𝔞.V l := haveI := hch; 𝔞.V.subtype.charP Subtype.val_injective l
  have hvm : v ∈ maximalIdeal (W.gr 0) := hspan ▸ Ideal.mem_sup_right (Ideal.subset_span hv)
  refine Po.nonAlg l c.O _ U ρ.hom 𝔞.V Y (fun a ha => by rw [hYa, hO a ha]) ((v : W.A) : U) ?_ (hYm _ ((hmax v).1 hvm)) ?_
  · rw [hvn]
    exact Po.zMono c.O _ U ρ.hom W (fun g a b => D.r0 g a b)
      (fun g a b h => Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) h) hform n hn
  · show f' (Ξ _) ≠ 0
    rwa [hext]
