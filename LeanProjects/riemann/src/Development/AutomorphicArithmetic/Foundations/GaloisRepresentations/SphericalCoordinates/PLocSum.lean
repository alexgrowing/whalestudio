import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.locSum_of :
    UpperTheory.Gal.W2.LocTan → UpperTheory.Gal.W2.TorusCount → UpperTheory.Gal.W2.PiLattice → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.DetOfCharpoly → UpperTheory.Gal.W2.LocSum := by
  intro hTan hCount hPi hFib hChart hDet O _ bar g ρ D X s A _ S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL hlat hinj hdT hdΘ
  classical
  have hrange : Submodule.span ℝ ((P₀.range : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  obtain ⟨hdisc, hspan⟩ := hPi g k P₀.range hP.2.2.1 hrange
  set Λk : AddSubgroup (Fin k → Fin g → ℂ) :=
    AddSubgroup.pi (Set.univ : Set (Fin k)) (fun _ => P₀.range) with hΛk
  have memΛ : ∀ z : Fin k → Fin g → ℂ, z ∈ Λk ↔ ∀ j, z j ∈ P₀.range := by
    intro z; simp [hΛk, AddSubgroup.mem_pi]
  obtain ⟨Fz, hFz1, hFz2, hFzc⟩ := hCount (Fin k → Fin g → ℂ) Λk hdisc hspan (fibMap H L)
    (fun z hz => (memΛ _).2 (hlat z ((memΛ z).1 hz))) hdΘ
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hFib O bar g ρ D X s A S k P₀ hP
  have e0 : H * 0 * (H.map star)⁻¹ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ z, S.pt k P₀ z ≫ c₂ = S.pt k P₀ (fibMap H L z) ≫ c₁ := by
    intro z
    have h := hChart O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP hM ga H hga L hL 0
      (by rw [perC_zero]; exact hP) (by rw [e0, perC_zero]; exact hP) z
    rw [e0, perC_zero] at h
    exact h
  have fixIff : ∀ z, S.pt k P₀ z ≫ c₁ = S.pt k P₀ z ≫ c₂ ↔ fibMap H L z - z ∈ Λk := by
    intro z
    constructor
    · intro h
      have h' : S.pt k P₀ z = S.pt k P₀ (fibMap H L z) := hinj _ _ (h.trans (key z))
      exact (memΛ _).2 ((hf4 _ _).1 h'.symm)
    · intro h
      have h' := (hf4 (fibMap H L z) z).2 ((memΛ _).1 h)
      rw [key z, h']
  let mk : (Fin k → Fin g → ℂ) → CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ) :=
    fun z => ⟨S.pt k P₀ z, by rw [← Category.assoc, hf1 z]; exact S.ov P₀ hP⟩
  have mkInj : Set.InjOn mk Fz := by
    intro z hz z' hz' h
    have h1 : S.pt k P₀ z = S.pt k P₀ z' := congrArg Subtype.val h
    have h2 : z - z' ∈ Λk := (memΛ _).2 ((hf4 z z').1 h1)
    obtain ⟨w, _, hw⟩ := hFz2 z (hFz1 z hz)
    have a := hw z ⟨hz, by rw [sub_self]; exact zero_mem _⟩
    have b := hw z' ⟨hz', h2⟩
    exact a.trans b.symm
  refine ⟨Fz.image mk, ?_, ?_⟩
  · intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hf1 z, (fixIff z).2 (hFz1 z hz)⟩
    · rintro ⟨ho, hfx⟩
      obtain ⟨z, hz⟩ := hf3 y.1 ho
      have hz1 : fibMap H L z - z ∈ Λk := (fixIff z).1 (by rw [← hz]; exact hfx)
      obtain ⟨z', ⟨hz'F, hz'⟩, _⟩ := hFz2 z hz1
      refine ⟨z', hz'F, Subtype.ext ?_⟩
      show S.pt k P₀ z' = y.1
      rw [hz]; exact ((hf4 z z').2 ((memΛ _).1 hz')).symm
  · intro At hAt
    have hdet : ∀ y ∈ Fz.image mk, ∀ t : ℂ, (1 - t • At y).det =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) := by
      intro y hy t
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      have hcp := hTan O bar g ρ D X s A S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL z
        ((memΛ _).1 (hFz1 z hz)) (mk z) rfl (At (mk z)) (hAt _ hy)
      exact hDet _ _ T (fibMap H L) _ _ hcp t
    have hdet1 : ∀ y ∈ Fz.image mk, (1 - At y).det =
        LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L) := by
      intro y hy
      have h := hdet y hy 1
      simpa only [one_smul] using h
    refine ⟨fun y hy => by rw [hdet1 y hy]; exact mul_ne_zero hdT hdΘ, fun t => ?_⟩
    have hterm : ∀ y ∈ Fz.image mk, lefTerm (At y) t =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) /
          (LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L)) := by
      intro y hy
      unfold lefTerm
      rw [hdet y hy t, hdet1 y hy]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_image_of_injOn mkInj, nsmul_eq_mul, hFzc]
    field_simp
