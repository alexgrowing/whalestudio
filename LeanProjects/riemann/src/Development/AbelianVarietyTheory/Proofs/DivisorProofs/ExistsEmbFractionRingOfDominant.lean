import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

theorem spMap_fractionRing_specializes (V : Type) [CommRing V] [IsDomain V] (w : Sp V) (p : Sp (FractionRing V)) :
    (spMap (algebraMap V (FractionRing V))) p ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
  show Ideal.comap (algebraMap V (FractionRing V)) p.asIdeal ≤ w.asIdeal
  have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal (PrimeSpectrum.isPrime p)
  rw [hp]
  intro x hx
  have hx' : algebraMap V (FractionRing V) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
  rw [(injective_iff_map_eq_zero _).1 (IsFractionRing.injective V (FractionRing V)) x hx']
  exact w.asIdeal.zero_mem

theorem exists_emb_fractionRing_of_dominant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∃ emb : Ω →+* FractionRing V, ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U → emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f) := by
  intro o Ω _ _ _ M V _ _ _ ξ ⟨w, hw⟩
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  let g0 : M.O z →+* V :=
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom.comp (M.stalkEquiv z).symm.toRingHom
  have hg0 : ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)) (hz : z ∈ U),
      g0 ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = valR ξ U f := by
    intro U f hz
    have h : ⊤ ≤ ξ ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff ξ U).2 hz
    have e1 : (M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f := by
      rw [RingEquiv.symm_apply_eq, RatModel.stalkEquiv_germ]
    have e2 := congrArg (fun φ => φ.hom f) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap ξ U h)
    change (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom ((M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩) = _
    rw [e1]
    rw [GlobalTheory.Points.valR_eq ξ U h]
    exact e2
  have hinj0 : Function.Injective g0 := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    obtain ⟨U, f, hz, rfl⟩ := RatModel.mem_O.1 hx
    rw [hg0 U f hz] at h0
    have hU : (U : Set M.Z).Nonempty := ⟨z, hz⟩
    by_cases hf : f = 0
    · subst hf
      apply Subtype.ext
      show valF M.pt U 0 = 0
      rw [← M.res_apply U hU, map_zero]
    · exfalso
      have hb : M.Z.basicOpen f ≠ ⊥ := fun hb => hf ((basicOpen_eq_bot_iff f).1 hb)
      obtain ⟨y, hy⟩ : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        exact fun h => hb (SetLike.coe_injective h)
      have hgen : genericPoint M.Z ∈ M.Z.basicOpen f :=
        (genericPoint_specializes y).mem_open (M.Z.basicOpen f).isOpen hy
      let eta : Sp (FractionRing V) ⟶ M.Z := spMap (algebraMap V (FractionRing V)) ≫ ξ
      have heta : ⊤ ≤ eta ⁻¹ᵁ M.Z.basicOpen f := by
        intro p _
        have hs : eta p ⤳ genericPoint M.Z := by
          rw [← hw]
          exact (spMap_fractionRing_specializes V w p).map ξ.continuous
        exact hs.mem_open (M.Z.basicOpen f).isOpen hgen
      have hetaU : ⊤ ≤ eta ⁻¹ᵁ U := heta.trans (eta.preimage_mono (M.Z.basicOpen_le f))
      have hu := (GlobalTheory.Points.le_preimage_basicOpen_iff eta hetaU f).1 heta
      rw [GlobalTheory.Points.valR_spMap_comp _ ξ U ((GlobalTheory.Points.le_preimage_iff ξ U).2 hz), h0, map_zero] at hu
      exact not_isUnit_zero hu
  let g : M.O z →+* FractionRing V := (algebraMap V (FractionRing V)).comp g0
  have hinj : Function.Injective g := (IsFractionRing.injective V (FractionRing V)).comp hinj0
  refine ⟨IsFractionRing.lift hinj, fun U f hz => ?_⟩
  have e : valF M.pt U f = algebraMap (M.O z) Ω ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ := rfl
  rw [e, IsFractionRing.lift_algebraMap]
  show algebraMap V (FractionRing V) (g0 _) = _
  rw [hg0 U f hz]

end GlobalTheory.ZH.RatModel
