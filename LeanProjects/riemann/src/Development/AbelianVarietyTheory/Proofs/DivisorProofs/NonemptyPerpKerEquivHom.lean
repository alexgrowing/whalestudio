import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.PerpKerRank

theorem exists_eStd_eq_addHom (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  obtain ⟨a, ha⟩ := (eStdBilin_bijective (g := g) (n := n)).2 (φ.toZModLinearMap n)
  exact ⟨a, fun b => LinearMap.congr_fun ha b⟩

theorem nonempty_perp_ker_equiv_hom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy) :
    Nonempty (S.perp yy.ker ≃+ (X →+ ZMod (S.r * S.N))) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  refine ⟨AddEquiv.ofBijective Λ ⟨(injective_iff_map_eq_zero _).2 fun t ht =>
    Subtype.ext (eq_zero_of_eStd_eq_zero fun b => ?_), fun l => ?_⟩⟩
  · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
    rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
  · let l' : (X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ l (by
        rintro _ ⟨x, rfl⟩
        show l ((S.r * S.N) • x) = 0
        rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq_addHom S.g _ (l'.comp yy)
    refine ⟨⟨a, fun h hh => (ha h).trans ?_⟩, AddMonoidHom.ext fun α => (ha (σ α)).trans ?_⟩
    · rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hh, map_zero]
    · rw [AddMonoidHom.comp_apply, hσ]
      rfl

theorem perp_ker_equiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range), Function.Surjective yy → S.IsoFree (S.perp yy.ker) → Nonempty (S.perp yy.ker ≃+ (Fin (Module.finrank ℤ X) → ZMod (S.r * S.N))) := by
  intro o Ω _ _ _ S X _ _ _ yy hs _
  obtain ⟨e⟩ := nonempty_perp_ker_equiv_hom S yy hs
  exact ⟨e.trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩

end GlobalTheory.ZH.PerpKerRank
