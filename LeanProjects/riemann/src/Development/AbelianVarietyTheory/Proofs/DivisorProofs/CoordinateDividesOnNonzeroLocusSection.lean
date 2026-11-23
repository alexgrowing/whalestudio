import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ThetaDiv

theorem resG_top_injective {X : Scheme.{0}} {W : X.Opens} (hW : ⊤ ≤ W) :
    Function.Injective (resG X (le_top : W ≤ ⊤)) := by
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  intro x y h
  have e : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  simpa only [resG, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] using h

theorem div_of_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  intro o Ω _ _ _ M δ I t th _ hsc a z hz
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hDU : M.Z.basicOpen ((t a).f k) ≤ δ.U k := M.Z.basicOpen_le _
  have hD : ((M.Z.basicOpen ((t a).f k) : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hk⟩
  have hptD := M.top_le_preimage_pt hD
  have hptU : ⊤ ≤ M.pt ⁻¹ᵁ δ.U k := fun x hx => hDU (hptD hx)
  obtain ⟨τ, -, hτ⟩ := hsc
  let j : PUnit → δ.ι := fun _ => k
  have hj : (δ.pull M.pt).U j ≤ M.pt ⁻¹ᵁ δ.U (j PUnit.unit) := LB.wchart_le δ _ j PUnit.unit
  have hW : ⊤ ≤ (δ.pull M.pt).U j := fun x _ => Set.mem_iInter.2 fun _ => hptU (x := x) trivial
  have inj := resG_top_injective hW
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  have hc : ∀ b, resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤) ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) =
      resG (Sp Ω) le_top (e.inv.hom (th b)) * (τ.s j).val := by
    intro b
    rw [← hτ b j hj]
    show (M.pt.appLE _ ⊤ hptU ≫ (Sp Ω).presheaf.map (homOfLE le_top).op).hom _ = _
    rw [Scheme.Hom.appLE_map]
  have hv : ∀ b, valF M.pt (δ.U k) ((t b).f k) = e.hom.hom ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) :=
    fun b => dif_pos hptU
  have hei : ∀ x : Ω, e.hom.hom (e.inv.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have key : ∀ b, valF M.pt (δ.U k) ((t b).f k) * th a = valF M.pt (δ.U k) ((t a).f k) * th b := by
    intro b
    have h1 : (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k) * e.inv.hom (th a) =
        (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t a).f k) * e.inv.hom (th b) := by
      apply inj
      rw [map_mul, map_mul, hc b, hc a]
      ring
    have h2 := congrArg e.hom.hom h1
    rwa [map_mul, map_mul, hei, hei, ← hv, ← hv] at h2
  have hua : valF M.pt (δ.U k) ((t a).f k) ≠ 0 :=
    ((GlobalTheory.Points.le_preimage_basicOpen_iff M.pt hptU ((t a).f k)).1 hptD).ne_zero
  have hth : th a ≠ 0 := by
    intro h0
    apply hua
    rw [hv]
    have h1 := hc a
    rw [h0, map_zero, map_zero, zero_mul] at h1
    rw [inj (h1.trans (map_zero _).symm), map_zero]
  refine ⟨hth, fun b => ?_⟩
  have hu : IsUnit (resG M.Z hDU ((t a).f k)) :=
    RingedSpace.isUnit_res_basicOpen M.Z.toLocallyRingedSpace.toRingedSpace ((t a).f k)
  have hval : valF M.pt _ (resG M.Z hDU ((t b).f k) * ((hu.unit⁻¹ : (Γ(M.Z, M.Z.basicOpen ((t a).f k)))ˣ) : Γ(M.Z, M.Z.basicOpen ((t a).f k)))) = th b / th a := by
    rw [← ZH.RatModel.res_apply M _ hD, map_mul, map_units_inv, IsUnit.unit_spec, ZH.RatModel.res_resG,
      ZH.RatModel.res_resG, ZH.RatModel.res_apply, ZH.RatModel.res_apply]
    field_simp
    linear_combination key b
  exact hval ▸ ZH.RatModel.valF_mem_O hk _

end GlobalTheory.ThetaDiv

end
