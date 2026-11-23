import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isLocallyNoetherian [IsNoetherianRing o] : IsLocallyNoetherian M.Z :=
  have := M.lft
  LocallyOfFiniteType.isLocallyNoetherian M.s

def ptOpen (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : Sp Ω ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι M.pt (by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hV))

theorem ptOpen_ι (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : M.ptOpen V hV ≫ V.ι = M.pt :=
  IsOpenImmersion.lift_fac _ _ _

def openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : RatModel o Ω :=
  haveI : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  { Z := V.toScheme
    s := V.ι ≫ M.s
    sep := have := M.sep; inferInstance
    lft := have := M.lft; inferInstance
    qc := have := M.qc; have := M.isLocallyNoetherian; inferInstance
    pt := M.ptOpen V hV
    pt_s := by rw [← Category.assoc, ptOpen_ι, M.pt_s]
    gen := by
      have h : ∀ w : Sp Ω, M.ptOpen V hV w = genericPoint V.toScheme := fun w => by
        apply V.ι.isOpenEmbedding.injective
        rw [genericPoint_eq_of_isOpenImmersion, ← M.pt_apply w, ← M.ptOpen_ι V hV]
        rfl
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
        rintro _ ⟨w, rfl⟩
        exact h w⟩
    onto := fun x => by
      obtain ⟨U, f, hU, rfl⟩ := M.onto x
      obtain ⟨z, hz, hz'⟩ := M.nonempty_inf hU hV
      refine ⟨V.ι ⁻¹ᵁ U, V.ι.app U f, ⟨⟨z, hz'⟩, hz⟩, ?_⟩
      refine (valR_comp _ _ U f).symm.trans ?_
      rw [ptOpen_ι]
      rfl }

theorem isHom_openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) :
    M.IsHom (M.openPart V hV) (AlgHom.id o Ω) V.ι :=
  (M.ptOpen_ι V hV).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ M.pt) (Spec.map_id _).symm))

variable {M}

theorem IsHom.O_eq {N : RatModel o Ω} {j : N.Z ⟶ M.Z} (h : M.IsHom N (AlgHom.id o Ω) j) [IsOpenImmersion j]
    (z : N.Z) : N.O z = M.O (j z) := by
  refine le_antisymm ?_ fun x hx => h.map_mem_O hx
  rintro _ ⟨U, g, hz, rfl⟩
  have hz' : j z ∈ j ''ᵁ U := ⟨z, hz, rfl⟩
  refine ⟨j ''ᵁ U, (j.appIso U).inv g, hz', ?_⟩
  refine (h.valF_app ⟨_, hz'⟩ _).symm.trans ?_
  have e := congrArg (fun φ => φ.hom g) (j.appIso_inv_app U)
  refine (congrArg _ e).trans ?_
  exact N.valF_resG (j.preimage_image_eq U).le ⟨z, hz'⟩ g

variable (M)

structure GenTriv (H : LB M.Z) (d : H.ι → Ω) : Prop where
  ne : ∀ k, d k ≠ 0
  g_eq : ∀ k k', ((H.U k ⊓ H.U k' : M.Z.Opens) : Set M.Z).Nonempty →
    valF M.pt (H.U k ⊓ H.U k') (H.g k k' : Γ(M.Z, H.U k ⊓ H.U k')) = d k' / d k

def HasVal {H : LB M.Z} (d : H.ι → Ω) (σ : H.Sec) (x : Ω) : Prop :=
  ∀ k, (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) (σ.f k) = x / d k

def ProjChart {Ω' : Type} [Field Ω'] [Algebra o Ω'] (N : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (q : N.Z ⟶ M.Z)
    (W : M.Z.Opens) {J : Type} (t : J → Ω') : Prop :=
  (∀ z', q z' ∈ W → ∃ i, N.Div t i z') ∧ ∀ i, t i ≠ 0 → ∃ U : N.Z.Opens, IsAffineOpen U ∧
    (U : Set N.Z) = {z' | q z' ∈ W ∧ N.Div t i z'} ∧
    N.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => t j / t i)

example : M.GenTriv ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ fun _ => 1 :=
  ⟨fun _ => one_ne_zero, fun _ _ h => (valR_one _ _ (M.top_le_preimage_pt h)).trans (div_one 1).symm⟩

end GlobalTheory.ZH.RatModel
end
