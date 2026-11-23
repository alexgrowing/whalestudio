import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem functionFieldMap_fnOf (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {x : X}
    (hx : x ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from hx)) s) =
      GlobalTheory.Cartier.fnOf (f ⁻¹ᵁ U) (GlobalTheory.Cartier.gen_mem hx) (f.app U s) := by
  rw [← GlobalTheory.Cartier.algebraMap_germ (show f x ∈ U from hx), functionFieldMap_algebraMap,
    ← GlobalTheory.Cartier.algebraMap_germ hx]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply f U x hx s

theorem fnOf_appLE (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    {x : X} (hx : x ∈ V) (s : Γ(Y, U)) :
    GlobalTheory.Cartier.fnOf V (GlobalTheory.Cartier.gen_mem hx) (f.appLE U V e s) =
      functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from e hx)) s) := by
  rw [functionFieldMap_fnOf f (e hx)]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact X.presheaf.germ_res_apply (homOfLE e) _ _ _

end GlobalTheory.FnPull

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {Γ : Type} [Group Γ]

theorem functionFieldMap_act (ρ : Γ →* Aut X) (q : X ⟶ Y) [IsDominant q]
    (hq : ∀ g, (ρ g).hom ≫ q = q) (hs : Function.Surjective q) (g : Γ) [IsDominant (ρ g).hom]
    (c : Y.functionField) :
    functionFieldMap (ρ g).hom (functionFieldMap q c) = functionFieldMap q c := by
  obtain ⟨U₀, hη, s, rfl⟩ := Y.presheaf.exists_germ_eq c
  obtain ⟨x, hx⟩ := hs (genericPoint Y)
  have hx' : x ∈ q ⁻¹ᵁ U₀ := show q x ∈ U₀ from hx ▸ hη
  change functionFieldMap (ρ g).hom (functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)) =
    functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)
  rw [functionFieldMap_fnOf q hx' s]
  obtain ⟨e, hinv⟩ := isInvariantSection_app ρ q hq U₀ s g
  rw [← fnOf_appLE (ρ g).hom e hx', hinv]

theorem isInvariantSection_of_fnOf [Finite Γ] {ρ : Γ →* Aut X} {q : X ⟶ Y} [IsDominant q]
    (h : IsAffineQuotient ρ q) {V : Y.Opens} {x : X} (hx : x ∈ q ⁻¹ᵁ V) (c : Γ(X, q ⁻¹ᵁ V))
    (b : Y.functionField) (hc : GlobalTheory.Cartier.fnOf _ (GlobalTheory.Cartier.gen_mem hx) c = functionFieldMap q b) :
    IsInvariantSection ρ _ c := fun g ↦ by
  haveI : IsIso (ρ g).hom := Iso.isIso_hom _
  refine ⟨h.preimage_le V g, GlobalTheory.Cartier.fnOf_injective _ (GlobalTheory.Cartier.gen_mem hx) ?_⟩
  rw [fnOf_appLE (ρ g).hom (h.preimage_le V g) hx, hc,
    functionFieldMap_act ρ q h.comp_eq h.surjective.surj g]

end GlobalTheory.FnPull

namespace GlobalTheory.OrbitSep

theorem unitAt_of_forall_unitAt_fibre : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  intro X W _ _ Γ _ _ ρ q _ h y b hb
  have hsurj : Function.Surjective q := h.surjective.surj
  haveI := h.isIntegralHom
  let O : Set X := {x | GlobalTheory.Cartier.UnitAt x (functionFieldMap q b)}
  have hOo : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hx
    exact ⟨U, fun z hz ↦ hU z hz, U.isOpen, hxU⟩
  have hV : IsOpen (q '' Oᶜ)ᶜ := (q.isClosedMap _ hOo.isClosed_compl).isOpen_compl
  let V : W.Opens := ⟨_, hV⟩
  obtain ⟨x₀, hx₀⟩ := hsurj y
  have hyV : y ∈ V := fun ⟨x, hx, e⟩ ↦ hx (hb x e)
  have hx₀V : x₀ ∈ q ⁻¹ᵁ V := show q x₀ ∈ V from hx₀ ▸ hyV
  have hUO : ∀ x ∈ q ⁻¹ᵁ V, GlobalTheory.Cartier.UnitAt x (functionFieldMap q b) := fun x hx ↦ by
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hUO
  have hgen := GlobalTheory.Cartier.gen_mem hx₀V
  have ha1 : GlobalTheory.Cartier.fnOf _ hgen (a : Γ(X, q ⁻¹ᵁ V)) = functionFieldMap q b := ha hgen
  have ha2 : GlobalTheory.Cartier.fnOf _ hgen ((a⁻¹ : Γ(X, q ⁻¹ᵁ V)ˣ) : Γ(X, q ⁻¹ᵁ V)) =
      functionFieldMap q b⁻¹ := by
    rw [map_units_inv, ha1, map_inv₀]
  obtain ⟨t, ht⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b ha1)
  obtain ⟨t', ht'⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b⁻¹ ha2)
  have htt : t * t' = 1 := h.app_injective V (by rw [map_mul, ht, ht', Units.mul_inv, map_one])
  let u : Γ(W, V)ˣ := ⟨t, t', htt, by rw [mul_comm]; exact htt⟩
  have hgenW := GlobalTheory.Cartier.gen_mem hyV
  have hbu : GlobalTheory.Cartier.fnOf V hgenW t = b := (functionFieldMap q).injective (by
    rw [GlobalTheory.FnPull.functionFieldMap_fnOf q hx₀V t, ht, ha1])
  rw [← hbu]
  exact GlobalTheory.Cartier.unitAt_fnOf hyV hgenW u

end GlobalTheory.OrbitSep
