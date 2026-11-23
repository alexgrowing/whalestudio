import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ChainPts.PullHT

open GlobalTheory.VB (IsFrame IsVB)

section EPres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B₁ : Vert.Model O} {Λ : Type} [CommRing Λ]

abbrev pullA (f : B.X ⟶ B₁.X) : AM B₁ Λ ⥤ AM B Λ := (Scheme.Modules.pullback f).mapAction Λ

theorem isAdd_pullA (f : B.X ⟶ B₁.X) {M : AM B₁ Λ} (h : IsAdd M) : IsAdd ((pullA f).obj M) := fun a b => by
  change (Scheme.Modules.pullback f).map (M.ρ (a + b) : M.V ⟶ M.V) =
    (Scheme.Modules.pullback f).map (M.ρ a : M.V ⟶ M.V) + (Scheme.Modules.pullback f).map (M.ρ b : M.V ⟶ M.V)
  rw [h, Functor.map_add]

def EPres.pull (g : Vert.Model.Hom B B₁) (P : EPres B₁ Λ) : EPres B Λ where
  r := P.r
  E := (pullA g.f).obj P.E
  E' := (pullA g.f).obj P.E'
  add := isAdd_pullA g.f P.add
  add' := isAdd_pullA g.f P.add'
  vb := P.vb.pullback g.f
  vb' := P.vb'.pullback g.f
  ψ := (pullA g.f).map P.ψ
  iso := by
    haveI := P.iso
    have := Vert.Model.GenIso.pull_inv g.comp_str (φ := Vert.Model.GenIso.ofHom P.ψ.hom) rfl
    change IsIso (B.genRes.map ((Scheme.Modules.pullback g.f).map P.ψ.hom))
    rw [← this]; infer_instance

end EPres

theorem isFrame_pullS {X X' : Scheme.{0}} (g : X' ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {r : ℕ}
    {V : X.Opens} {U : X'.Opens} (hU : U ≤ g ⁻¹ᵁ V) {e : Fin r → Γ(F, V)} (he : IsFrame e) :
    IsFrame fun i => pullbackSections g F hU (e i) := by
  have := (he.pullback g).res hU
  convert this using 2 with i
  exact (res_pullbackSections g F _ hU _).symm

theorem valF_appLE {k : Type} [Field k] {X X' : Scheme.{0}} (w : Sp k ⟶ X') (g : X' ⟶ X) {U : X.Opens}
    {U' : X'.Opens} (h : U' ≤ g ⁻¹ᵁ U) (h' : g ⁻¹ᵁ U ≤ U') (c : Γ(X, U)) :
    valF w U' ((g.appLE U U' h).hom c) = valF (w ≫ g) U c := by
  have e : U' = g ⁻¹ᵁ U := le_antisymm h h'
  subst e
  unfold valF
  by_cases hc : ⊤ ≤ (w ≫ g) ⁻¹ᵁ U
  · have hc' : ⊤ ≤ w ⁻¹ᵁ g ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage] at hc
    rw [dif_pos hc, dif_pos hc']
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  · have hc' : ¬ ⊤ ≤ w ⁻¹ᵁ g ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage] at hc
    rw [dif_neg hc, dif_neg hc']

theorem top_le_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (w : Sp R ⟶ X) (V : X.Opens)
    (h : w (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ w ⁻¹ᵁ V :=
  (Scheme.preimage_eq_top_of_closedPoint_mem w h).ge

end GlobalTheory.ChainPts.PullHT

end
