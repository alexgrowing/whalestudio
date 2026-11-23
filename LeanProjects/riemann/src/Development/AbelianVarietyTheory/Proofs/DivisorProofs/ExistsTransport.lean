import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

namespace GlobalTheory.ChainPts

section admitted

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits}

def LatUnique (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∀ (r : ℕ) (x : Fin r → Letter S.Dw) (d : Bool)
      (P P' : EPres B (𝓞 D.host.E)), IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) x d P →
        IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) x d P' →
          ∃ (e : P.E ≅ P'.E) (e' : P.E' ≅ P'.E'), P.ψ ≫ e.hom = e'.hom ≫ P'.ψ

def ChainCover (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (o : ℕ) (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B₁.X → f₁.relDim = 0 → ∃ (B : Vert.Model (z.Z.i.c.V W)) (g : Vert.Model.Hom B B₁)
      (Q : EqChain p B (𝓞 D.host.E) o), GlobalTheory.IsNormalScheme B.X ∧ g.relDim = 0 ∧
        IsEqLatPres z.Z ((g.comp f₁).f ≫ (nmodel z.Z).compι c) (xAll S) false Q.lw ∧
        IsEqLatPres z.Z ((g.comp f₁).f ≫ (nmodel z.Z).compι c) (fun k => xAll S k.rev) true Q.oo

end admitted

def LatUniqueSt : Prop := AtAll fun _ _ _ _ _ _ _ z => LatUnique z

def ChainCoverSt : Prop := AtAll fun _ _ _ _ _ _ _ z => ChainCover z

section Transport

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

theorem comp_smulA {M M' : AM B Λ} (u : M ⟶ M') (a : Γ(B.X, ⊤)) : u ≫ smulA M' a = smulA M a ≫ u := by
  apply Action.Hom.ext
  exact (smulHom_comp u.hom a).symm

theorem IsExtA.of_iso {F₁ F₂ F₃ G₁ G₂ G₃ : AM B Λ} (h : IsExtA F₁ F₂ F₃) (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂)
    (e₃ : F₃ ≅ G₃) : IsExtA G₁ G₂ G₃ := by
  obtain ⟨T, hT, ⟨i₁⟩, ⟨i₂⟩, ⟨i₃⟩⟩ := h
  exact ⟨T, hT, ⟨i₁ ≪≫ e₁⟩, ⟨i₂ ≪≫ e₂⟩, ⟨i₃ ≪≫ e₃⟩⟩

theorem EqChain.exists_transport {o : ℕ} (Q : EqChain p B Λ o) (lw oo : EPres B Λ) (e : lw.E ≅ Q.lw.E)
    (e' : lw.E' ≅ Q.lw.E') (he : lw.ψ ≫ e.hom = e'.hom ≫ Q.lw.ψ) (f : oo.E ≅ Q.oo.E) (f' : oo.E' ≅ Q.oo.E')
    (hf : oo.ψ ≫ f.hom = f'.hom ≫ Q.oo.ψ) : ∃ Q' : EqChain p B Λ o, Q'.lw = lw ∧ Q'.oo = oo := by
  have hw : lw.ψ ≫ (e.hom ≫ Q.wl ≫ e'.inv) = smulA _ Q.π := by
    rw [reassoc_of% he, reassoc_of% Q.lw_wl, reassoc_of% (comp_smulA e'.hom Q.π), Iso.hom_inv_id, Category.comp_id]
  have ec : cokernel (e.hom ≫ Q.wl ≫ e'.inv) ≅ cokernel Q.wl :=
    cokernelEpiComp e.hom (Q.wl ≫ e'.inv) ≪≫ cokernelCompIsIso Q.wl e'.inv
  have eo : oo.mod ≅ Q.oo.mod := cokernel.mapIso oo.ψ Q.oo.ψ f' f hf
  refine ⟨{ Q with
      lw := lw
      wl := e.hom ≫ Q.wl ≫ e'.inv
      lw_wl := hw
      oo := oo
      c3 := Q.c3.of_iso ec.symm (Iso.refl _) eo.symm
      l_last := fun n hn => (Q.l_last n hn).map fun i => i ≪≫
        cokernel.mapIso (smulA Q.lw.E' (p : Γ(B.X, ⊤))) (smulA lw.E' (p : Γ(B.X, ⊤))) e'.symm e'.symm
          (comp_smulA _ _).symm }, rfl, rfl⟩

end Transport

theorem latHalfSt_of (hU : LatUniqueSt) (hC : ChainCoverSt) : LatHalfSt := by
  intro D O hO p _ W hW jc hj z
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  intro c o B₁ f₁ hB₁ hf₁
  obtain ⟨B, g, Q, hB, hg, hQl, hQo⟩ := hC D O hO p W hW jc hj z c o B₁ f₁ hB₁ hf₁
  have hgf : (g.comp f₁).relDim = 0 := by
    unfold Vert.Model.Hom.relDim at *
    omega
  refine ⟨B, g, hB, hg, fun lw oo hlo => ?_⟩
  obtain ⟨e, e', he⟩ := hU D O hO p W hW jc hj z c B (g.comp f₁) hB hgf _ _ false lw Q.lw hlo.2.1 hQl
  obtain ⟨f, f', hf⟩ := hU D O hO p W hW jc hj z c B (g.comp f₁) hB hgf _ _ true oo Q.oo hlo.2.2 hQo
  exact Q.exists_transport lw oo e e' he f f' hf

end GlobalTheory.ChainPts
