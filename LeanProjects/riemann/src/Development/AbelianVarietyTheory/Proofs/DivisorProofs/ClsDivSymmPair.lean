import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameGradedPieceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleClassOfTriangularFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoTriangularLineClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorizationThroughSubbundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagPairGenericIsoStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TriFrame

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}

theorem exists_flagPair {A : B.X.Opens} (hA : genericPoint B.X ∈ A) {E E' : B.X.Modules} (ψ : E' ⟶ E)
    [IsIso (B.genRes.map ψ)] {r : ℕ} {s : Fin r → Γ(E', A)} (hs' : IsFrame s) (hs : IsFrame fun i => ψ.app A (s i))
    {L L' : Fin r → LB B.X} (hL : ∀ i, (L i).IsLB) (hL' : ∀ i, (L' i).IsLB) {ρ : ∀ i k, Γ(B.X, A ⊓ (L i).U k)}
    {ρ' : ∀ i k, Γ(B.X, A ⊓ (L' i).U k)} (hρ : ∀ i, IsGenOn A (L i) (ρ i)) (hρ' : ∀ i, IsGenOn A (L' i) (ρ' i))
    (hT : Tri hs L ρ) (hT' : Tri hs' L' ρ') :
    ∃ P : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ) r, ∀ i,
      CechPic.cls _ (P.fl.isLB_root i) = CechPic.cls _ (hL i) ∧ CechPic.cls _ (P.fl'.isLB_root i) = CechPic.cls _ (hL' i) ∧
      ∀ D : VertDiv B, IsRatio A D (L i) (L' i) (ρ i) (ρ' i) → (P.div i).cls = D.cls := by
  obtain ⟨fl, hfl⟩ := GlobalTheory.T.exists_flag_of_triangular_frames B.X A E r _ hs hA fun x =>
    have ⟨V, e, _, _, h₁, h₂, h₃, _⟩ := hT x; ⟨V, e, h₁, h₂, h₃⟩
  obtain ⟨fl', hfl'⟩ := GlobalTheory.T.exists_flag_of_triangular_frames B.X A E' r _ hs' hA fun x =>
    have ⟨V, e, _, _, h₁, h₂, h₃, _⟩ := hT' x; ⟨V, e, h₁, h₂, h₃⟩
  choose t ht hti using hfl A _ hs (isTri_self hs)
  choose t' ht' hti' using hfl' A _ hs' (isTri_self hs')
  choose a ha using fun i => GlobalTheory.T.exists_factorization_through_subbundle B.X A (fl.F i) (fl'.F i) E (fl.ι i) (fl'.ι i ≫ ψ) i (t' i) hA
    (fl.isSubbundle i) (ht' i) fun j => ⟨t i j, (hti i j).trans (congrArg (ψ.app A) (hti' i j).symm)⟩
  obtain ⟨P, rfl, rfl, hP⟩ := GlobalTheory.T.exists_flag_pair_generic_iso O B E E' ψ r fl fl' a ha
  refine ⟨P, fun i => ?_⟩
  obtain ⟨φ, b, h₁, h₂, h₃⟩ := hP i
  let u : Γ(P.fl'.F i.succ, A) := t' i.succ (Fin.last i)
  have hu : (P.fl'.ι i.succ).app A u = s i := hti' i.succ (Fin.last i)
  have hau : (P.fl.ι i.succ).app A ((a i.succ).app A u) = ψ.app A (s i) :=
    (congrArg (fun f => f.app A u) (ha i.succ)).trans (congrArg (ψ.app A) hu)
  obtain ⟨σ', T'⟩ := GlobalTheory.T.triangular_frame_graded_piece B.X A E' r s hs' L' ρ' P.fl' hT' hfl' i u hu
  obtain ⟨σ, T⟩ := GlobalTheory.T.triangular_frame_graded_piece B.X A E r _ hs L ρ P.fl hT hfl i _ hau
  refine ⟨GlobalTheory.T.line_bundle_class_of_triangular_frame B.X A _ _ σ _ (hL i) _ hA (hρ i) T (P.fl.isVB_gr i),
    GlobalTheory.T.line_bundle_class_of_triangular_frame B.X A _ _ σ' _ (hL' i) _ hA (hρ' i) T' (P.fl'.isVB_gr i), fun D hD => ?_⟩
  have e : (P.fl.π i).app A ((a i.succ).app A u) = b.app A ((P.fl'.π i).app A u) :=
    (congrArg (fun f => f.app A u) h₂).symm
  revert σ T
  rw [e]
  intro σ T
  rw [h₃]
  exact GlobalTheory.T.generic_iso_triangular_line_classes O B A _ _ _ _ b φ h₁ hA _ σ' σ _ _ _ _ (hρ i) (hρ' i) T T' D hD

def symmPair {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ} (P : Vert.Model.FlagPair φ r) :
    Vert.Model.FlagPair φ.symm r where
  fl := P.fl'
  fl' := P.fl
  gen i := (P.gen i).symm
  gen_ι i := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, P.gen_ι, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem cls_div_symmPair {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ} (P : Vert.Model.FlagPair φ r) (i : Fin r) :
    ((symmPair P).div i).cls = -(P.div i).cls := by
  have h : P.grIso i ≪≫ (symmPair P).grIso i = Iso.refl _ := by
    ext1
    rw [← cancel_epi (B.genRes.map (P.fl.π i)), Iso.trans_hom, ← Category.assoc, P.π_grIso_hom, Category.assoc]
    refine (congrArg _ ((symmPair P).π_grIso_hom i)).trans ?_
    exact (Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm
  have h₀ := Vert.Model.GenIso.cls_div_trans (Iso.refl _) (P.fl.isVB_gr i) (P.fl.isVB_gr i) (P.fl.isVB_gr i) (Iso.refl _)
  have h₁ := Vert.Model.GenIso.cls_div_trans (P.grIso i) (P.fl.isVB_gr i) (P.fl'.isVB_gr i) (P.fl.isVB_gr i)
    ((symmPair P).grIso i)
  rw [Iso.trans_refl, left_eq_add] at h₀
  rw [h, h₀] at h₁
  exact eq_neg_of_add_eq_zero_right h₁.symm

end GlobalTheory.TriFrame

end
