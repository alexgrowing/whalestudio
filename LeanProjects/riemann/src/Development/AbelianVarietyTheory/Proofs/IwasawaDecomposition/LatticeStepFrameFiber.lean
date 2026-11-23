import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocM.LatNorm

theorem fromSpec_appLE_top' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem val_appLE {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {k : Type} [CommRing k]
    (φ : Γ(X, U) →+* k) (g : X ⟶ Y) {O : Y.Opens} (hle : U ≤ g ⁻¹ᵁ O)
    (h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ O) (s : Γ(Y, O)) :
    (Scheme.ΓSpecIso (.of k)).hom (((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h s) = φ (g.appLE O U hle s) := by
  have e₀ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₁ : ⊤ ≤ spMap φ ⁻¹ᵁ (⊤ : (Sp Γ(X, U)).Opens) := le_top
  have e : ((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h =
      g.appLE O U hle ≫ hU.fromSpec.appLE U ⊤ e₀ ≫ (spMap φ).appLE ⊤ ⊤ e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have h1 : (spMap φ).appLE ⊤ ⊤ e₁ = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [e, fromSpec_appLE_top', h1]
  have := congrArg (fun f => f.hom ((Scheme.ΓSpecIso Γ(X, U)).inv (g.appLE O U hle s)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at this ⊢
  refine this.trans ?_
  exact congrArg φ (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U)) _)

open GlobalTheory.Twist (resM app_resM)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem tanEv_incl_res {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {V O : B.X.Opens} (hOV : O ≤ V)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (hO : ⊤ ≤ x ⁻¹ᵁ O) (s : Γ(L.N.toMod, V)) :
    tanEv B.t hv h (L.N.incl.app V s) = tanEv B.t hv hO (L.N.incl.app O (resM _ hOV s)) := by
  rw [app_resM, tanEv_resM]

theorem tanEv_incl_sum {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {O : B.X.Opens} (hO : ⊤ ≤ x ⁻¹ᵁ O) {n : ℕ}
    (c : Fin n → Γ(B.X, O)) (s : Fin n → Γ(L.N.toMod, O)) :
    tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) =
      ∑ i, (Scheme.ΓSpecIso (.of k)).hom (x.appLE O ⊤ hO (c i)) * tanEv B.t hv hO (L.N.incl.app O (s i)) := by
  let f : Γ(B.om, O) →+ k := AddMonoidHom.mk' (tanEv B.t hv hO) (tanEv_add B.t hv hO)
  have e : tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) = f (L.N.incl.app O (∑ i, c i • s i)) := rfl
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul]
  exact tanEv_smul B.t hv hO _ _

theorem stepAt_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L σ r hr g hg hH V n m hm x hx
  obtain ⟨-, g', hg', hS⟩ := hH
  dsimp only at g' hg' hS
  obtain rfl := GlobalTheory.LocM.MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW Z B g' g hg' hg
  obtain ⟨U', hU', V', n', m', a', hxU', hU'V', hm', hcl⟩ := hS x
  have hxO : g' x ∈ V ⊓ V' := ⟨hx, hU'V' hxU'⟩
  haveI : Nontrivial Γ(B.X, V ⊓ V') := (B.X.presheaf.germ (V ⊓ V') (g' x) hxO).hom.domain_nontrivial
  let b := hm.basis (inf_le_left : V ⊓ V' ≤ V)
  let b' := hm'.basis (inf_le_right : V ⊓ V' ≤ V')
  obtain rfl : n = n' := by simpa using Fintype.card_congr (b.indexEquiv b')
  obtain ⟨U, hU, hxU, hUle⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := U' ⊓ g' ⁻¹ᵁ (V ⊓ V')) x ⟨hxU', hxO⟩
  have hUU' : U ≤ U' := hUle.trans inf_le_left
  have hUO : U ≤ g' ⁻¹ᵁ (V ⊓ V') := hUle.trans inf_le_right
  have hUV : U ≤ g' ⁻¹ᵁ V := hUO.trans (g'.preimage_mono inf_le_left)
  let gU : Γ(B.X, V ⊓ V') →+* Γ(Z.X, U) := (g'.appLE (V ⊓ V') U hUO).hom
  let T := b.toMatrix b'
  let S := b'.toMatrix b
  let Mu : GL (Fin n) Γ(Z.X, U) := ⟨(T.map gU).transpose, (S.map gU).transpose,
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one]⟩
  let a : GL (Fin n) Γ(Z.X, U) := Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' * Mu
  refine ⟨U, hU, a, hxU, hUV, ?_⟩
  intro k _ φ v hv h hin j hj
  have ept : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) ≫ hU'.fromSpec = spMap φ ≫ hU.fromSpec := by
    have sc : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) = spMap φ ≫ spMap (GlobalTheory.LocM.StepFrame.resR hUU') := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [sc, Category.assoc, GlobalTheory.LocM.StepFrame.spMap_resR hU' hU hUU']
  have key := hcl k (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) v
  rw [ept] at key
  have hfU : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  have hO : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ (V ⊓ V') := by
    rw [Scheme.Hom.comp_preimage]
    exact hfU.trans ((spMap φ ≫ hU.fromSpec).preimage_mono hUO)
  have hV' : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ V' := hO.trans (Scheme.Hom.preimage_mono _ inf_le_right)
  have k0 := key hv hV' hin j hj

  have hb : ∀ l, b l = resM _ (inf_le_left : V ⊓ V' ≤ V) (m l) := fun l => hm.basis_apply _ _
  have hb' : ∀ l, b' l = resM _ (inf_le_right : V ⊓ V' ≤ V') (m' l) := fun l => hm'.basis_apply _ _
  have e₁ : ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b l)) := fun l => by
    rw [hb]
    exact tanEv_incl_res L hv inf_le_left h hO (m l)
  have e₂ : ∀ l', tanEv B.t hv hV' (L.N.incl.app V' (m' l')) =
      ∑ i, φ (gU (T i l')) * tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b i)) := fun l' => by
    rw [tanEv_incl_res L hv inf_le_right hV' hO (m' l'), ← hb', ← b.sum_toMatrix_smul_self b' l', tanEv_incl_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [val_appLE hU φ g' hUO]
  have e₃ : ∀ l, φ (a j l) = ∑ l', φ (GlobalTheory.LocM.StepFrame.resR hUU' (a' j l')) * φ (gU (T l l')) := fun l => by
    have ea : (a : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = (Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' :
        Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (Mu : Matrix (Fin n) (Fin n) Γ(Z.X, U)) := Units.val_mul _ _
    rw [ea, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [map_mul]
    rfl
  simp only [e₂, RingHom.comp_apply] at k0
  simp only [e₁, e₃, Finset.sum_mul, Finset.mul_sum, mul_assoc] at k0 ⊢
  rw [Finset.sum_comm]
  exact k0

end GlobalTheory.LocM.LatNorm
