import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensorsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem IsKForm.map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D₁ D : Datum H} {ε : ℤˣ}
    {h₁ : D₁.La → D₁.La → OK H} {h : D.La → D.La → OK H} (k₁ : IsKForm D₁ ε h₁) (k : IsKForm D ε h)
    {L : Submodule (𝓞 E) D.La} (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E) (hf : ∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b)
    (a b : D₁.La) : h (f a) (f b) = h₁ (c • a) b := by
  apply Subtype.ext
  have e : H.w0 • ((f a : L) : D.La) = ((f (H.w0 • a) : L) : D.La) := by rw [map_smul]; rfl
  rw [k, k₁, e, hf, hf, smul_comm c H.w0 a]

theorem exists_famLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  intro E _ _ _ H R _ ω C D₁ D ε h₁ h T₁ T t L ψ f c k₁ k hf ⟨l, hadd, hsmul, hlam⟩
  let F : D₁.La →ₗ[OK H] Serre.Pts (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) C.P.A :=
    { toFun := fun a => Serre.Pts.mk _ (ψ (f a))
      map_add' := fun a b => Serre.Pts.ext (by rw [map_add]; exact hadd _ _)
      map_smul' := fun s a => Serre.Pts.ext (by
        have e : f (s • a) = (s : 𝓞 E) • f a := f.map_smul (s : 𝓞 E) a
        rw [e]; exact hsmul _ _) }
  have hF : ∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (F a).hom :=
    fun a => l (f a)
  have hm : IsMonHom (t.ten.lift F hF) := (t.ten.isLinearHom_lift F hF).isMonHom
  have ht : ∀ a, t.ten.tmul a ≫ t.ten.lift F hF = ψ (f a) := fun a => t.ten.tmul_lift F hF a
  refine ⟨t.ten.lift F hF, ⟨hm, fun s => ?_⟩, ht, ?_⟩
  · have := T₁.t.act.hom s
    have := T.t.act.hom s
    refine t.ten.hom_ext fun a => ?_
    rw [← Category.assoc, ← t.lin, ht, ← Category.assoc, ht, map_smul, hsmul]
  · refine GlobalTheory.T.tensor_pairing_identity_of_pure_tensors _ _ _ _ _ _ _ t.ten _ _ _ t.ten _ _ _ _ _ _ _ _ T.t.PP.isLB T₁.t.PP.isLB
      ⟨T.t.cub.t, T.t.cub.isGen⟩ ⟨T₁.t.cub.t, T₁.t.cub.isGen⟩ hm hm (T₁.t.act.hom c) inferInstance fun a b => ?_
    rw [ht, ht, ← t.lin, Category.comp_id]
    have e := hlam (f a) (f b)
    rw [k₁.map_eq k f c hf] at e
    exact LBIso.trans (LamCalc.cubeLB_isLB T.t.PP.isLB _) (LamCalc.cubeLB_isLB C.P.isLB _)
      (LamCalc.cubeLB_isLB T₁.t.PP.isLB _) e (LBIso.symm (t.lam (c • a) b))

end GlobalTheory.CM
end
