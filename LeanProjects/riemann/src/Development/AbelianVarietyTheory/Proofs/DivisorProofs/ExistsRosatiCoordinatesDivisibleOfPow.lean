import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleScalarSecondSlotConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTripleStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
