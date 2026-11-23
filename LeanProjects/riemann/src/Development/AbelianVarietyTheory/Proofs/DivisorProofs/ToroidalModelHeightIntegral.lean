import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem mono_of_matches : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d → IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ {M M' : X.Modules} {r : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB) (u : M ⟶ M'),
    IsVB M r → IsVB M' r → IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    Matches Z jB πB u t t' → Mono u := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hW M M' r τ t t' u hM hM' ht ht' hm
  refine GlobalTheory.QCoh.mono_of_locally_app_injective u fun W₀ x hx => ?_
  obtain ⟨V, f, f', hf, hf', -, hxV⟩ := GlobalTheory.CommonFrames.exists_common_affine_frames X M M' r hM hM' x
  refine ⟨V ⊓ W₀, ⟨hxV, hx⟩, inf_le_right, ?_⟩
  have hUV : V ⊓ W₀ ≤ V := inf_le_left
  have hfU := hf.res hUV
  have hf'U := hf'.res hUV
  let fU : Fin r → Γ(M, V ⊓ W₀) := fun i => Twist.resM M hUV (f i)
  let f'U : Fin r → Γ(M', V ⊓ W₀) := fun i => Twist.resM M' hUV (f' i)
  let A : Matrix (Fin r) (Fin r) Γ(X, V ⊓ W₀) := fun b i =>
    (hf'U.basis le_rfl).repr (Twist.resM M' le_rfl (u.app (V ⊓ W₀) (fU i))) b
  have key : ∀ a : Fin r → Γ(X, V ⊓ W₀), (∀ b, ∑ i, A b i * a i = 0) → a = 0 := by
    intro a ha
    rcases ((V ⊓ W₀ : X.Opens) : Set X).eq_empty_or_nonempty with hV | hV
    · have hb : V ⊓ W₀ = ⊥ := TopologicalSpace.Opens.coe_eq_empty.1 hV
      haveI : Subsingleton Γ(X, V ⊓ W₀) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
      exact Subsingleton.elim _ _
    obtain ⟨K, _, y, ψ, hψ, h, hinj⟩ := GlobalTheory.ArLieBase.exists_generic_evalPt_injective hq hW _ hV
    have bf := ht.1 _ fU hfU K y h ψ hψ
    have bf' := ht'.1 _ f'U hf'U K y h ψ hψ
    let T := fun i => LieMet.tanOf (bf.1 i).1
    let T' := fun b => LieMet.tanOf (bf'.1 b).1
    have hT : ∀ i, T i = ∑ b, TangentOrigin.evalPt (y ≫ jB) _ h (A b i) • T' b := fun i =>
      (LieMet.isComb_iff T' _ (T i)).1 (hm _ fU f'U hfU hf'U K y h i)
    have h0 : ∑ i, TangentOrigin.evalPt (y ≫ jB) _ h (a i) • T i = 0 := by
      simp only [hT, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [← Finset.sum_smul]
      have e1 : ∑ i, TangentOrigin.evalPt (y ≫ jB) _ h (a i) * TangentOrigin.evalPt (y ≫ jB) _ h (A b i) =
          TangentOrigin.evalPt (y ≫ jB) _ h (∑ i, A b i * a i) := by
        simp only [map_sum, map_mul, mul_comm]
      rw [e1, ha b, map_zero, zero_smul]
    funext j
    show a j = 0
    have hj1 : IsCombAtG Z.t (y ≫ πB ≫ genι Z) (t _ fU hfU K y h) (Pi.single j 1) (t _ fU hfU K y h j) :=
      (LieMet.isComb_iff T _ (T j)).2 (by simp [Pi.single_apply])
    have hj2 : IsCombAtG Z.t (y ≫ πB ≫ genι Z) (t _ fU hfU K y h)
        (Pi.single j 1 + fun i => TangentOrigin.evalPt (y ≫ jB) _ h (a i)) (t _ fU hfU K y h j) :=
      (LieMet.isComb_iff T _ (T j)).2 (by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, h0, add_zero]
        simp [Pi.single_apply])
    have e2 := congrFun ((bf.2 _ (bf.1 j)).unique hj1 hj2) j
    have hz : TangentOrigin.evalPt (y ≫ jB) _ h (a j) = 0 := by simpa using e2
    exact hinj (by rw [hz, map_zero])
  intro s s' hss
  rw [← sub_eq_zero]
  let a := (hfU.basis le_rfl).repr (s - s')
  have hs : s - s' = ∑ i, a i • fU i := by
    conv_lhs => rw [← (hfU.basis le_rfl).sum_repr (s - s')]
    exact Finset.sum_congr rfl fun i _ => by rw [VB.IsFrame.basis_apply, Twist.resM_self]
  have hd : u.app (V ⊓ W₀) (s - s') = 0 := by simp [hss]
  have hz : ∀ b, ∑ i, A b i * a i = 0 := by
    intro b
    have e0 : (hf'U.basis le_rfl).repr (u.app (V ⊓ W₀) (s - s')) b = 0 := by rw [hd, map_zero]; rfl
    rw [hs] at e0
    simp only [map_sum, Scheme.Modules.Hom.app_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at e0
    rw [← e0]
    exact Finset.sum_congr rfl fun i _ => by simp only [A, Twist.resM_self]; exact mul_comm _ _
  have ha := key a hz
  rw [hs]
  simp [ha]

end GlobalTheory.LieFilt

end
