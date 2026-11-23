import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtensionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.FlagBun

section Model

theorem coordTie_along {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem closure_genField (Ω : Type) [Field Ω] {I : Type} :
    Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) with hF
  have hp : ∀ p : MvPolynomial I Ω, algebraMap _ (FractionRing (MvPolynomial I Ω)) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]
      rfl
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨some i, none, ?_⟩))
      simp
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω) a
  exact div_mem (hp p) (hp q)

end Model

theorem exists_genericFlag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y A y₀ d hy hS hHT hζ hcov
  classical
  haveI : Finite (GenIx (labelRk D)) := by unfold GenIx; infer_instance
  let Ω' := GenField Ω (labelRk D)
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective

  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M₁ : PModel ℤ x :=
    { X := A.X, ξ := A.ξ, s := specZIsTerminal.from _, hover := specZIsTerminal.hom_ext _ _, all := A.all, tie := A.tie }
  let w : Option (GenIx (labelRk D)) → Ω' :=
    fun o => o.elim 1 fun q => algebraMap (MvPolynomial (GenIx (labelRk D)) Ω) Ω' (MvPolynomial.X q)
  obtain ⟨M₂, f₂, hd₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ x M₁ Ω' i _ w (fun a => by simp)
    ⟨none, one_ne_zero⟩ (closure_genField Ω)
  obtain ⟨κ₃, _, y₃, M₃, f₃, hd₃, hN, -, -⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω' _ _ M₂ Ω'
  letI : Fintype κ₃ := Fintype.ofFinite κ₃
  let y' : (Σ _ : Unit, κ₃) → Ω' := fun q => y₃ q.2
  have htie : CoordTie ℤ M₃.ξ (fun c' : (k : Unit) → κ₃ => ∏ k, y' ⟨k, c' k⟩) :=
    coordTie_along M₃.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp [y']
  have hd₃' : M₃.ξ ≫ f₃ = M₂.ξ := by
    have h := hd₃
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
    rw [h, show algebraMap Ω' Ω' = RingHom.id Ω' from rfl, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hdh : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ A.ξ (f₃ ≫ f₂) i := by
    show M₃.ξ ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, hd₃']
    exact hd₂
  have hnormal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₃.X := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' M₃.ξ M₃.tie.gen M₃.all).2.1 hN

  obtain ⟨A', e, j₁, m, he, hf, hm, hcst, hR, hext, hpt, hHT', hV⟩ := GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K Unit
    J (fun _ => κ₃) y y' A y₀ M₃.X M₃.ξ (f₃ ≫ f₂) hy hS (fun p hp => (hHT p hp).2) M₃.all
    (by convert htie using 1 <;> first | exact Subsingleton.elim _ _ | skip) hnormal hdh
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ f₃ ≫ f₂) i := by
    show A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, he]
    exact hdh
  have hf' : A'.f = (e.hom ≫ f₃ ≫ f₂) ≫ A.f := hf.trans (Category.assoc _ _ _).symm
  have hfn : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ₀ A'.f (i.comp A.fn) := by
    have h : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
    have h' : A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := hd'
    show A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom (i.comp A.fn)) ≫ A.ξ₀
    have e1 : A'.ξ ≫ A'.f = (A'.ξ ≫ e.hom ≫ f₃ ≫ f₂) ≫ A.f :=
      (congrArg (A'.ξ ≫ ·) hf').trans (Category.assoc _ _ _).symm
    have e2 : Spec.map (CommRingCat.ofHom (i.comp A.fn)) =
        Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom A.fn) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [e1, h', Category.assoc, h, e2, Category.assoc]
  let 𝔐 : HodgeCpt Y S y' :=
    { A' with Ω₀ := A.Ω₀, fld₀ := A.fld₀, ξ₀ := A.ξ₀, gen₀ := A.gen₀, fn := i.comp A.fn, fn_over := hfn }
  have hy' : 𝔐.ξ ≫ 𝔐.f = (spMap i ≫ y₀) ≫ Y.j := by
    show A'.ξ ≫ A'.f = _
    have h' := hd'
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h'
    rw [hf', ← Category.assoc, h', Category.assoc, hy, Category.assoc]

  obtain ⟨cst₀, y₁, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_constants_generic_point E H D l Xo c Y S Ω' Unit (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) hy'
  obtain ⟨Li₀, _, _, M₀, j, V₀, cb, hj, hsm, hV₀, hcb, hli, hspan⟩ := GlobalTheory.T.constants_compatible_generic E H D l Xo c Y S Ω' Unit
    (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) cst₀ y₁ hy' h₁ h₂ h₃
  have hfin := GlobalTheory.T.finrank_adjoin_vars_field 𝔐.Ω₀ Ω A.fn (GenIx (labelRk D)) d hcov.1 hcov.2
  obtain ⟨hsp, hgen⟩ := GlobalTheory.T.generic_flag_field_change 𝔐.Ω₀ Ω A.fn _ (labelRk D) d hcov.1 hfin Li₀ 𝔐.Li j V₀ cb hcb hsm hli
  refine ⟨Ω', inferInstance, inferInstance, i, Unit, inferInstance, fun _ => κ₃, inferInstance, y', 𝔐,
    e.hom ≫ f₃ ≫ f₂, _, Li₀, _, _, M₀, j, V₀, hd', hf', hR, fun p hp => ⟨?_, hHT' p hp⟩,
    fun s => (hsp s).trans (hspan s), hj, hV₀, hgen⟩
  exact GlobalTheory.T.hodge_comp_field_extension hW E H D l Xo c Y S Ω Ω' i K Unit J (fun _ => κ₃) y y' A 𝔐 (e.hom ≫ f₃ ≫ f₂) m j₁ y₀ p hp hd' hf' hR
    hext hpt hy (hζ p hp) (hHT p hp).1

end GlobalTheory.CompanionTheory.Ar.GenFlag
