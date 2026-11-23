import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtRing

theorem qCast_trans {a p q : ℕ} [Fact a.Prime] [Fact p.Prime] [Fact q.Prime] (ι : Qbar a ≃+* ℂ) (h₀ : a = p)
    (h₁ : a = q) (hl : p = q) : qCast h₁ ι = qCast hl (qCast h₀ ι) := by
  subst h₀; subst hl; rfl

theorem exists_gens {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ s : Finset (Qbar l), ∀ x, ι x ∈ Submodule.span ℚ_[l] (s : Set (Qbar l)) := by
  classical
  obtain ⟨K, hK, hfd, -⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι hι
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℚ_[l] K).FG)
  refine ⟨t.image Subtype.val, fun x => ?_⟩
  have hx : (⟨ι x, (hK _).2 ⟨x, rfl⟩⟩ : K) ∈ Submodule.span ℚ_[l] (t : Set K) := ht ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := K.val.toLinearMap) hx
  rw [← Submodule.span_image] at this
  rw [Finset.coe_image]
  exact this

theorem exists_ringHom {l₀ l₁ : ℕ} [Fact l₀.Prime] [Fact l₁.Prime] (hl : l₀ = l₁)
    {O₀ : Type} [cr₀ : CommRing O₀] [dm₀ : IsDomain O₀] [dv₀ : IsDiscreteValuationRing O₀] [al₀ : Algebra ℤ_[l₀] O₀]
    [fi₀ : Module.Finite ℤ_[l₀] O₀]
    {O₁ : Type} [cr₁ : CommRing O₁] [dm₁ : IsDomain O₁] [dv₁ : IsDiscreteValuationRing O₁] [al₁ : Algebra ℤ_[l₁] O₁]
    [fi₁ : Module.Finite ℤ_[l₁] O₁]
    (ι₀ : FractionRing O₀ →+* Qbar l₀)
    (hι₀ : ∀ z : ℤ_[l₀], ι₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) =
      algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀]))
    (ι₁ : FractionRing O₁ →+* Qbar l₁)
    (hι₁ : ∀ z : ℤ_[l₁], ι₁ (algebraMap O₁ (FractionRing O₁) (algebraMap ℤ_[l₁] O₁ z)) =
      algebraMap ℚ_[l₁] (Qbar l₁) (z : ℚ_[l₁]))
    (c₀ : Qbar l₀ ≃+* ℂ) (c₁ : Qbar l₁ ≃+* ℂ) (hc : c₁ = qCast hl c₀) (s : Set (Qbar l₀))
    (hs : ∀ x, ι₀ x ∈ Submodule.span ℚ_[l₀] s) (hs₁ : ∀ y ∈ s, ∃ x, c₁ (ι₁ x) = c₀ y) :
    ∃ φ : O₀ →+* O₁, (∀ z, c₁ (ι₁ (algebraMap O₁ _ (φ z))) = c₀ (ι₀ (algebraMap O₀ _ z))) ∧
      ∀ (z : ℤ_[l₀]) (z' : ℤ_[l₁]), HEq z z' → φ (algebraMap ℤ_[l₀] O₀ z) = algebraMap ℤ_[l₁] O₁ z' := by
  subst hl
  have hc' : ∀ x, c₁ x = c₀ x := fun x => by rw [hc]; rfl
  simp only [hc'] at hs₁ ⊢
  obtain ⟨K₀, hK₀, -, hn₀⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₀ hι₀
  obtain ⟨K₁, hK₁, -, hn₁⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₁ hι₁
  have hsK : s ⊆ (K₁ : Set (Qbar l₀)) := by
    intro y hy
    obtain ⟨x, hx⟩ := hs₁ y hy
    exact (hK₁ y).2 ⟨x, c₀.injective hx⟩
  have hspan : Submodule.span ℚ_[l₀] s ≤ K₁.toSubalgebra.toSubmodule := Submodule.span_le.2 hsK
  let f₀ : O₀ →+* Qbar l₀ := ι₀.comp (algebraMap O₀ (FractionRing O₀))
  let f₁ : O₁ →+* Qbar l₀ := ι₁.comp (algebraMap O₁ (FractionRing O₁))
  have hf₁ : Function.Injective f₁ := ι₁.injective.comp (IsFractionRing.injective O₁ (FractionRing O₁))
  have hrange : ∀ z, f₀ z ∈ f₁.range := by
    intro z
    have h1 : f₀ z ∈ K₁ := hspan (hs _)
    obtain ⟨y, hy⟩ := (hK₁ _).1 h1
    have hle : ‖ι₀ (algebraMap O₀ (FractionRing O₀) z)‖ ≤ 1 := (hn₀ _).2 ⟨z, rfl⟩
    have hy1 : ‖ι₁ y‖ ≤ 1 := by rw [hy]; exact hle
    obtain ⟨u, rfl⟩ := (hn₁ y).1 hy1
    exact ⟨u, hy⟩
  let e₁ : O₁ ≃+* f₁.range := RingEquiv.ofBijective f₁.rangeRestrict
    ⟨fun a b h => hf₁ (congrArg Subtype.val h), f₁.rangeRestrict_surjective⟩
  let φ : O₀ →+* O₁ := e₁.symm.toRingHom.comp (f₀.codRestrict f₁.range hrange)
  have hφ : ∀ z, f₁ (φ z) = f₀ z := by
    intro z
    have : e₁ (φ z) = f₀.codRestrict f₁.range hrange z := e₁.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨φ, fun z => congrArg c₀ (hφ z), fun z z' hzz => ?_⟩
  cases eq_of_heq hzz
  apply hf₁
  rw [hφ]
  change ι₀ _ = ι₁ _
  rw [hι₀, hι₁]

end GlobalTheory.CoefDuty.ExtRing

end

open GlobalTheory.CoefDuty.ExtRing in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.CoefDuty.ExtRing.ext_ring : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), Built A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  classical
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ L₀ hB₀
  obtain ⟨Sp₀, ⟨Au₀⟩, -⟩ := hB₀
  have hg := fun i => exists_gens (Sp₀.iq i) (Sp₀.iq_alg i)
  let gens : ∀ i : L₀.X.nd.Loc, Finset (Qbar (L₀.X.nd.l i)) := fun i => Classical.choose (hg i)
  have hgens : ∀ i x, Sp₀.iq i x ∈ Submodule.span ℚ_[L₀.X.nd.l i] (gens i : Set (Qbar (L₀.X.nd.l i))) :=
    fun i => Classical.choose_spec (hg i)
  let big₁ : D.what₂.places.Pl → Finset ℂ := fun w => (Finset.Icc 1 D.R.m).biUnion fun j =>
    (L₀.X.nd.locs j w).biUnion fun i => (gens i).image fun y => qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y
  have hbig : ∀ i y, y ∈ gens i → qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y ∈ big₁ (L₀.X.nd.w i) := by
    intro i y hy
    refine Finset.mem_biUnion.2 ⟨L₀.X.nd.j i, Finset.mem_Icc.2 (L₀.X.nd.j_range i), ?_⟩
    exact Finset.mem_biUnion.2 ⟨i, (L₀.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, Finset.mem_image_of_mem _ hy⟩
  refine ⟨big₁, fun L₁ hB₁ i₀ i₁ hw => ?_⟩
  obtain ⟨Sp₁, ⟨Au₁⟩, -⟩ := hB₁
  change L₀.X.nd.w i₀ = L₁.X.nd.w i₁ at hw
  have hl : L₀.X.nd.l i₀ = L₁.X.nd.l i₁ := by
    exact (L₀.X.nd.w_l i₀).symm.trans ((congrArg _ hw).trans (L₁.X.nd.w_l i₁))
  haveI := L₀.X.nd.lPrime i₀
  haveI := L₁.X.nd.lPrime i₁
  have key : ∀ w (_ : L₀.X.nd.w i₀ = w) (h₁ : D.what₂.places.resChar w = L₁.X.nd.l i₁),
      qCast h₁ (A.pl.ι w) = qCast hl (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) := by
    intro w hw' h₁
    subst hw'
    exact qCast_trans _ _ _ _
  obtain ⟨φ, h1, h2⟩ := exists_ringHom (O₀ := L₀.X.nd.O i₀) (O₁ := L₁.X.nd.O i₁)
    (cr₀ := L₀.X.nd.instO i₀) (dm₀ := L₀.X.nd.domO i₀) (dv₀ := L₀.X.nd.dvrO i₀) (al₀ := L₀.X.nd.algO i₀) (fi₀ := L₀.X.nd.finO i₀)
    (cr₁ := L₁.X.nd.instO i₁) (dm₁ := L₁.X.nd.domO i₁) (dv₁ := L₁.X.nd.dvrO i₁) (al₁ := L₁.X.nd.algO i₁) (fi₁ := L₁.X.nd.finO i₁) hl (Sp₀.iq i₀) (Sp₀.iq_alg i₀) (Sp₁.iq i₁) (Sp₁.iq_alg i₁)
    (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁)))
    (key _ hw _) _ (hgens i₀) (fun y hy => Sp₁.iq_big i₁ _ (hw ▸ hbig i₀ y hy))
  refine ⟨φ, fun z => ?_, h2⟩
  have e₀ := fun x => (congrArg (fun g : Qbar (L₀.X.nd.l i₀) ≃+* ℂ => g (L₀.Y.naut.iotaQ i₀ x)) (Au₀.iotaQC i₀)).trans
    (congrArg (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (DFunLike.congr_fun (Au₀.iotaQ i₀) x))
  have e₁ := fun x => (congrArg (fun g : Qbar (L₁.X.nd.l i₁) ≃+* ℂ => g (L₁.Y.naut.iotaQ i₁ x)) (Au₁.iotaQC i₁)).trans
    (congrArg (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁))) (DFunLike.congr_fun (Au₁.iotaQ i₁) x))
  exact (e₁ _).trans ((h1 z).trans (e₀ _).symm)
