import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open Formalism.L2.Pj (FrPt FrMap Rul evR sOf embK Ix FromTest EvalWD IsNatural TRing)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Labels

def labelC : CMType H ⊕ CMType H → (E →+* ℂ)
  | .inl τ => τ.1
  | .inr τ => conjEmb τ.1

@[simp] theorem labelC_inl (τ : CMType H) : labelC (.inl τ) = τ.1 := rfl

@[simp] theorem labelC_inr (τ : CMType H) : labelC (.inr τ) = conjEmb τ.1 := rfl

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have : (H.d : ℂ) = 0 := by simpa using h2
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem conjEmb_rt_ne (τ : CMType H) : conjEmb τ.1 (H.rt : E) ≠ H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ (τ.1 (H.rt : E)) = H.rt0 := h
  rw [τ.2, rt0_conj_neg_ne_zero] at h1
  exact rt0_ne_zero H (by linear_combination (-1 / 2 : ℂ) * h1)

theorem conjEmb_rt_of_ne {σ : E →+* ℂ} (h : σ (H.rt : E) ≠ H.rt0) : conjEmb σ (H.rt : E) = H.rt0 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, h1, H.sqrt_neg_disc_sq]; simp
  have h3 : σ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h
  show starRingEnd ℂ (σ (H.rt : E)) = H.rt0
  rw [h3, map_neg, rt0_conj_neg_ne_zero, neg_neg]

theorem conjEmb_conjEmb (σ : E →+* ℂ) : conjEmb (conjEmb σ) = σ := by
  ext x; simp [conjEmb]

theorem labelC_bijective (H : Host E) : Function.Bijective (labelC (H := H)) := by
  refine ⟨?_, fun σ => ?_⟩
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd ((show τ.1 = conjEmb τ'.1 from h) ▸ τ.2) (conjEmb_rt_ne τ')
    · exact absurd ((show τ'.1 = conjEmb τ.1 from h.symm) ▸ τ'.2) (conjEmb_rt_ne τ)
    · refine congrArg _ (Subtype.ext ?_)
      rw [← conjEmb_conjEmb τ.1, ← conjEmb_conjEmb τ'.1]
      exact congrArg conjEmb h
  · by_cases h : σ (H.rt : E) = H.rt0
    · exact ⟨.inl ⟨σ, h⟩, rfl⟩
    · exact ⟨.inr ⟨conjEmb σ, conjEmb_rt_of_ne h⟩, conjEmb_conjEmb σ⟩

def labelEquiv (H : Host E) : CMType H ⊕ CMType H ≃ (E →+* ℂ) := Equiv.ofBijective labelC (labelC_bijective H)

theorem mult_labelC (D : Datum H) (s : CMType H ⊕ CMType H) : D.mult (labelC s) = labelRk D s := by
  rcases s with τ | τ
  · exact if_pos τ.2
  · exact if_neg (conjEmb_rt_ne τ)

theorem embK_labelC (c : Coeff l) (s : CMType H ⊕ CMType H) : embK c (labelC s) = labelEmb c s := by
  rcases s with τ | τ
  · rfl
  · ext a
    show starRingEnd ℂ (τ.1 (a : E)) = τ.1 ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def labelFin (D : Datum H) (s : CMType H ⊕ CMType H) (i : Fin (labelRk D s)) : Fin (D.mult (labelC s)) :=
  Fin.cast (mult_labelC D s).symm i

@[simp] theorem labelFin_val (D : Datum H) (s : CMType H ⊕ CMType H) (i : Fin (labelRk D s)) :
    (labelFin D s i : ℕ) = i := rfl

theorem exists_labelFin (D : Datum H) (σ : E →+* ℂ) (i : Fin (D.mult σ)) :
    ∃ (s : CMType H ⊕ CMType H) (k : Fin (labelRk D s)),
      (⟨labelC s, labelFin D s k⟩ : Σ τ : E →+* ℂ, Fin (D.mult τ)) = ⟨σ, i⟩ := by
  obtain ⟨s, rfl⟩ := (labelC_bijective H).2 σ
  exact ⟨s, Fin.cast (mult_labelC D s) i, rfl⟩

def labelIx (D : Datum H) (q : Σ s, Fin (labelRk D s)) : Ix D := some ⟨labelC q.1, labelFin D q.1 q.2⟩

def rootFrameIx (D : Datum H) (r : RootIx D) : Ix D := labelIx D (HodgeCpt.rootIdx D r)

end Labels

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {S : Type} [CommRing S] [Algebra c.F S]

def ptF (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, sOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

@[reassoc (attr := simp)] theorem ptF_fst (y : FrPt Xo c S) : ptF y ≫ pullback.fst _ _ = y.x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem ptF_snd (y : FrPt Xo c S) :
    ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
  pullback.lift_snd _ _ _

variable (Y : Model Xo c β)

def ptY (y : FrPt Xo c S) : Sp S ⟶ Y.X := ptF y ≫ Y.j

theorem ptY_over (y : FrPt Xo c S) : ptY Y y ≫ Y.s = spMap ((algebraMap c.F S).comp β) := by
  rw [ptY, Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
    ptF_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def tanF (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) : Sp (DualNumber S) ⟶ Y.oF.t.G.left :=
  Y.m0.cart.1.lift (y.u τ i) (spMap (algebraMap S (DualNumber S)) ≫ ptF y) (by
    rw [(y.tan τ i).1, Category.assoc, ptF_fst])

@[reassoc (attr := simp)] theorem tanF_φ (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) :
    tanF Y y τ i ≫ Y.m0.toSABMap.φ = y.u τ i :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)] theorem tanF_hom (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) :
    tanF Y y τ i ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ ptF y :=
  IsPullback.lift_snd _ _ _ _

theorem eq_tanF (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) (w : Sp (DualNumber S) ⟶ Y.oF.t.G.left)
    (h₁ : w ≫ Y.m0.toSABMap.φ = y.u τ i)
    (h₂ : w ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ ptF y) : w = tanF Y y τ i :=
  Y.m0.cart.1.hom_ext (h₁.trans (tanF_φ Y y τ i).symm) (h₂.trans (tanF_hom Y y τ i).symm)

def tanY (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) : Sp (DualNumber S) ⟶ Y.t.G.left :=
  tanF Y y τ i ≫ Y.m.φ

theorem tanY_hom (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (D.mult τ)) :
    tanY Y y τ i ≫ Y.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ ptY Y y := by
  rw [tanY, Category.assoc, Y.m.cart.1.w, tanF_hom_assoc]
  rfl

theorem ptF_eq_of_ptY_eq {y y' : FrPt Xo c S} (h : ptY Y y = ptY Y y') : ptF y = ptF y' := by
  haveI := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · simpa only [ptY, Model.j, Category.assoc] using h
  · simp only [Category.assoc, Y.jQ_over, ptF_snd]

theorem u_eq_of_tanY_eq {y y' : FrPt Xo c S} (h : ptY Y y = ptY Y y') {τ : E →+* ℂ} {i : Fin (D.mult τ)}
    (h' : tanY Y y τ i = tanY Y y' τ i) : y.u τ i = y'.u τ i := by
  have : tanF Y y τ i = tanF Y y' τ i :=
    Y.m.cart.1.hom_ext h' (by rw [tanF_hom, tanF_hom, ptF_eq_of_ptY_eq Y h])
  rw [← tanF_φ Y y, this, tanF_φ]

variable {T : Type} [CommRing T] [Algebra c.F T]

theorem ptF_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptF_fst, ptF_fst, h.1]
  · rw [Category.assoc, ptF_snd, ptF_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap.symm

theorem ptY_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptY Y z = spMap φ.toRingHom ≫ ptY Y y := by
  rw [ptY, ptY, ptF_map h, Category.assoc]

theorem tanY_map {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (τ : E →+* ℂ)
    (i : Fin (D.mult τ)) : tanY Y z τ i = spMap (dualMap φ.toRingHom) ≫ tanY Y y τ i := by
  rw [tanY, tanY, ← Category.assoc, eq_tanF Y z τ i (spMap (dualMap φ.toRingHom) ≫ tanF Y y τ i)]
  · rw [Category.assoc, tanF_φ, h.2.1]
    rfl
  · rw [Category.assoc, tanF_hom, ptF_map h, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end Model

section Gen

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

abbrev cstAlg (Or : RootOrigin Y S RM Fx) : Algebra c.F RM.Ω := Or.𝔐.cst.toAlgebra

structure GenFrame (Or : RootOrigin Y S RM Fx) where

  y₀ : letI := cstAlg Or; FrPt Xo c RM.Ω
  pt_eq : letI := cstAlg Or; ptY Y y₀ = Or.𝔐.ξ ≫ Or.𝔐.f
  tan_eq : letI := cstAlg Or; ∀ s i,
    tanY Y y₀ (labelC s) (labelFin D s i) = (Or.𝔐.M.pt (Or.Fl.b s i)).left ≫ Or.𝔐.m.φ
  test : letI := cstAlg Or
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₀

namespace GenFrame

variable {Or : RootOrigin Y S RM Fx} (Fr : GenFrame Or)

def rd (f : Rul Xo c) : RM.Ω := letI := cstAlg Or; evR Xo c f Fr.y₀

@[simp] theorem rd_zero : Fr.rd 0 = 0 := letI := cstAlg Or; Formalism.L2.Pj.evalAt_zero _ _ _

@[simp] theorem rd_one : Fr.rd 1 = 1 := letI := cstAlg Or; Formalism.L2.Pj.evalAt_one _ _ _ Fr.test

theorem rd_add (f g : Rul Xo c) : Fr.rd (f + g) = Fr.rd f + Fr.rd g :=
  letI := cstAlg Or; Formalism.L2.Pj.evalAt_add _ _ f g _

theorem rd_mul (f g : Rul Xo c) : Fr.rd (f * g) = Fr.rd f * Fr.rd g :=
  letI := cstAlg Or; Formalism.L2.Pj.evalAt_mul _ _ f g _

set_option synthInstance.maxHeartbeats 200000 in

theorem rd_smul (a : c.F) (f : Rul Xo c) : Fr.rd (a • f) = Or.𝔐.cst a * Fr.rd f :=
  letI := cstAlg Or; Formalism.L2.Pj.evalAt_smul _ _ a f _

def rdHom : Rul Xo c →+* RM.Ω where
  toFun := Fr.rd
  map_one' := Fr.rd_one
  map_mul' := Fr.rd_mul
  map_zero' := Fr.rd_zero
  map_add' := Fr.rd_add

@[simp] theorem rdHom_apply (f : Rul Xo c) : Fr.rdHom f = Fr.rd f := rfl

theorem rd_pow (f : Rul Xo c) (n : ℕ) : Fr.rd (f ^ n) = Fr.rd f ^ n := map_pow Fr.rdHom f n

theorem rd_sum {I : Type} (s : Finset I) (f : I → Rul Xo c) : Fr.rd (∑ i ∈ s, f i) = ∑ i ∈ s, Fr.rd (f i) :=
  map_sum Fr.rdHom f s

theorem exists_spread : letI := cstAlg Or
    ∃ (p : TRing c.F) (φ : p.R →ₐ[c.F] RM.Ω) (y : FrPt Xo c p.R), FrMap φ y Fr.y₀ ∧ ∀ f, Fr.rd f = φ (f p y) := by
  letI := cstAlg Or
  refine ⟨_, _, _, Fr.test.choose_spec.choose_spec.choose_spec, fun f => ?_⟩
  exact dif_pos Fr.test

theorem rd_eq_of_frMap (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    (p : TRing c.F) : letI := cstAlg Or
    ∀ (φ : p.R →ₐ[c.F] RM.Ω) (y : FrPt Xo c p.R), FrMap φ y Fr.y₀ → Fr.rd f = φ (f p y) := by
  letI := cstAlg Or
  intro φ y h
  obtain ⟨q, ψ, z, hz, hr⟩ := Fr.exists_spread
  rw [hr]
  exact hWD f hf _ q p ψ φ z y _ hz h

theorem x_eq (Fr' : GenFrame Or) : letI := cstAlg Or; Fr.y₀.x = Fr'.y₀.x := by
  letI := cstAlg Or
  rw [← ptF_fst Fr.y₀, ← ptF_fst Fr'.y₀, ptF_eq_of_ptY_eq Y (Fr.pt_eq.trans Fr'.pt_eq.symm)]

theorem u_eq (Fr' : GenFrame Or) : letI := cstAlg Or; Fr.y₀.u = Fr'.y₀.u := by
  letI := cstAlg Or
  funext σ i
  obtain ⟨s, rfl⟩ := (labelC_bijective H).2 σ
  exact u_eq_of_tanY_eq Y (Fr.pt_eq.trans Fr'.pt_eq.symm)
    ((Fr.tan_eq s (Fin.cast (mult_labelC D s) i)).trans (Fr'.tan_eq s (Fin.cast (mult_labelC D s) i)).symm)

set_option synthInstance.maxHeartbeats 200000 in

example (a : c.F) : Fr.rd (algebraMap c.F (Rul Xo c) a) = Or.𝔐.cst a := by
  rw [Algebra.algebraMap_eq_smul_one, rd_smul, rd_one, _root_.mul_one]

end GenFrame

end Gen

example (τ : CMType H) : D.mult (conjEmb τ.1) = D.q := mult_labelC D (.inr τ)

example (τ : CMType H) (hp : 0 < D.p) :
    rootFrameIx D (τ, ⟨0, by omega⟩) = labelIx D ⟨.inl τ, ⟨0, hp⟩⟩ := by
  simp [rootFrameIx, HodgeCpt.rootIdx, hp]

example (τ : CMType H) (hq : 0 < D.q) :
    rootFrameIx D (τ, ⟨D.p + D.q - 1, by omega⟩) = labelIx D ⟨.inr τ, ⟨0, hq⟩⟩ := by
  have h : ¬ D.p + D.q - 1 < D.p := by omega
  simp [rootFrameIx, HodgeCpt.rootIdx, h]

end GlobalTheory.CompanionTheory.Ar.Small
