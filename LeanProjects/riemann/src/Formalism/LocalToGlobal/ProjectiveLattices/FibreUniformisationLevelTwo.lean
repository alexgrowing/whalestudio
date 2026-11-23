import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PerFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (v + w) = Data.emb σ v + Data.emb σ w := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_add _ _ _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [Matrix.mulVec_add]; done)
    | (simp [hermC, Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [mul_add, add_mul, Finset.sum_add_distrib, map_add])

theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (0 : Fin r → E) = 0 := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_zero _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [hermC]; done)
    | (unfold hermC; simp)

end PerFr

section Lin

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1

theorem eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (q : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eb e τ i (e.symm q) = if q = ⟨τ, i⟩ then 1 else 0 := by
  by_cases hq : q = ⟨τ, i⟩
  · subst hq
    simp [eb]
  · simp [eb, hq, Pi.single_apply, e.symm.injective.eq_iff]

theorem sum_eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ)
    (c : Fin (Dw.mult τ) → ℂ) (l : Fin (Dw.mult τ)) : (∑ j, c j • eb e τ j) (e.symm ⟨τ, l⟩) = c l := by
  simp [Finset.sum_apply, eb_apply]

theorem sum_single_eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    (∑ j, (Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ) j • eb e τ j) = eb e τ i := by
  simp [Pi.single_apply, ite_smul]

def blkF {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ)
    (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : ℂ :=
  ∑ l, A p.1 p.2 l * z (e.symm ⟨p.1, l⟩)

def blkL {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z j := blkF e A z (e j)
  map_add' z z' := by
    funext j; simp [blkF, mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j; simp [blkF, Finset.mul_sum, mul_left_comm]

theorem blkL_symm {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ)
    (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : blkL e A z (e.symm p) = blkF e A z p := by
  show blkF e A z (e (e.symm p)) = blkF e A z p
  rw [Equiv.apply_symm_apply]

theorem blkL_comp {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ) :
    blkL e A (blkL e B z) = blkL e (fun τ => A τ * B τ) z := by
  funext j
  show blkF e A (blkL e B z) (e j) = blkF e (fun τ => A τ * B τ) z (e j)
  simp only [blkF, blkL_symm, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  first
    | exact Finset.sum_comm
    | (rw [Finset.sum_comm])
    | (conv_lhs => rw [Finset.sum_comm])

theorem blkL_one {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (z : Fin g → ℂ) :
    blkL e (fun _ => 1) z = z := by
  funext j
  show blkF e (fun _ => 1) z (e j) = z j
  simp [blkF, Matrix.one_apply]

def blkE {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det) :
    (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
  LinearEquiv.ofLinear (blkL e A) (blkL e fun τ => (A τ)⁻¹)
    (LinearMap.ext fun z => by
      have h1 : (fun τ => A τ * (A τ)⁻¹) = fun _ => 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hA τ)
      simp only [LinearMap.comp_apply, blkL_comp, h1, blkL_one, LinearMap.id_apply])
    (LinearMap.ext fun z => by
      have h1 : (fun τ => (A τ)⁻¹ * A τ) = fun _ => 1 := funext fun τ => Matrix.nonsing_inv_mul _ (hA τ)
      simp only [LinearMap.comp_apply, blkL_comp, h1, blkL_one, LinearMap.id_apply])

theorem blkE_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det)
    (z : Fin g → ℂ) : blkE e A hA z = blkL e A z := rfl

theorem blkL_col {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (τ : E →+* ℂ)
    (B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hAB : A τ * B = 1) (i : Fin (Dw.mult τ)) :
    blkL e A (∑ l, B l i • eb e τ l) = eb e τ i := by
  funext j
  obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective j
  rw [blkL_symm, eb_apply]
  by_cases ht : τ' = τ
  · subst ht
    simp only [blkF, sum_eb_apply]
    rw [← Matrix.mul_apply, hAB, Matrix.one_apply]
    simp
  · simp [blkF, Finset.sum_apply, eb_apply, ht]

end Lin

section Der

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} {e1 e2 : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e2 (h z) = e1 z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e1 w v) : IsDerivAt0 e2 (h w) v := by
  unfold IsDerivAt0 at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 : h 0 = 0 := map_zero h
  have h3 : e2 0 = e1 0 := by simpa [h0] using he 0
  refine ⟨h1.trans h3.symm, ?_⟩
  intro U hU f
  refine (h2 U hU f).trans ?_
  have hfun : (fun z => valAt' (e1 z) U f) =
      (fun y => valAt' (e2 y) U f) ∘ (LinearEquiv.toContinuousLinearEquiv h) := by
    funext z
    simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp [h0]

end Der

section Fam

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]

def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left

def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v

def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v

def PerDom {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (x : Frame (M.X k).Ψ r), x ∈ (M.X k).dom → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (pmOf e M k x)

def PerOntoX {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P →
      ∃ x ∈ (M.X k).dom, pmOf e M k x = P

def PerFib {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (x x' : Frame (M.X k).Ψ r), x ∈ (M.X k).dom → x' ∈ (M.X k).dom →
      ∀ (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        (∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) →
        (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b, gam a = a + l.M • b) →
        (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, pmOf e M k x' (gam a) = h (pmOf e M k x a)) →
        (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
          eb e τ i = h (∑ j, cf j • eb e τ j)) →
        ∃ g0 ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, x' = rmul (lact g0 x) b

theorem isCombAt_zero {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j))
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v 0 w) : w = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  rw [isCombAt_unique h (isCombAt_epsPt hv 0)]
  simp only [Pi.zero_apply, epsPt_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem isCombAt_empty {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {v : Fin 0 → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin 0 → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) : w = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  first
    | (simp_all [IsCombAt]; done)
    | (unfold IsCombAt at h; skip)

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}

theorem derivAt_exists {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex i P z).left) w v := by
  obtain ⟨v, hv, -⟩ := (F.ex_diff i P hP).1 w
  exact ⟨_, hv⟩

theorem derivAt_unique (hTE : ExpTan e F) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) {w w' : Fin g → ℂ}
    {v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left} (h1 : IsDerivAt0 (fun z => (F.ex i P z).left) w v)
    (h2 : IsDerivAt0 (fun z => (F.ex i P z).left) w' v) : w = w' := by
  have ht := (hTE i P hP w v h1).1
  let v0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsPt (F.u i P) ⟶ Xo.univ.t.G := Over.homMk v ht.1
  exact ((F.ex_diff i P hP).2 v0 h1.1).unique h1 h2

theorem derivAt_of_comb (hL : ExpLin e F) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) {m : ℕ} {w : Fin m → (Fin g → ℂ)}
    {vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)} {cf : Fin m → ℂ}
    {v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left}
    (hvs : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) (hc : IsCombAt (F.u i P) vs cf v) :
    IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v := by
  obtain ⟨v', hv'⟩ := derivAt_exists hP (∑ j, cf j • w j)
  have hc' := hL i P hP m w vs cf v' hvs hv'
  have hvv : v = v' := by
    unfold IsCombAt at hc hc'
    obtain ⟨u, hu1, hu2⟩ := hc
    obtain ⟨u', hu1', hu2'⟩ := hc'
    have huu : u = u' := funext fun j => by
      first
        | exact Over.OverMorphism.ext ((hu1 j).trans (hu1' j).symm)
        | (ext; exact (hu1 j).trans (hu1' j).symm)
    rw [← hu2, ← hu2', huu]
  rw [hvv]
  exact hv'

def blkP {Di : Datum H} (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det)
    (P : Di.La →+ (Fin g → ℂ)) : Di.La →+ (Fin g → ℂ) :=
  (blkE e A hA).toLinearMap.toAddMonoidHom.comp P

theorem blockDiagonal_comp_apply {Di : Datum H} (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hA : ∀ τ, IsUnit (A τ).det) (P : Di.La →+ (Fin g → ℂ)) (a : Di.La) :
    blkP (e := e) A hA P a = blkE e A hA (P a) := rfl

theorem hermForm_mat (Hm N : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Nᵀ * Hm * Nᴴᵀ) z w = hermForm Hm (N *ᵥ z) (N *ᵥ w) := by
  unfold hermForm
  have hs : star (N *ᵥ w) = Nᴴᵀ *ᵥ star w := by
    ext i
    first
      | (simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, mul_comm]; done)
      | (simp [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, star_sum, mul_comm]; done)
      | (simp [Matrix.mulVec, dotProduct, star_sum, star_mul']; done)
  rw [hs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Nᵀ,
    Matrix.vecMul_transpose]

theorem isPeriod_blk {Di : Datum H} (P : Di.La →+ (Fin g → ℂ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det)
    (hP : IsPeriod Di (fun j => relab c σ (e j).1) P) :
    IsPeriod Di (fun j => relab c σ (e j).1) (blkP (e := e) A hA P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  let N : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' ((blkE e A hA).symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hN : ∀ z, N *ᵥ z = (blkE e A hA).symm z := fun z => LinearMap.toMatrix'_mulVec _ z
  refine ⟨?_, ?_, ?_, ?_, Nᵀ * Hm * Nᴴᵀ, ?_, ?_, ?_⟩
  · intro a x i
    rw [blockDiagonal_comp_apply, blockDiagonal_comp_apply, blkE_apply, blkE_apply]
    show blkF e A (P (a • x)) (e i) = _ * blkF e A (P x) (e i)
    simp only [blkF, hlin, Equiv.apply_symm_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · intro x y hxy
    exact hinj ((blkE e A hA).injective hxy)
  · have hsub : ∀ y : (blkP (e := e) A hA P).range, (blkE e A hA).symm (y : Fin g → ℂ) ∈ (P.range : Set (Fin g → ℂ)) := by
      intro y
      obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.1 y.2
      refine AddMonoidHom.mem_range.2 ⟨x, ?_⟩
      rw [← hx, blockDiagonal_comp_apply, LinearEquiv.symm_apply_apply]
    have h1 : Topology.IsEmbedding (fun y : (blkP (e := e) A hA P).range => (blkE e A hA).symm (y : Fin g → ℂ)) :=
      ((blkE e A hA).symm.toContinuousLinearEquiv.toHomeomorph.isEmbedding).comp Topology.IsEmbedding.subtypeVal
    have : DiscreteTopology (P.range : Set (Fin g → ℂ)) := hdisc
    exact (h1.codRestrict _ hsub).discreteTopology
  · have hr : Set.range (blkP (e := e) A hA P) =
        (((blkE e A hA).restrictScalars ℝ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ''
          Set.range P := by
      ext y
      simp [blockDiagonal_comp_apply]
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · have hK : (Nᴴᵀ)ᴴ = Nᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [← hK]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hH
  · intro z hz
    rw [hermForm_mat, hN]
    exact hpos _ (fun h0 => hz ((LinearEquiv.map_eq_zero_iff _).1 h0))
  · intro x y
    rw [hermForm_mat, hN, hN, blockDiagonal_comp_apply, blockDiagonal_comp_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact him x y

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem coverTri_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (hMB : ModelBase M) (hR : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1))
    (hT : TanLin Xo) (hU : ExpUniq e F) (hL : ExpLin e F) (hTE : ExpTan e F) (hOX : PerOntoX e F M) :
    CoverTri e F M := by
  intro y
  obtain ⟨k, P0, hP0, hu0⟩ := F.onto y.x y.x_over
  choose D1 hD1 using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => derivAt_exists hP0 (eb e τ i)
  have htan : ∀ τ i, IsTanAt y.x (D1 τ i) := fun τ i => by
    have := (hTE k _ hP0 _ _ (hD1 τ i)).1
    rw [hu0] at this
    exact this
  have heig : ∀ τ i, IsEigAt c τ (D1 τ i) := fun τ i => by
    have := (hTE k _ hP0 _ _ (hD1 τ i)).2 (e.symm ⟨τ, i⟩) rfl
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hbas : ∀ τ (i : Fin (Dw.mult τ)), ∃ a : Fin (Dw.mult τ) → CAt σ, IsCombAt y.x (y.u τ) a (D1 τ i) :=
    fun τ i => (y.basis τ _ (htan τ i) (heig τ i)).exists
  choose Acol hAcol using hbas
  let A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := fun τ => Matrix.of fun i l => Acol τ l i
  have hAc : ∀ τ l, IsCombAt y.x (y.u τ) (fun j => A τ j l) (D1 τ l) := fun τ l => hAcol τ l
  have hzero : ∀ τ (cv : Fin (Dw.mult τ) → ℂ), (A τ).mulVec cv = 0 → cv = 0 := by
    intro τ cv hcv
    obtain ⟨w0, hw0⟩ := derivAt_exists hP0 (∑ l, cv l • eb e τ l)
    have h1 : IsCombAt (F.u k P0) (D1 τ) cv w0 := hL k _ hP0 _ _ _ cv w0 (hD1 τ) hw0
    rw [hu0] at h1
    have h2 : IsCombAt y.x (y.u τ) ((A τ).mulVec cv) w0 :=
      hT (CAt σ) y.x (y.u τ) (y.tan τ) (D1 τ) (A τ) cv w0 (hAc τ) h1
    rw [hcv] at h2
    have hw1 := isCombAt_zero (y.tan τ) h2
    obtain ⟨w00, hw00⟩ := derivAt_exists hP0 0
    have h3 : IsCombAt (F.u k P0) (Fin.elim0 : Fin 0 → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
        (Fin.elim0 : Fin 0 → ℂ) w00 :=
      hL k _ hP0 0 Fin.elim0 Fin.elim0 Fin.elim0 w00 (fun j => j.elim0) (by simpa using hw00)
    rw [hu0] at h3
    have hw2 := isCombAt_empty h3
    have hw12 : w0 = w00 := hw1.trans hw2.symm
    have h4 : IsDerivAt0 (fun z => (F.ex k P0 z).left) 0 w0 := by
      rw [hw12]
      exact hw00
    have h5 := derivAt_unique hTE hP0 hw0 h4
    funext l
    have := congrFun h5 (e.symm ⟨τ, l⟩)
    rw [sum_eb_apply] at this
    simpa using this
  have hunit : ∀ τ, IsUnit (A τ).det := fun τ => by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro c1 c2 h12
    have := hzero τ (c1 - c2) (by rw [Matrix.mulVec_sub, h12, sub_self])
    exact sub_eq_zero.1 this
  have hAB : ∀ τ, A τ * (A τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (hunit τ)
  have hyD : ∀ τ (i : Fin (Dw.mult τ)),
      IsDerivAt0 (fun z => (F.ex k P0 z).left) (∑ l, (A τ)⁻¹ l i • eb e τ l) (y.u τ i) := by
    intro τ i
    obtain ⟨w', hw'⟩ := isCombAt_exists (htan τ) (fun l => (A τ)⁻¹ l i)
    have h2 : IsCombAt y.x (y.u τ) ((A τ).mulVec fun l => (A τ)⁻¹ l i) w' :=
      hT (CAt σ) y.x (y.u τ) (y.tan τ) (D1 τ) (A τ) _ w' (hAc τ) hw'
    have hcol : ((A τ).mulVec fun l => (A τ)⁻¹ l i) = (Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ) := by
      funext j
      have := congrFun (congrFun (hAB τ) j) i
      rw [Matrix.mul_apply] at this
      show ∑ l, A τ j l * (A τ)⁻¹ l i = (Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ) j
      rw [this, Matrix.one_apply, Pi.single_apply]
    rw [hcol] at h2
    have h3 : w' = y.u τ i := isCombAt_unique h2 (isCombAt_single (y.tan τ) i)
    rw [← h3]
    have hw'' : IsCombAt (F.u k P0) (D1 τ) (fun l => (A τ)⁻¹ l i) w' := by
      rw [hu0]
      exact hw'
    exact derivAt_of_comb hL hP0 (hD1 τ) hw''
  have hP2 := isPeriod_blk P0 A hunit hP0
  have hrel : ∀ a, blkP (e := e) A hunit P0 (LinearEquiv.refl (𝓞 E) (F.Di k).La a) =
      blkE e A hunit (P0 a) := fun a => rfl
  have hx2 : F.u k (blkP (e := e) A hunit P0) = F.u k P0 :=
    ((F.fibre k _ _ hP0 hP2).2 ⟨LinearEquiv.refl _ _, blkE e A hunit, fun a b => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, hrel⟩).symm
  have hex := hU k _ _ hP0 hP2 (LinearEquiv.refl _ _) (blkE e A hunit) (fun a b => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) hrel
  obtain ⟨x', hx', hxe⟩ := hOX hMB hR k _ hP2
  refine ⟨k, ⟨x', hx'⟩, blkP (e := e) A hunit P0, fun a j => by rw [← hxe]; rfl, hx2.trans hu0,
    fun v hv τ i => ?_⟩
  have hd : IsDerivAt0 (fun z => (F.ex k (blkP (e := e) A hunit P0) z).left) (eb e τ i) (y.u τ i) := by
    have := isDerivAt0_comp (e1 := fun z => (F.ex k P0 z).left)
      (e2 := fun z => (F.ex k (blkP (e := e) A hunit P0) z).left) (blkE e A hunit) hex (hyD τ i)
    rw [blkE_apply, blkL_col e A τ _ (hAB τ) i] at this
    exact this
  have hd' : IsDerivAt0 (fun z => (F.ex k (blkP (e := e) A hunit P0) z).left)
      (∑ j, (Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ) j • eb e τ j) (y.u τ i) := by
    rw [sum_single_eb]
    exact hd
  have hc := hL k _ hP2 _ (eb e τ) (v τ) _ (y.u τ i) (hv τ) hd'
  rw [hx2.trans hu0] at hc
  exact ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne (ne_of_lt hj).symm _, hc⟩

theorem fibTri_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (hMB : ModelBase M) (hR : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1))
    (hU : ExpUniq e F) (hL : ExpLin e F) (hTE : ExpTan e F) (hD : PerDom e F M) (hFb : PerFib e F M) :
    FibTri e F M := by
  intro k k' x x' Pm Pm' v v' hPm hPm' hu hv hv' htri
  have eP : Pm = pmOf e M k x.1 := AddMonoidHom.ext fun a => funext fun j => hPm a j
  have eP' : Pm' = pmOf e M k' x'.1 := AddMonoidHom.ext fun a => funext fun j => hPm' a j
  subst eP eP'
  have hP := hD hMB hR k x.1 x.2
  have hP' := hD hMB hR k' x'.1 x'.2
  obtain rfl := F.disj k k' _ _ hP hP' hu
  obtain ⟨gam, h, hiso, hlM, hlA, hrel⟩ := (F.fibre k _ _ hP hP').1 hu
  have hex := hU k _ _ hP hP' gam h hiso hlM hlA hrel
  have htr : ∀ τ j, IsDerivAt0 (fun z => (F.ex k (pmOf e M k x'.1) z).left) (h (eb e τ j)) (v τ j) :=
    fun τ j => isDerivAt0_comp (e1 := fun z => (F.ex k (pmOf e M k x.1) z).left)
      (e2 := fun z => (F.ex k (pmOf e M k x'.1) z).left) h hex (hv τ j)
  have htri' : ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      eb e τ i = h (∑ j, cf j • eb e τ j) := by
    intro τ i
    have hexi : ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt (F.u k (pmOf e M k x.1)) (v τ) cf (v' τ i) := htri τ i
    obtain ⟨cf, hcu, hct, hcc⟩ := hexi
    obtain ⟨w0, hw0⟩ := derivAt_exists hP' (∑ j, cf j • h (eb e τ j))
    have h1 := hL k _ hP' _ (fun j => h (eb e τ j)) (v τ) cf w0 (htr τ) hw0
    rw [← hu] at h1
    have h2 : w0 = v' τ i := isCombAt_unique h1 hcc
    rw [h2] at hw0
    have h3 := derivAt_unique hTE hP' (hv' τ i) hw0
    refine ⟨cf, hcu, hct, ?_⟩
    rw [map_sum]
    simp only [map_smul]
    exact h3
  obtain ⟨γ, hγ, b, hb, hx⟩ := hFb hMB hR k x.1 x'.1 x.2 x'.2 gam h hiso hlM hlA hrel htri'
  exact ⟨γ, hγ, b, hb, by rw [hx]⟩

end Main

section Rows

variable {D : D7}

theorem cover_uniformisation_level_two {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : TanLin (Q.Xo j)) (hU : ExpUniq (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR))
    (hL : ExpLin (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR)) (hTE : ExpTan (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR))
    (hOX : PerOntoX (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) : CoverU (unfJ hF) :=
  coverU_J hF (coverTri_of _ _ _ hM.choose_spec.1 hR hT hU hL hTE hOX)

theorem fibre_uniformisation_level_two {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : TanLin (Q.Xo j)) (hU : ExpUniq (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR))
    (hL : ExpLin (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR)) (hTE : ExpTan (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR))
    (hD : PerDom (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM))
    (hFb : PerFib (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) : FibreU (unfJ hF) :=
  fibreU_J hF hT (fibTri_of _ _ _ hM.choose_spec.1 hR hU hL hTE hD hFb)

end Rows

end Formalism.L2.Pj
