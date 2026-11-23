import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FrameCo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm

namespace GlobalTheory.BcLie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : Var F}
  {ρ : Y.X ⟶ gen Z}

variable (e ρ) in

abbrev GenFrame : Type := EigFrame Z (constF e Y) (genericPt Y ≫ ρ ≫ genι Z)

variable (ρ) in

abbrev StalkFrame (y : Y.X) (φ : c.F →+* Y.X.presheaf.stalk y) : Type := EigFrame Z φ (stalkPt Y y ≫ ρ ≫ genι Z)

abbrev toFn (y : Y.X) : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField

variable (g₀ : GenFrame e ρ) (τ : E →+* ℂ)

def Fits (y : Y.X) (φ : c.F →+* Y.X.presheaf.stalk y) (f : StalkFrame ρ y φ)
    (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) : Prop :=
  constF e Y = (toFn y).comp φ ∧ ∀ i, IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (g₀.v τ) (fun a => P a i)
    (spMap (dualMap (toFn y)) ≫ f.v τ i)

variable {X : Scheme.{0}} (j : Y.X ⟶ X)

def FrOn (U : X.Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) : Prop :=
  ∀ y : Y.X, j y ∈ U → ∃ φ f, Fits g₀ τ y φ f P

def valP {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) (y : AlgPt Y) [Fact (resP v).Prime] :
    Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom

def LatOn (U : X.Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : Ext v) (y : AlgPt Y) (yt : Sp ε.O ⟶ X),
    spMap ε.O.subtype ≫ yt = y.1 ≫ j → ⊤ ≤ yt ⁻¹ᵁ U → ∀ φ f, Fits g₀ τ (below y.1) φ f P →
    ∀ (a : Fin (Dw.mult τ) → ℂ_[resP v]) (w : Sp (DualNumber ℂ_[resP v]) ⟶ Z.t.G.left),
      IsCombAtG Z.t (spMap (valP ε y) ≫ stalkPt Y (below y.1) ≫ ρ ≫ genι Z)
        (fun i => spMap (dualMap (valP ε y)) ≫ f.v τ i) a w →
      (w ∈ latDR Z.t (spMap (valP ε y) ≫ stalkPt Y (below y.1) ≫ ρ ≫ genι Z) ↔ ∀ i, ‖a i‖ ≤ 1)

variable {M : X.Modules} (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn)

def IsLie : Prop := IsCo (genericPt Y ≫ j) A ∧ ∀ ch : Chart M (Dw.mult τ), FrOn g₀ τ j ch.U (lieMat dual (A ch))

def IsLat : Prop := ∀ ch : Chart M (Dw.mult τ), LatOn g₀ τ j ch.U (lieMat dual (A ch))

variable {q : X ⟶ Sp (𝓞 F)} (G : ∀ σ : c.F →+* ℂ, EigMet Z σ) (h : VMetric q M (Dw.mult τ))

def MetOn (ch : Chart M (Dw.mult τ)) : Prop :=
  ∀ (σ : F →+* ℂ) (p : Pts Y σ) (z : CxPts q (σ.comp (algebraMap (𝓞 F) F))), z.1 = p.1 ≫ j →
    z ∈ CxPts.ptsIn q _ ch.U → ∀ φ f, Fits g₀ τ (Var.base p) φ f (lieMat dual (A ch)) →
    ∀ (yc : CxPts (genStr Z) (embOf e σ)), yc.1 = p.1 ≫ ρ → ∀ g : EigFrame Z (embOf e σ) (yc.1 ≫ genι Z),
      f.IsMap (Var.evStalk p) g →
      (h.met _).G ch z = cond dual ((G _).gram yc g τ)⁻¹ ((G _).gram yc g τ)ᵀ

def IsMet : Prop := ∀ ch, MetOn g₀ τ j dual A G h ch

def IsFlag {K : Type} [CommRing K] {r : ℕ} (ξ : Sp K ⟶ X) (dual : Bool) (A : Chart M r → Matrix (Fin r) (Fin r) K)
    (fl : Vert.Flag M r) : Prop :=
  ∀ ch : Chart M r, IsAdapted fl ch → ⊤ ≤ ξ ⁻¹ᵁ ch.U → IsTri ((A ch).submatrix (pos dual) id)

def IsGrSec {r : ℕ} (dual : Bool) (A : Chart M r → Matrix (Fin r) (Fin r) Y.Fn) (fl : Vert.Flag M r) (i : Fin r)
    (s : ((fl.root i).pull j).ι → Y.Fnˣ) : Prop :=
  Cartier.IsRatSec ((fl.root i).pull j) s ∧ ∀ (ch : Chart M r), IsAdapted fl ch → ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ ch.U →
    ∀ (t : Γ(fl.F i.succ, ch.U)), (fl.ι i.succ).app ch.U t = ch.e i →
    ∀ ht : IsFrame fun _ : Fin 1 => (fl.π i).app ch.U t,
      (s (fun _ => (⟨ch.U, _, ht⟩ : Chart (fl.gr i) 1)) : Y.Fn) * A ch (pos dual i) i = 1

def SplitOn (ρ' : X ⟶ Z.X) (V : X.Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) : Prop :=
  ∃ (hV : IsAffineOpen V) (hξ : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ V) (g : ℕ)
    (b : Fin g → (Sp (DualNumber Γ(X, V)) ⟶ Z.t.G.left)) (S : Matrix (Fin g) (Fin (Dw.mult τ)) Γ(X, V))
    (S' : Matrix (Fin (Dw.mult τ)) (Fin g) Γ(X, V)),
    IsTanBasis Z.t (R := Γ(X, V)) (hV.fromSpec ≫ ρ') b ∧ S' * S = 1 ∧ IsUnit P.det ∧
    ∀ i, ∃ w, IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (g₀.v τ) (fun a => P a i) w ∧
      IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (fun k => spMap (dualMap (evalPt _ V hξ)) ≫ b k)
        (fun k => evalPt _ V hξ (S k i)) w

def ValAt {K : Type} [Field K] (x : Sp K ⟶ Y.X) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn)
    {χ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (g : EigFrame Z χ x₀) : Prop :=
  x₀ = x ≫ ρ ≫ genι Z ∧ ∃ φ f, Fits g₀ τ (below x) φ f P ∧ χ = (Scheme.stalkClosedPointTo x).hom.comp φ ∧
    f.IsMap (Scheme.stalkClosedPointTo x).hom g

variable {g₀ τ}

omit [NumberField F] in
theorem spMap_toFn (y : Y.X) : spMap (toFn y) ≫ stalkPt Y y = genericPt Y :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

omit [NumberField F] in
theorem toFn_injective (y : Y.X) : Function.Injective (toFn y) :=
  IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField

omit [NumberField F] in

theorem fits_iff {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} {f : StalkFrame ρ y φ} {f' : GenFrame e ρ}
    (hφ : constF e Y = (toFn y).comp φ) (hf : f.IsMap (toFn y) f')
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} : Fits g₀ τ y φ f P ↔ g₀.co f' τ = P :=
  ⟨fun h => EigFrame.co_eq fun i => by rw [hf τ i]; exact h.2 i, fun h => ⟨hφ, fun i => by
    rw [← hf τ i, ← h]; exact g₀.co_spec f' τ i⟩⟩

omit [NumberField F] in
theorem exists_isMap_toFn {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} (f : StalkFrame ρ y φ)
    (hφ : constF e Y = (toFn y).comp φ) : ∃ f' : GenFrame e ρ, f.IsMap (toFn y) f' :=
  f.exists_isMap _ hφ (by rw [← spMap_toFn y, Category.assoc])

omit [NumberField F] in
theorem Fits.isUnit_det {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} {f : StalkFrame ρ y φ}
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} (h : Fits g₀ τ y φ f P) : IsUnit P.det := by
  obtain ⟨f', hf⟩ := exists_isMap_toFn (e := e) f h.1
  rw [← (fits_iff h.1 hf).1 h]
  exact g₀.isUnit_det_co f' τ

omit [NumberField F] in
theorem Fits.φ_eq {y : Y.X} {φ φ' : c.F →+* Y.X.presheaf.stalk y} {f : StalkFrame ρ y φ} {f' : StalkFrame ρ y φ'}
    {τ' : E →+* ℂ} {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn}
    {P' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) Y.Fn} (h : Fits g₀ τ y φ f P) (h' : Fits g₀ τ' y φ' f' P') :
    φ = φ' :=
  RingHom.ext fun a => toFn_injective y ((RingHom.congr_fun h.1 a).symm.trans (RingHom.congr_fun h'.1 a))

omit [NumberField F] in

theorem Fits.eq_mul {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} {f f' : StalkFrame ρ y φ}
    {P P' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} (h : Fits g₀ τ y φ f P) (h' : Fits g₀ τ y φ f' P') :
    P' = P * (f.co f' τ).map (toFn y) := by
  obtain ⟨k, hk⟩ := exists_isMap_toFn (e := e) f h.1
  obtain ⟨k', hk'⟩ := exists_isMap_toFn (e := e) f' h.1
  rw [← (fits_iff h.1 hk).1 h, ← (fits_iff h.1 hk').1 h', ← hk.co τ hk' (by rw [← spMap_toFn y, Category.assoc]),
    EigFrame.co_mul]

omit [NumberField F] in

theorem Fits.co_eq {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} {f f' : StalkFrame ρ y φ}
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} {T : Matrix _ _ (Y.X.presheaf.stalk y)}
    (h : Fits g₀ τ y φ f P) (h' : Fits g₀ τ y φ f' (P * T.map (toFn y))) : f.co f' τ = T := by
  have := h.eq_mul h'
  rw [((isUnit_iff_isUnit_det _).2 h.isUnit_det).mul_right_inj] at this
  exact (Matrix.map_injective (toFn_injective y) this).symm

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in

theorem exists_co_eq {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : (E →+* ℂ) → EigFrame Z φ x)
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (hT : ∀ τ, IsUnit (T τ).det) :
    ∃ g : EigFrame Z φ x, ∀ τ, (f τ).co g τ = T τ := by
  have key (τ) (a : Fin (Dw.mult τ) → R) :
      ∑ i, a i • ∑ k, T τ k i • (f τ).vec τ k = ∑ k, (T τ *ᵥ a) k • (f τ).vec τ k := by
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul, mul_comm]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, T τ k i • (f τ).vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ => EigFrame.co_eq fun i => (GlobalTheory.LieMet.isComb_iff ((f τ).vec τ) _ _).2 rfl⟩
  · simp only [map_sum, map_smul, EigFrame.act_vec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨b, hb, hu⟩ := (f τ).existsUnique_sum τ w hw
    refine ⟨(T τ)⁻¹ *ᵥ b, by
      beta_reduce
      rw [key, mulVec_mulVec, mul_nonsing_inv _ (hT τ), one_mulVec]; exact hb, fun a ha => ?_⟩
    rw [← hu _ (ha.trans (key τ a)), mulVec_mulVec, nonsing_inv_mul _ (hT τ), one_mulVec]

omit [NumberField F] in

theorem Fits.exists_mul {y : Y.X} {φ : c.F →+* Y.X.presheaf.stalk y} {f : StalkFrame ρ y φ}
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} (h : Fits g₀ τ y φ f P)
    {T : Matrix _ _ (Y.X.presheaf.stalk y)} (hT : IsUnit T.det) :
    ∃ f' : StalkFrame ρ y φ, f.co f' τ = T ∧ Fits g₀ τ y φ f' (P * T.map (toFn y)) := by
  classical
  obtain ⟨f', hf'⟩ := exists_co_eq (fun _ => f) (Function.update (fun _ => 1) τ T) fun τ' => by
    by_cases h : τ' = τ
    · subst h; rwa [Function.update_self]
    · rw [Function.update_of_ne h, det_one]; exact isUnit_one
  have e₁ : f.co f' τ = T := by rw [hf', Function.update_self]
  obtain ⟨k', hk'⟩ := exists_isMap_toFn (e := e) f' h.1
  have h' := (fits_iff (g₀ := g₀) (τ := τ) h.1 hk').2 rfl
  refine ⟨f', e₁, ?_⟩
  rwa [h.eq_mul h', e₁] at h'

omit [NumberField F] in

theorem exists_fits (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (y : Y.X) :
    ∃ φ f P, Fits g₀ τ y φ f P := by
  let φ : c.F →+* Y.X.presheaf.stalk y := (Spec.preimage ((stalkPt Y y ≫ ρ) ≫ genStr Z)).hom
  have hφ : (stalkPt Y y ≫ ρ) ≫ genStr Z = spMap φ := (Spec.map_preimage _).symm
  obtain ⟨f₁⟩ := EigLoc.exists_eigFrame E H Dw l Xo c O β Z _ φ _ hφ
  have f : EigFrame Z φ (stalkPt Y y ≫ ρ ≫ genι Z) := by rw [← Category.assoc]; exact f₁
  have h : constF e Y = (toFn y).comp φ := EigLoc.spMap_inj (by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    have h3 : spMap ((toFn y).comp φ) = spMap (toFn y) ≫ spMap φ := by rw [← Spec.map_comp]; rfl
    have h4 : spMap (constF e Y) = spMap (algebraMap F Y.Fn) ≫ spMap e.symm.toRingHom := by rw [← Spec.map_comp]; rfl
    rw [h3, h4, ← hφ, ← h1, ← hρ, ← spMap_toFn y]
    simp only [Category.assoc, h2, Category.comp_id])
  obtain ⟨f', hf'⟩ := exists_isMap_toFn (e := e) f h
  exact ⟨φ, f, _, (fits_iff h hf').2 rfl⟩

omit [NumberField F] in
theorem stalk_le {y : Y.X} {U : X.Opens} (h : j y ∈ U) : ⊤ ≤ (stalkPt Y y ≫ j) ⁻¹ᵁ U := fun p _ => by
  have h₁ : stalkPt Y y p ∈ Set.range (Y.X.fromSpecStalk y) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h₁
  exact (Specializes.map h₁ j.continuous).mem_open U.isOpen h

omit [NumberField F] in
theorem gen_le {y : Y.X} {U : X.Opens} (h : j y ∈ U) : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ U := by
  rw [← spMap_toFn y, Category.assoc]
  exact fun p _ => stalk_le j h (x := spMap (toFn y) p) trivial

omit [NumberField F] in
theorem trAt_gen {r : ℕ} {y : Y.X} (ch ch' : Chart M r) (h : j y ∈ ch.U) (h' : j y ∈ ch'.U) :
    trAt (genericPt Y ≫ j) ch ch' = (trAt (stalkPt Y y ≫ j) ch ch').map (toFn y) := by
  rw [← trAt_spMap _ ch ch' (stalk_le j h) (stalk_le j h'), ← Category.assoc, spMap_toFn]

variable {j dual A}

omit [NumberField F] in

theorem Fits.change (hA : IsCo (genericPt Y ≫ j) A) {y : Y.X} {ch ch' : Chart M (Dw.mult τ)} (h : j y ∈ ch.U)
    (h' : j y ∈ ch'.U) {φ : c.F →+* Y.X.presheaf.stalk y} {f : StalkFrame ρ y φ}
    (hf : Fits g₀ τ y φ f (lieMat dual (A ch))) : ∃ f' : StalkFrame ρ y φ,
      f.co f' τ = lieMat dual (trAt (stalkPt Y y ≫ j) ch ch') ∧ Fits g₀ τ y φ f' (lieMat dual (A ch')) := by
  have hu := isUnit_det_trAt ch ch' (stalk_le j h) (stalk_le j h')
  rw [hA.2 ch ch' (gen_le j h) (gen_le j h'), lieMat_mul, trAt_gen j ch ch' h h', lieMat_map _ _ hu]
  exact hf.exists_mul (isUnit_det_lieMat dual hu)

omit [NumberField F] in

theorem isLie_of_exists (hA : IsCo (genericPt Y ≫ j) A)
    (h : ∀ y : Y.X, ∃ ch : Chart M (Dw.mult τ), j y ∈ ch.U ∧ ∃ φ f, Fits g₀ τ y φ f (lieMat dual (A ch))) :
    IsLie g₀ τ j dual A := by
  refine ⟨hA, fun ch y hy => ?_⟩
  obtain ⟨ch₀, h₀, φ, f, hf⟩ := h y
  obtain ⟨f', -, hf'⟩ := hf.change hA h₀ hy
  exact ⟨φ, f', hf'⟩

variable (e) in

def IsOver {B : Var F} (ρB : B.X ⟶ gen Z) (ρ : Y.X ⟶ gen Z) (f : Y.X ⟶ B.X) (φ : B.Fn →+* Y.Fn) : Prop :=
  f ≫ ρB = ρ ∧ f ≫ B.str = Y.str ∧ genericPt Y ≫ f = spMap φ ≫ genericPt B ∧ constF e Y = φ.comp (constF e B)

section Pull

variable {B : Var F} {ρB : B.X ⟶ gen Z} {f : Y.X ⟶ B.X} {φ : B.Fn →+* Y.Fn}

omit [NumberField F] in
theorem spMap_stalkMap (f : Y.X ⟶ B.X) (y : Y.X) :
    spMap (f.stalkMap y).hom ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f

omit [NumberField F] in
theorem IsOver.toFn_comp (h : IsOver e ρB ρ f φ) (y : Y.X) :
    (toFn y).comp (f.stalkMap y).hom = φ.comp (toFn (f y)) :=
  EigLoc.spMap_inj ((cancel_mono (B.X.fromSpecStalk (f y))).1 (by
    have h₁ : spMap ((toFn y).comp (f.stalkMap y).hom) = spMap (toFn y) ≫ spMap (f.stalkMap y).hom := by
      rw [← Spec.map_comp]; rfl
    have h₂ : spMap (φ.comp (toFn (f y))) = spMap φ ≫ spMap (toFn (f y)) := by rw [← Spec.map_comp]; rfl
    change _ ≫ stalkPt B (f y) = _ ≫ stalkPt B (f y)
    rw [h₁, h₂, Category.assoc, Category.assoc, spMap_stalkMap, spMap_toFn, ← Category.assoc, spMap_toFn, h.2.2.1]))

omit [NumberField F] in
theorem IsOver.exists_isMap (h : IsOver e ρB ρ f φ) (g : GenFrame e ρB) : ∃ g' : GenFrame e ρ, g.IsMap φ g' :=
  g.exists_isMap φ h.2.2.2 (by rw [← h.1, Category.assoc, ← Category.assoc, h.2.2.1, Category.assoc])

omit [NumberField F] in

theorem Fits.pull (h : IsOver e ρB ρ f φ) {g : GenFrame e ρB} {g' : GenFrame e ρ} (hg : g.IsMap φ g') (g₁ : GenFrame e ρ)
    {y : Y.X} {φ₀ : c.F →+* B.X.presheaf.stalk (f y)} {k : StalkFrame ρB (f y) φ₀}
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B.Fn} (hk : Fits g τ (f y) φ₀ k P) :
    ∃ k₁ : StalkFrame ρ y ((f.stalkMap y).hom.comp φ₀), k.IsMap (f.stalkMap y).hom k₁ ∧
      Fits g₁ τ y _ k₁ (g₁.co g' τ * P.map φ) := by
  obtain ⟨k₁, hk₁⟩ := k.exists_isMap (f.stalkMap y).hom (x' := stalkPt Y y ≫ ρ ≫ genι Z) rfl
    (by rw [← Category.assoc (spMap _), spMap_stalkMap, ← h.1]; simp only [Category.assoc])
  have hφ : constF e Y = (toFn y).comp ((f.stalkMap y).hom.comp φ₀) := by
    rw [← RingHom.comp_assoc, h.toFn_comp, RingHom.comp_assoc, ← hk.1, h.2.2.2]
  obtain ⟨k', hk'⟩ := exists_isMap_toFn (e := e) k hk.1
  obtain ⟨k₁', hk₁'⟩ := exists_isMap_toFn (e := e) k₁ hφ
  have hm : k'.IsMap φ k₁' := fun τ i => by
    rw [hk₁', hk₁, hk', GlobalTheory.GradedPieces.dual_comp, GlobalTheory.GradedPieces.dual_comp, h.toFn_comp]
  refine ⟨k₁, hk₁, (fits_iff hφ hk₁').2 ?_⟩
  rw [← g₁.co_mul g', hg.co τ hm (by rw [← h.1, Category.assoc, ← Category.assoc, h.2.2.1, Category.assoc]),
    (fits_iff hk.1 hk').1 hk]

def IsPullCo {XB : Scheme.{0}} (jB : B.X ⟶ XB) (π : X ⟶ XB) {N : XB.Modules} (hN : IsVB N (Dw.mult τ)) (dual : Bool)
    (φ : B.Fn →+* Y.Fn) (g' g₁ : GenFrame e ρ)
    (A : Chart N (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B.Fn)
    (A' : Chart ((Scheme.Modules.pullback π).obj N) (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) : Prop :=
  ∀ ch : Chart N (Dw.mult τ), ⊤ ≤ (genericPt B ≫ jB) ⁻¹ᵁ ch.U →
    A' (ch.pull hN π) = lieMat dual (g₁.co g' τ) * (A ch).map φ

omit [NumberField F] in

theorem IsLie.exists_pull (h : IsOver e ρB ρ f φ) {g : GenFrame e ρB} {g' : GenFrame e ρ} (hg : g.IsMap φ g')
    (g₁ : GenFrame e ρ) {XB : Scheme.{0}} {jB : B.X ⟶ XB} (π : X ⟶ XB) (j : Y.X ⟶ X) (hj : j ≫ π = f ≫ jB) {N : XB.Modules}
    (hN : IsVB N (Dw.mult τ)) {A : Chart N (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B.Fn}
    (hA : IsLie g τ jB dual A) : ∃ A', IsLie g₁ τ j dual A' ∧ IsPullCo jB π hN dual φ g' g₁ A A' := by
  obtain ⟨A', h₁, h₂⟩ := hA.1.exists_pull hN π (genericPt Y ≫ j) φ
    (by rw [Category.assoc, hj, ← Category.assoc, h.2.2.1, Category.assoc]) _
    (isUnit_det_lieMat dual (g₁.isUnit_det_co g' τ))
  refine ⟨A', isLie_of_exists h₁ fun y => ?_, h₂⟩
  obtain ⟨U, s, hU, hs⟩ := hN (jB (f y))
  let ch : Chart N (Dw.mult τ) := ⟨U, s, hs⟩
  obtain ⟨φ₀, k, hk⟩ := hA.2 ch (f y) hU
  obtain ⟨k₁, -, hk₁⟩ := hk.pull h hg g₁
  refine ⟨ch.pull hN π, ?_, _, k₁, ?_⟩
  · change π (j y) ∈ U
    rwa [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
  · rwa [h₂ ch (gen_le jB hU), lieMat_mul, lieMat_lieMat _ (g₁.isUnit_det_co g' τ),
      lieMat_map _ _ (hA.1.1 ch (gen_le jB hU))]

end Pull

end GlobalTheory.BcLie

end
