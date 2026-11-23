import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem ker_le_span_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : X →ₛₗ[σ] H)
    (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W) (Rel : X → Y → Prop) (hex : ∀ x, ∃ y, Rel x y)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → jW y = T (j x)) :
    LinearMap.ker T ≤ Submodule.span ℂ (j '' {u | Rel u 0}) := by
  have hinj : Function.Injective jW := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h0
    exact (hind 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx
  choose f hf using hex
  have e : ∀ x, jW (f x) = T (j x) := fun x => hT x _ (hf x)
  let θ : X →ₗ[K] Y :=
    { toFun := f
      map_add' := fun x y => hinj (by rw [map_add, e, e, e, map_add, map_add])
      map_smul' := fun a x => hinj (by rw [RingHom.id_apply, map_smulₛₗ, e, e, map_smulₛₗ, map_smul]) }
  refine (GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW T hsp hind fun x => (e x).symm).trans
    (Submodule.span_mono (Set.image_mono fun u hu => ?_))
  have h0 : f u = 0 := hu
  exact h0 ▸ hf u

theorem mem_orthogonal_of_le_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : Submodule ℂ H} {s : Set H}
    (h : N ≤ Submodule.span ℂ s) {v : H} (hv : ∀ u ∈ s, ⟪v, u⟫_ℂ = 0) : v ∈ Nᗮ := by
  refine Submodule.orthogonal_le h ((Submodule.mem_orthogonal' _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem u hu => exact hv u hu
  | zero => exact inner_zero_right _
  | add u u' _ _ h h' => rw [inner_add_right, h, h', add_zero]
  | smul a u _ h => rw [inner_smul_right, h, mul_zero]

theorem toF_mem {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  obtain ⟨f, hf, e⟩ : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : B.toF ℓ Z y = f := (congrArg B.S.basis.equivFun.symm e.symm).trans (B.S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem inner_eq_zero_of_mem_range_adjoint {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {a b : H}
    (ha : a ∈ LinearMap.range (LinearMap.adjoint T)) (hb : T b = 0) : ⟪a, b⟫_ℂ = 0 := by
  obtain ⟨w, rfl⟩ := ha
  rw [LinearMap.adjoint_inner_left, hb, inner_zero_right]

theorem mem_orthogonal_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ)
    (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W) (U : W ≃ₗᵢ[ℂ] W) (κ : ℂ) (g : W →ₗ[ℂ] W) (Rel : X → Y → Prop)
    (hex : ∀ x, ∃! y, Rel x y) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → U (jW y) = κ • g (th (j x))) {v : H} (hv : ∀ u, Rel u 0 → ⟪v, j u⟫_ℂ = 0) :
    v ∈ (LinearMap.ker th)ᗮ := by
  have hk := ker_le_span_of_rel σ j jW ((U.symm.toLinearEquiv.toLinearMap ∘ₗ (κ • g)) ∘ₗ th) Rel (fun x => (hex x).exists) hsp
    hind (fun x y h => U.toLinearEquiv.eq_symm_apply.2 (hT x y h))
  refine mem_orthogonal_of_le_span ((LinearMap.ker_le_ker_comp _ _).trans hk) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hv u hu

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem csum_eq_zero_of_adjoint (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : R.jV i t f ∈ LinearMap.range (LinearMap.adjoint (R.thG i t))) (hg : R.thG i t (R.jV i t g) = 0) :
    (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  have h3 : inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
    refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
    refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
      (h2 i t f) (h2 i t g)).trans ?_
    exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g
  exact (map_eq_zero _).1 (h3.symm.trans (inner_eq_zero_of_mem_range_adjoint _ hf hg))

end

set_option maxHeartbeats 1600000 in

theorem conjForms_mem_orthogonal_ker : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.LUnif → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ph : ℂ, ph ≠ 0 → (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ x, j ((A.fam.L i A.μ0).toF ℓ Z x) ∈ (LinearMap.ker th)ᗮ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hU gramR c0R c0L hT i σ c c₁ H j μ' η' th ph hph hex hC hD ℓ Z hH hE hZ x
  obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hC
  obtain ⟨-, κ, -, hκ⟩ := hall μ' η' c c₁ H j th hD
  have hsp := GlobalTheory.ConjSpan.span_conjForms R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.fam.L i A.μ0).S.basis
  refine mem_orthogonal_of_rel σ j ((R.FW i).j σ) th U κ (R.gW i σ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph) hex hsp (hU i σ).1
    hκ fun v hv => ?_
  have h0 : R.thG i A.μ0 (R.jV i A.μ0 v) = 0 :=
    (smul_eq_zero.1 ((map_zero _).symm.trans hv).symm).resolve_left hph
  refine (GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1 _ v).trans ?_
  exact (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt (A.fam.L i A.μ0) ℓ Z hH hE).2 v
    (fun y => csum_eq_zero_of_adjoint hM.HV hM.jV i A.μ0 (hZ _ (toF_mem _ ℓ Z y)) h0) σ x

end GlobalTheory.ConjScalar
