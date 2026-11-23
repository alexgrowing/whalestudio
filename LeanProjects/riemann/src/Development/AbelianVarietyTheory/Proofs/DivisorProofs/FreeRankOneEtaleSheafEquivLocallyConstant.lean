import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamilyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (j : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ j) x = Sec.res k (Sec.res j x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_smul {V U : Scheme.{0}} (j : V ⟶ U) (c : R) (x : Sec F U) :
    Sec.res j ((ULift.up c : ULift.{1} R) • x) = (ULift.up c : ULift.{1} R) • Sec.res j x :=
  map_smul _ _ _

theorem res_add {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x + y) = Sec.res j x + Sec.res j y := map_add _ _ _

theorem res_sub {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x - y) = Sec.res j x - Sec.res j y := map_sub _ _ _

theorem sep {U : Scheme.{0}} (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U) (he : ∀ i, Etale (j i))
    (hc : ∀ u : U, ∃ i v, j i v = u) (x y : Sec F U) (h : ∀ i, Sec.res (j i) x = Sec.res (j i) y) : x = y :=
  sub_eq_zero.1 ((GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U ι V j he hc).1 (x - y) (fun i => by rw [res_sub, h i, sub_self]))

theorem sec_empty {V : Scheme.{0}} [IsEmpty V] (x y : Sec F V) : x = y :=
  sep PEmpty (fun _ => V) (fun _ => 𝟙 V) (fun _ => inferInstance) (fun u => isEmptyElim u) x y (fun i => i.elim)

def fib {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) : V.Opens :=
  ⟨ψ ⁻¹' {ψ v}, ψ.isLocallyConstant.isOpen_fiber _⟩

theorem fib_apply {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) (w : (fib ψ v).toScheme) :
    ψ ((fib ψ v).ι w) = ψ v := by
  have h := (Scheme.Opens.range_ι (fib ψ v)).subset ⟨w, rfl⟩
  exact h

theorem fib_cov {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (u : V) :
    ∃ (i : V) (w : (fib ψ i).toScheme), (fib ψ i).ι w = u := by
  have h : u ∈ Set.range (fib ψ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, hw⟩ := h
  exact ⟨u, w, hw⟩

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

def IsMul {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (j : V ⟶ U) (c : R), (∀ v, φ (j v) = c) →
    Sec.res j x = (ULift.up c : ULift.{1} R) • Sec.res (j ≫ s) g

theorem isMul_of_fib {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U)
    (h : ∀ u, Sec.res (fib φ u).ι x = (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) : IsMul s g φ x := by
  intro V j c hc
  by_cases hV : IsEmpty V
  · exact sec_empty _ _
  obtain ⟨v⟩ := not_isEmpty_iff.1 hV
  have H : Set.range j ⊆ Set.range (fib φ (j v)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change φ (j w) = φ (j v)
    rw [hc w, hc v]
  have hf := IsOpenImmersion.lift_fac (fib φ (j v)).ι j H
  rw [← hf, res_comp, h, res_smul, ← res_comp, hc v, Category.assoc]

theorem isMul_unique {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g φ y) : x = y :=
  sep U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance) (fib_cov φ) x y
    (fun u => by rw [hx _ _ (φ u) (fib_apply φ u), hy _ _ (φ u) (fib_apply φ u)])

theorem isMul_exists {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    ∃ x, IsMul s g φ x := by
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance)
    (fib_cov φ)).2 (fun u => (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) (by
      intro i k
      rw [res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, pullback.condition]
      by_cases hP : IsEmpty (pullback (fib φ i).ι (fib φ k).ι : Scheme.{0})
      · exact sec_empty _ _
      obtain ⟨p⟩ := not_isEmpty_iff.1 hP
      have e : φ i = φ k := by
        rw [← fib_apply φ i (pullback.fst (fib φ i).ι (fib φ k).ι p), ← fib_apply φ k (pullback.snd (fib φ i).ι (fib φ k).ι p),
          ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [e])
  exact ⟨x, isMul_of_fib s g φ x hx⟩

theorem isMul_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g ψ y) : IsMul s g (φ + ψ) (x + y) := by
  intro V j c hc
  let χ : LocallyConstant V (R × R) :=
    ⟨fun v => (φ (j v), ψ (j v)), ((φ.comap j.base.hom).isLocallyConstant.comp₂ (ψ.comap j.base.hom).isLocallyConstant Prod.mk)⟩
  refine sep V (fun v => (fib χ v).toScheme) (fun v => (fib χ v).ι) (fun _ => inferInstance) (fib_cov χ) _ _ (fun v => ?_)
  have h1 : ∀ w, φ (((fib χ v).ι ≫ j) w) = φ (j v) := fun w => congrArg Prod.fst (fib_apply χ v w)
  have h2 : ∀ w, ψ (((fib χ v).ι ≫ j) w) = ψ (j v) := fun w => congrArg Prod.snd (fib_apply χ v w)
  rw [← res_comp, res_add, hx _ _ _ h1, hy _ _ _ h2, res_smul, ← res_comp, ← add_smul, ← hc v]
  rfl

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

noncomputable def mulSec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) : Sec F U :=
  (isMul_exists s g φ).choose

theorem mulSec_spec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    IsMul s g φ (mulSec s g φ) := (isMul_exists s g φ).choose_spec

theorem mulSec_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) :
    mulSec s g (φ + ψ) = mulSec s g φ + mulSec s g ψ :=
  isMul_unique s g _ _ _ (mulSec_spec s g _) (isMul_add s g φ ψ _ _ (mulSec_spec s g φ) (mulSec_spec s g ψ))

theorem coeff_eq {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U)
    {V₁ V₂ : Scheme.{0}} (j₁ : V₁ ⟶ U) (j₂ : V₂ ⟶ U) (c₁ c₂ : R)
    (h₁ : Sec.res j₁ x = (ULift.up c₁ : ULift.{1} R) • Sec.res (j₁ ≫ s) g)
    (h₂ : Sec.res j₂ x = (ULift.up c₂ : ULift.{1} R) • Sec.res (j₂ ≫ s) g) (v₁ : V₁) (v₂ : V₂) (hv : j₁ v₁ = j₂ v₂) :
    c₁ = c₂ := by
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v₁ v₂ hv
  have e : Sec.res (pullback.fst j₁ j₂) (Sec.res j₁ x) = Sec.res (pullback.snd j₁ j₂) (Sec.res j₂ x) := by
    rw [← res_comp, ← res_comp, pullback.condition]
  rw [h₁, h₂, res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, ← pullback.condition] at e
  have h0 : (ULift.up (c₁ - c₂) : ULift.{1} R) • Sec.res ((pullback.fst j₁ j₂ ≫ j₁) ≫ s) g = 0 := by
    have hu : (ULift.up (c₁ - c₂) : ULift.{1} R) = ULift.up c₁ - ULift.up c₂ := rfl
    rw [hu, sub_smul, e, sub_self]
  exact sub_eq_zero.1 ((hg _ _).2 (c₁ - c₂) ⟨p⟩ h0)

theorem mulSec_inj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (φ : LocallyConstant U R)
    (h : mulSec s g φ = 0) : φ = 0 := by
  ext u
  have e := mulSec_spec s g φ _ (fib φ u).ι (φ u) (fib_apply φ u)
  rw [h] at e
  have hu : u ∈ Set.range (fib φ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, -⟩ := hu
  exact (hg (fib φ u).toScheme ((fib φ u).ι ≫ s)).2 (φ u) ⟨w⟩ (by rw [← e]; exact map_zero _)

theorem mulSec_surj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U) :
    ∃ φ, mulSec s g φ = x := by
  choose V j v c he hv hx₀ using (hg U s).1 x
  have hx : ∀ u, Sec.res (j u) x = (ULift.up (c u) : ULift.{1} R) • Sec.res (j u ≫ s) g := hx₀
  have hconst : ∀ u, ∀ u' ∈ Set.range (j u), c u' = c u := by
    rintro u _ ⟨w, rfl⟩
    exact coeff_eq s g hg x (j (j u w)) (j u) _ _ (hx _) (hx u) _ w (hv _)
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (j u), (j u).isOpenMap.isOpen_range, ⟨v u, hv u⟩, hconst u⟩
  refine ⟨⟨c, hlc⟩, isMul_unique s g _ _ _ (mulSec_spec s g _) ?_⟩
  intro W k a ha
  refine sep W (fun w => (pullback (j (k w)) k : Scheme.{0})) (fun w => pullback.snd (j (k w)) k)
    (fun _ => inferInstance) (fun w => ?_) _ _ (fun w => ?_)
  · obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (v (k w)) w (hv (k w))
    exact ⟨w, p, hp⟩
  · have hc : c (k w) = a := ha w
    rw [← res_comp, ← pullback.condition, res_comp, hx, res_smul, ← res_comp, res_smul, ← res_comp, hc,
      ← Category.assoc, ← Category.assoc, pullback.condition]

end GlobalTheory.EtC.GenLC

open GlobalTheory.EtC.GenLC in

theorem GlobalTheory.EtC.gen_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  intro R _ F S g hg
  let m : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R →+ Sec F U := fun U s =>
    AddMonoidHom.mk' (mulSec s g) (mulSec_add s g)
  refine ⟨fun U s => AddEquiv.ofBijective (m U s)
    ⟨(injective_iff_map_eq_zero (m U s)).2 (fun φ h => mulSec_inj s g hg φ h), mulSec_surj s g hg⟩, ?_, ?_⟩
  · intro U s c
    show mulSec s g (LocallyConstant.const U c) = _
    refine isMul_unique s g _ _ _ (mulSec_spec s g _) ?_
    intro V j a ha
    rw [res_smul, ← res_comp]
    by_cases hV : IsEmpty V
    · exact sec_empty _ _
    obtain ⟨v⟩ := not_isEmpty_iff.1 hV
    have hca : c = a := ha v
    rw [hca]
  · intro V U j s φ
    show Sec.res j (mulSec s g φ) = mulSec (j ≫ s) g (φ.comap j.base.hom)
    refine isMul_unique (j ≫ s) g _ _ _ ?_ (mulSec_spec (j ≫ s) g _)
    intro W k a ha
    rw [← res_comp, mulSec_spec s g φ W (k ≫ j) a ha, Category.assoc]
