import Development.EtaleCohomology.EtaleSheaves.ChartSurjCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.StandardEtaleChartsMultivariableHensel

attribute [local instance] MvPolynomial.gradedAlgebra in

def stdOpen (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

def StdPair {A : Type} [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) : Prop :=
  ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1), IsIntegralHom u ∧ IsProper l ∧
    IsPullback f l (terminal.from P1) (terminal.from _) ∧ u ≫ l = p ∧
    Set.range ι₁ = ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) ∧ Set.range ι₂ = ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ ∧ StdPair p ι₁ ι₂

def MvHensel : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (n : ℕ)
  (F : Fin n → MvPolynomial (Fin n) A) (x₀ : Fin n → A),
  (∀ i, MvPolynomial.eval x₀ (F i) ∈ IsLocalRing.maximalIdeal A) →
  IsUnit (MvPolynomial.eval x₀ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (F i)))) →
  ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j - x₀ j ∈ IsLocalRing.maximalIdeal A

def Heart : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  StdPair p ι₁ ι₂ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem chartSurj (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) :
    ∀ (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
    ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
    IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
    StdPair p ι₁ ι₂ →
    ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
      w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
        pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b := by
  unfold LateralTheory.E.ChartSurjCut.Root at hR
  unfold LateralTheory.E.ChartSurjCut.LCIso at hL
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

theorem goal_of (hMV : MV) (hC : StdCharts) (hF : LateralTheory.E.LineOneCut.FibCover) (hA : ChartAcyc)
    (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov, hstd⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := chartSurj hR hL hT H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.StandardEtaleChartsMultivariableHensel
