import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem htot_subsingleton (l : ℕ) [Fact l.Prime] (E : Spc)
    (h : ∀ n : ℤ, Subsingleton (Hl l E n 0)) : Subsingleton (Htot l E) := by
  have hq : ∀ n : ℤ, Subsingleton (HQ l E n 0) := fun n => by
    have := h n
    refine ⟨fun a b => ?_⟩
    have z : ∀ c : HQ l E n 0, c = 0 := fun c => by
      induction c using TensorProduct.induction_on with
      | zero => rfl
      | tmul q y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add c d hc hd => rw [hc, hd, add_zero]
    rw [z a, z b]
  exact ⟨fun a b => DFinsupp.ext fun n => (hq n).elim _ _⟩

private theorem op_eq (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (p : Z ⟶ sp k)
    (s : Y ⟶ Z) (t : Y ⟶ Z') (hT : (et l (sp k)).Good)
    (tr : (et l (sp k)).H (s ≫ p) →ₗ[ℚ_[l]] (et l (sp k)).H p) (htr : (et l (sp k)).IsTr p (s ≫ p) s tr)
    (A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (hA : IsCorrOp l s t A)
    (x : Htot l (sch.obj Z')) : A x = tr (pullTot l (sch.map t) x) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, hx⟩ := hA
  have hσ : ∀ j, σ j ≫ s ≫ p = c ≫ p := fun j => by
    rw [← Category.assoc, hsp.choose j]
  have hinj := hT.inj p (c ≫ p) c rfl G a hgal
  apply hinj
  have e := htr W (c ≫ p) c rfl J σ hσ hsp (pullTot l (sch.map t) x)
  refine Eq.trans ?_ e.symm
  refine (hx x).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Functor.map_comp, pullTot_comp]
  rfl

theorem UpperTheory.Gal.G3.jCorrUniq :
    EtGood → SplitDesc → CharVan → CorrUniq := by
  intro hG hD hV l _ k _ Z Y Z' p s t A A' hA hA'
  by_cases hl : (l : k) = 0
  · have := htot_subsingleton l (sch.obj Z) fun n => hV l k hl p n 0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · have hu : IsUnit (l : Γ(sp k, ⊤)) := by
      have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (l : k)) := (IsUnit.mk0 _ hl).map _
      rwa [map_natCast] at h
    have hT := hG l (sp k) hu
    obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, -⟩ := id hA
    obtain ⟨hf, he, hs, -, -, -⟩ := hgal
    obtain ⟨_, _⟩ := @hD Z Y W s c hf he hs J _ σ hsp
    obtain ⟨tr, htr⟩ := hT.tr p (s ≫ p) s rfl
    exact LinearMap.ext fun x => (op_eq l k p s t hT tr htr A hA x).trans (op_eq l k p s t hT tr htr A' hA' x).symm
