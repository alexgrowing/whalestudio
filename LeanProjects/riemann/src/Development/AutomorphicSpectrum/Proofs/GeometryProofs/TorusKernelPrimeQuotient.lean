import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompactCentralizerTranslate
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSurjectiveZmodOfNeZero

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsField

theorem exists_ideal_eq_iff {S : Scheme.{0}} {Y : Over S} [IsSeparated Y.hom] {R : Type} [CommRing R]
    {c : Sp R ⟶ S} (f g : Over.mk c ⟶ Y) :
    ∃ J : Ideal R, ∀ (A : Type) [CommRing A] (ρ : R →+* A),
      spMap ρ ≫ f.left = spMap ρ ≫ g.left ↔ J ≤ RingHom.ker ρ := by
  haveI hcl : IsClosedImmersion (equalizer.ι f g).left := isClosedImmersion_equalizer_ι_left _ _
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hcl
  have hcond : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left := by
    rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]
  refine ⟨I, fun A _ ρ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · let i : Over.mk (spMap ρ ≫ c) ⟶ Over.mk c := Over.homMk (spMap ρ)
    have hi : i ≫ f = i ≫ g := by
      ext1
      exact h
    let l := equalizer.lift i hi
    have h1 : spMap ρ = l.left ≫ (equalizer.ι f g).left := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    rw [he] at h1
    let σ := Spec.preimage (l.left ≫ e.hom)
    have h2 : spMap ρ = Spec.map σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [Spec.map_preimage, Category.assoc]
      exact h1
    rw [← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    intro x hx
    have h4 : ρ x = σ.hom (Ideal.Quotient.mk I x) := by
      have := congrArg (fun q => q.hom x) h3
      simpa using this
    rw [RingHom.mem_ker, h4, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  · let q : (R ⧸ I) →+* A := Ideal.Quotient.lift I ρ (fun a ha => h ha)
    have hq : CommRingCat.ofHom ρ =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom q := by
      ext x
      exact (Ideal.Quotient.lift_mk I ρ (fun a ha => h ha)).symm
    have h1 : spMap ρ = (spMap q ≫ e.inv) ≫ (equalizer.ι f g).left := by
      rw [he, Category.assoc, Iso.inv_hom_id_assoc, spMap, hq, Spec.map_comp]
    rw [h1]
    simp only [Category.assoc, hcond]

open AddMonoidAlgebra in

theorem exists_span_of_coideal (k X : Type) [Field k] [AddCommGroup X] (J : Ideal (AddMonoidAlgebra k X))
    (h1 : ∀ f ∈ J, Coalgebra.counit (R := k) f = 0)
    (h2 : ∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) :
    ∃ Y : AddSubgroup X, J = Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  haveI : (J.restrictScalars k).IsCoideal := ⟨fun x hx => h1 x hx, fun x hx => h2 x hx⟩
  haveI : Nontrivial (AddMonoidAlgebra k X ⧸ J) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun h => ?_
    have := h1 1 (h ▸ Submodule.mem_top)
    simp at this
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.CommAlg.ker_eq_span_single_sub_one k X (AddMonoidAlgebra k X ⧸ J)
    (Bialgebra.Quotient.mkBialgHom (R := k) J) Ideal.Quotient.mk_surjective
  refine ⟨Y, ?_⟩
  rw [← hY]
  exact (Ideal.mk_ker).symm

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
  {k : Type} [Field k]

theorem exists_ringHom_of_point {A : Type} [CommRing A] (g : k →+* A) {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ ρ : AddMonoidAlgebra k X →+* A, ρ.comp (algebraMap k (AddMonoidAlgebra k X)) = g ∧
      ∀ χ, ρ (AddMonoidAlgebra.single χ 1) = charVal t χ := by
  obtain ⟨h0, hadd⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t
  letI : Algebra k A := g.toAlgebra
  let w : Multiplicative X →* A :=
    { toFun := fun x => charVal t x.toAdd
      map_one' := h0
      map_mul' := fun x y => hadd x.toAdd y.toAdd }
  refine ⟨(AddMonoidAlgebra.lift k A X w : AddMonoidAlgebra k X →ₐ[k] A).toRingHom, ?_, fun χ => ?_⟩
  · ext c
    exact (AddMonoidAlgebra.lift k A X w).commutes c
  · simp [w]

theorem exists_universal_point (b : Sp k ⟶ S) :
    ∃ t₀ : Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ splitTorus S X,
      ∀ χ, charVal t₀ χ = AddMonoidAlgebra.single χ 1 := by
  obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra k X)
    (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b)).2.2.2.2.1 (AddMonoidAlgebra.of k X)
  exact ⟨t, fun χ => by simpa using ht χ⟩

theorem spMap_comp_base {K A : Type} [CommRing K] [CommRing A] (g₀ : k →+* K) (ρ : K →+* A) (b : Sp k ⟶ S) :
    spMap ρ ≫ spMap g₀ ≫ b = spMap (ρ.comp g₀) ≫ b := by
  rw [← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem exists_killing_ideal [IsSeparated G.hom] (u : splitTorus S X ⟶ G) [IsMonHom u] (b : Sp k ⟶ S) :
    ∃ J : Ideal (AddMonoidAlgebra k X), ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ) := by
  obtain ⟨t₀, ht₀⟩ := exists_universal_point (X := X) b
  obtain ⟨J, hJ⟩ := exists_ideal_eq_iff (t₀ ≫ u) (1 : _ ⟶ G)
  refine ⟨J, fun A _ ρ a ha t ht => ?_⟩
  rw [← spMap_comp_base] at ha
  subst ha
  rw [← hJ A ρ]
  let h : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶
      Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) := Over.homMk (spMap ρ)
  have e : t = h ≫ t₀ := by
    refine (GlobalTheory.T.charVal_multiplicative S X A _).1 _ _ fun χ => ?_
    rw [ht, (GlobalTheory.T.charVal_multiplicative S X _ _).2.2.2.2.2 A ρ t₀ (h ≫ t₀) rfl χ, ht₀]
  have e1 : (1 : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ G) = h ≫ 1 :=
    (MonObj.comp_one h).symm
  rw [e, Category.assoc, e1]
  constructor
  · intro h'
    exact congrArg (fun q => q.left) h'
  · intro h'
    ext1
    exact h'

open TensorProduct in

theorem killing_ideal_coideal (b : Sp k ⟶ S) (u : splitTorus S X ⟶ G) [IsMonHom u]
    (J : Ideal (AddMonoidAlgebra k X))
    (hJ : ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ)) :
    (∀ f ∈ J, Coalgebra.counit (R := k) f = 0) ∧
    (∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) := by
  constructor
  · let ε : AddMonoidAlgebra k X →ₐ[k] k := Bialgebra.counitAlgHom k (AddMonoidAlgebra k X)
    have hε : (ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k := by
      ext c
      exact ε.commutes c
    have hb : b = spMap ((ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      rw [hε]
      change b = Spec.map (𝟙 _) ≫ b
      rw [Spec.map_id, Category.id_comp]
    have hk := (hJ k (ε : AddMonoidAlgebra k X →+* k) b hb (1 : Over.mk b ⟶ splitTorus S X) ?_).1 (MonObj.one_comp u)
    · intro f hf
      exact hk hf
    · intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X k b).2.2.1 χ]
      simp [ε]
  · let Q := AddMonoidAlgebra k X ⧸ J
    let mkQ : AddMonoidAlgebra k X →ₐ[k] Q := Ideal.Quotient.mkₐ k J
    let c : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q :=
      (Algebra.TensorProduct.map mkQ mkQ).comp (Bialgebra.comulAlgHom k (AddMonoidAlgebra k X))
    let i₁ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeLeft.comp mkQ
    let i₂ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeRight.comp mkQ
    let A := Q ⊗[k] Q
    let a : Sp A ⟶ S := spMap (algebraMap k A) ≫ b
    have hcomp : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A,
        a = spMap ((φ : AddMonoidAlgebra k X →+* A).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      intro φ
      rw [φ.comp_algebraMap]
    have hpt : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A, ∃ t : Over.mk a ⟶ splitTorus S X,
        ∀ χ, charVal t χ = φ (AddMonoidAlgebra.single χ 1) := by
      intro φ
      obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1
        (((φ : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X))
      exact ⟨t, fun χ => by simpa using ht χ⟩
    obtain ⟨t₁, ht₁⟩ := hpt i₁
    obtain ⟨t₂, ht₂⟩ := hpt i₂
    have k₁ : t₁ ≫ u = 1 := (hJ A (i₁ : AddMonoidAlgebra k X →+* A) a (hcomp i₁) t₁ ht₁).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₁, this]
    have k₂ : t₂ ≫ u = 1 := (hJ A (i₂ : AddMonoidAlgebra k X →+* A) a (hcomp i₂) t₂ ht₂).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₂, this]
    have hc : ∀ χ, charVal (t₁ * t₂) χ = (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) := by
      intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X A a).2.1 t₁ t₂ χ, ht₁, ht₂]
      have e : (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) = mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ mkQ (AddMonoidAlgebra.single χ 1) := by
        simp [c, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply]
      rw [e]
      change (mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] mkQ (AddMonoidAlgebra.single χ 1)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have hk := (hJ A (c : AddMonoidAlgebra k X →+* A) a (hcomp c) (t₁ * t₂) hc).1
      (by rw [MonObj.mul_comp, k₁, k₂, _root_.mul_one])
    intro f hf
    exact hk hf

theorem exists_mu_killed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X]
    [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (b : Sp k ⟶ S)
    (M : LieModel (splitTorus S X) b (X →+ k)), IsCocharLie M → ∀ δ : X →+ k, δ ≠ 0 → M.pt δ ≫ u = 1 →
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ KillsOver u ψ.ker b := by
  intro S G _ _ X _ _ u _ k _ b M hM δ hδ hu
  obtain ⟨J, hJ⟩ := exists_killing_ideal (k := k) u b
  obtain ⟨h1, h2⟩ := killing_ideal_coideal b u J hJ
  obtain ⟨Y, hY⟩ := exists_span_of_coideal k X J h1 h2
  have hmain : ∀ (A : Type) [CommRing A] (g : k →+* A) (a : Sp A ⟶ S), a = spMap g ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (t ≫ u = 1 ↔ ∀ y ∈ Y, charVal t y = 1) := by
    intro A _ g a ha t
    obtain ⟨ρ, hρ, hv⟩ := exists_ringHom_of_point (k := k) g t
    rw [hJ A ρ a (by rw [hρ, ha]) t (fun χ => (hv χ).symm), hY, Ideal.span_le]
    constructor
    · intro h y hy
      have h0 : ρ (AddMonoidAlgebra.single y 1 - 1) = 0 := h ⟨y, hy, rfl⟩
      rwa [map_sub, map_one, hv, sub_eq_zero] at h0
    · rintro h _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hv, h y hy, sub_self]
  have hδY : ∀ y ∈ Y, δ y = 0 := by
    intro y hy
    have h0 := (hmain (DualNumber k) (algebraMap k (DualNumber k)) _ rfl (M.pt δ)).1 hu y hy
    rw [hM δ y] at h0
    simpa using congrArg TrivSqZeroExt.snd h0
  obtain ⟨l, hl, ψ, hs, hψ⟩ := GlobalTheory.CompanionTheory.QuotPrime.exists_surjective_zmod_of_ne_zero k X Y δ hδ hδY
  exact ⟨l, hl, ψ, hs, fun A _ g t ht => (hmain A g _ rfl t).2 fun y hy => ht y (hψ y hy)⟩

end GlobalTheory.CompanionTheory.Ar.TsField
