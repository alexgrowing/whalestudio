import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsTuple

theorem exists_power {X : Scheme.{0}} (Q : Over X) [IsAffineHom Q.hom] [Flat Q.hom] (J : Type) [Finite J] :
    ∃ (R : Over X) (p : J → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : J → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by

  have key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by
    intro n
    induction n with
    | zero =>
      refine ⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩
      · show IsAffineHom (𝟙 X)
        infer_instance
      · show Flat (𝟙 X)
        infer_instance
    | succ n ih =>
      obtain ⟨R, p, hRa, hRf, hR⟩ := ih
      have ha : IsAffineHom (pullback.fst R.hom Q.hom) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›
      let R' : Over X := Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)
      let a : R' ⟶ Q := Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm
      let b : R' ⟶ R := Over.homMk (pullback.fst R.hom Q.hom) rfl
      refine ⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩
      · show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · show Flat (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · intro T u
        obtain ⟨v, hv⟩ := hR T (fun i => u i.succ)
        have hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom := by rw [Over.w v, Over.w (u 0)]
        refine ⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by
          change _ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _
          rw [pullback.lift_fst_assoc, Over.w v]), ?_⟩
        refine Fin.cases ?_ (fun i => ?_)
        · apply Over.OverMorphism.ext
          simp only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]
          exact pullback.lift_snd _ _ _
        · apply Over.OverMorphism.ext
          simp only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]
          rw [pullback.lift_fst_assoc]
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨R, p, ha, hf, hu⟩ := key n
  refine ⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩
  obtain ⟨v, hv⟩ := hu T (fun i => u (e.symm i))
  exact ⟨v, fun j => by simpa using hv (e j)⟩

theorem exists_point {X : Scheme.{0}} (R : Over X) [IsAffineHom R.hom] [Flat R.hom] (S : Type) [CommRing S]
    (x0 : Sp S ⟶ X) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Over.mk (spMap φ ≫ x0) ⟶ R), φ.Flat ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : Over.mk (spMap ψ ≫ x0) ⟶ R),
        ∃ χ : B →+* T, χ.comp φ = ψ ∧ u.left = spMap χ ≫ w.left := by

  have : IsAffine (pullback x0 R.hom) := inferInstance
  let e := (pullback x0 R.hom).isoSpec
  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom :=
    ⟨_, Spec.map_preimage _⟩
  have hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom := by
    simp [hφ, pullback.condition]
  refine ⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩
  · have hfl : Flat (spMap φ) := by
      rw [hφ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  · intro T _ ψ u
    let g : Sp T ⟶ pullback x0 R.hom := pullback.lift (spMap ψ) u.left (Over.w u).symm
    obtain ⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom := ⟨_, Spec.map_preimage _⟩
    refine ⟨χ, ?_, ?_⟩
    · have h1 : spMap (χ.comp φ) = spMap ψ := by
        change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _
        rw [Spec.map_comp]
        change spMap χ ≫ spMap φ = _
        rw [hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_fst _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    · rw [hχ]
      change u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact (pullback.lift_snd _ _ _).symm

theorem exists_kernel {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] :
    ∃ (Q : Over X) (j : Q ⟶ A), IsAffineHom Q.hom ∧ Flat Q.hom ∧ j ^ k = 1 ∧
      ∀ (T : Over X) (u : T ⟶ A), u ^ k = 1 → ∃ v : T ⟶ Q, v ≫ j = u := by

  have hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k := by
    intro T u
    rw [show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]

  let Q : Over X := Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)
  have hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom := by
    rw [← Over.w (mulA A k), pullback.condition_assoc, Over.w]
    exact Category.comp_id _
  let j : Q ⟶ A := Over.homMk (pullback.fst _ _) hjw
  refine ⟨Q, j, ?_, ?_, ?_, ?_⟩
  · show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · rw [hm j]
    apply Over.OverMorphism.ext
    show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left
    rw [Over.comp_left, Over.comp_left]
    exact pullback.condition
  · intro T u hu
    have h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one := by
      rw [← hm u, hu]
      rfl
    have h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left := by
      have h2 := congrArg (fun f => f.left) h0
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact pullback.lift_fst _ _ _

theorem exists_tuple {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (J : Type) [Finite J] :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Over.mk (spMap φ ≫ x0) ⟶ A)), φ.Flat ∧
      (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (Over.mk (spMap ψ ≫ x0) ⟶ A)),
        (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  obtain ⟨Q, j, hQa, hQf, hj, hQ⟩ := exists_kernel A k
  have := hQa
  have := hQf
  obtain ⟨R, p, hRa, hRf, hR⟩ := exists_power Q J
  have := hRa
  have := hRf
  obtain ⟨B, iB, φ, w, hφ, hw⟩ := exists_point R S x0
  refine ⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩
  · show (w ≫ p i ≫ j) ^ k = 1
    rw [← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]
  · intro T _ ψ u hu
    choose v hv using fun i => hQ _ (u i) (hu i)
    obtain ⟨v', hv'⟩ := hR _ v
    obtain ⟨χ, hχ, hχw⟩ := hw T ψ v'
    refine ⟨χ, hχ, fun i => ?_⟩
    rw [← hv i, ← hv' i]
    simp [hχw]

end TorsTuple

theorem exists_flat_universal_torsion_tuple :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (J : Type) [Fintype J], ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.Flat ∧ (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)), (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk J _

  have hN := hL.mulN
  unfold MulNSt at hN
  obtain ⟨hloc, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨hfin, hfl, -⟩ := hN Xo.X (UnivPol.pol Xo) k hk
  have hfin' : IsFinite (mulA Xo.univ.t.G k).left := hfin
  have hfl' : Flat (mulA Xo.univ.t.G k).left := hfl
  exact TorsTuple.exists_tuple Xo.univ.t.G k S x0 J

end GlobalTheory
