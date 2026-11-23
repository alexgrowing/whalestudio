import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.HasEnoughRootsOfUnityGlobalSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreField

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull

section Ring

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def homRing : Subring (AddMonoid.End (Additive (A ⟶ A))) where
  carrier := {f | ∃ u : A ⟶ A, IsMonHom u ∧ ∀ x : A ⟶ A, f (Additive.ofMul x) = Additive.ofMul (x ≫ u)}
  mul_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    exact ⟨v ≫ u, inferInstance, fun x => by
      change f (g _) = _
      rw [hg, hf, Category.assoc]⟩
  one_mem' := ⟨𝟙 A, inferInstance, fun x => by rw [Category.comp_id]; rfl⟩
  add_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    refine ⟨u * v, by rw [Hom.mul_def]; infer_instance, fun x => ?_⟩
    rw [MonObj.comp_mul, ofMul_mul, ← hf, ← hg]; rfl
  zero_mem' := ⟨1, by rw [Hom.one_def]; infer_instance, fun x => by rw [MonObj.comp_one]; rfl⟩
  neg_mem' := by
    rintro f ⟨u, hu, hf⟩
    refine ⟨u⁻¹, by rw [Hom.inv_def]; infer_instance, fun x => ?_⟩
    rw [GrpObj.comp_inv, ofMul_inv, ← hf]; rfl

variable {A}

def toRing (u : A ⟶ A) [IsMonHom u] : homRing A :=
  ⟨MonoidHom.toAdditive (IsMonHom.monoidHom u A), u, inferInstance, fun _ => rfl⟩

theorem toRing_apply (u : A ⟶ A) [IsMonHom u] (x : A ⟶ A) :
    (toRing u).1 (Additive.ofMul x) = Additive.ofMul (x ≫ u) := rfl

theorem natCast_mul_apply (n : ℕ) (f : homRing A) (x : Additive (A ⟶ A)) :
    ((n : homRing A) * f).1 x = n • f.1 x := by
  rw [← nsmul_eq_mul]; rfl

theorem homRing_ext {f g : homRing A}
    (h : f.1 (Additive.ofMul (𝟙 A)) = g.1 (Additive.ofMul (𝟙 A))) : f = g := by
  obtain ⟨f, u, hu, hf⟩ := f
  obtain ⟨g, v, hv, hg⟩ := g
  have e : u = v := by
    simpa only [hf, hg, Category.id_comp, EmbeddingLike.apply_eq_iff_eq] using h
  subst e
  exact Subtype.ext (AddMonoidHom.ext fun x => (hf x.toMul).trans (hg x.toMul).symm)

noncomputable def iter (σ : A ≅ A) : ℕ → (A ≅ A)
  | 0 => Iso.refl A
  | m + 1 => iter σ m ≪≫ σ

omit [IsCommMonObj A] in
instance isMonHom_iter (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) : IsMonHom (iter σ m).hom := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 A))
  | succ m ih => exact inferInstanceAs (IsMonHom ((iter σ m).hom ≫ σ.hom))

theorem toRing_pow (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) :
    toRing σ.hom ^ m = toRing (iter σ m).hom := by
  induction m with
  | zero => exact homRing_ext (by rw [toRing_apply]; simp [iter])
  | succ m ih =>
    rw [pow_succ', ih]
    exact homRing_ext (by
      change (toRing σ.hom).1 ((toRing (iter σ m).hom).1 _) = _
      simp only [toRing_apply, iter, Iso.trans_hom, Category.assoc])

omit [GrpObj A] [IsCommMonObj A] in

theorem hasGen_iter {L : LB A.left} (hL : L.IsLB) (σ : A ≅ A)
    (h : HasGen L (K := Fin 2) ![σ.hom.left, 𝟙 A.left] ![1, -1]) (m : ℕ) :
    HasGen L (K := Fin 2) ![(iter σ m).hom.left, 𝟙 A.left] ![1, -1] := by
  induction m with
  | zero =>
    exact (h.mul h.inv).of_formEq hL (fun U _ f => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, iter])
  | succ m ih =>
    exact ((h.pull (iter σ m).hom.left).mul ih).of_formEq hL (fun U _ f => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, iter])

theorem exists_iter_fix (σ : A ≅ A) [IsMonHom σ.hom] (T : Over S) (n : ℕ)
    [Finite {x : T ⟶ A // x ^ n = 1}] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x : T ⟶ A, x ^ n = 1 → x ≫ (iter σ m).hom = x := by
  let f : {x : T ⟶ A // x ^ n = 1} → {x : T ⟶ A // x ^ n = 1} := fun x =>
    ⟨x.1 ≫ σ.hom, by rw [← MonObj.pow_comp, x.2, MonObj.one_comp]⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((cancel_mono σ.hom).1 (congrArg Subtype.val h))
  let e : Equiv.Perm {x : T ⟶ A // x ^ n = 1} := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have he : ∀ (m : ℕ) x, ((e ^ m) x).1 = x.1 ≫ (iter σ m).hom := by
    intro m
    induction m with
    | zero => intro x; simp [iter]
    | succ m ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      change ((e ^ m) x).1 ≫ σ.hom = _
      rw [ih, iter, Iso.trans_hom, Category.assoc]
  refine ⟨orderOf e, (orderOf_pos e).ne', fun x hx => ?_⟩
  have := he (orderOf e) ⟨x, hx⟩
  rw [pow_orderOf_eq_one] at this
  exact this.symm

end Ring

theorem exists_odd_ne_zero (K : Type) [Field K] : ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : ((5 : ℕ) : K) = 0
  · refine ⟨11, by decide, by decide, fun h' => ?_⟩
    have : (1 : K) = ((11 : ℕ) : K) - 2 * ((5 : ℕ) : K) := by push_cast; ring
    rw [h, h'] at this
    simp at this
  · exact ⟨5, by decide, le_rfl, h⟩

theorem serre_algClosed :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u → (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) → (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), Odd n → 5 ≤ n → (n : K) ≠ 0 → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ^ n = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A) → (∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : ℕ), 3 ≤ M → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A := by
  intro hM hdiv hsep hfin hmink K _ _ P M hM3 σ hσ hL hfix
  obtain ⟨n, hodd, h5, hn⟩ := exists_odd_ne_zero K
  haveI := (hM _ P n (by omega)).1
  haveI := finite_torsion_of_isFinite_mul K P n
  obtain ⟨m, hm0, hm⟩ := exists_iter_fix σ (baseOver (Spec (CommRingCat.of K))) n
  have hord : (iter σ m).hom = 𝟙 P.A :=
    hfin K P n hodd h5 hn (iter σ m) inferInstance (hasGen_iter P.isLB σ hL m) hm
  have hu : IsMonHom (σ.hom * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (σ.hom * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix T x hx, Category.comp_id, mul_inv_cancel])
  have key : toRing σ.hom = 1 := by
    refine hmink (homRing P.A) M hM3 ?_ ?_ (toRing σ.hom) (toRing φ) m hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _, _, -⟩ := hM _ P k (by omega)
        haveI : Epi (mulA P.A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (mulA P.A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K P q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.SerreField
