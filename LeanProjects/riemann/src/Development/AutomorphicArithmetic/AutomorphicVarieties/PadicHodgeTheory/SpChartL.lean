import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpLiftL
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TangentSpaceDeformationAtL
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H]

private theorem cl_prj (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (c : Fin 4 → R) (X : M4 R) (i : Fin 4) : prj (fun a => f (c a)) (F X) i = F (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R, Polynomial.aeval (F X) (p.map f) = F (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hF, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem cl_eqs (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (hadj : ∀ X, adj (F X) = F (adj X)) (hch : ∀ X : M4 R, (F X).charpoly = X.charpoly.map f)
    (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) (r' : H →* M4 K)
    (hr : ∀ g, r' g = F (r g)) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r') ∧
    (Function.Injective f → Function.Injective F →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r' →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have e0 : ∀ g, adj (r' g) * r' g = F (adj (r g) * r g) := fun g => by rw [hr, hadj, map_mul]
  have e1 : ∀ a : R, f a • (1 : M4 K) = F (a • 1) := fun a => by rw [hF, map_one]
  have e2 : (∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀)))) =
      (∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).map f := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have e3 : ∀ i, prj (fun a => f (ps a s₀)) (r' s₀) i = F (prj (fun a => ps a s₀) (r s₀) i) := fun i => by
    rw [hr, cl_prj f F hF (fun a => ps a s₀)]
  refine ⟨fun ⟨h1, h⟩ => ⟨fun g => ?_, ?_, fun g i j hij => ?_, fun s hs i => ?_⟩,
    fun hf hi ⟨h1, h⟩ => ⟨fun g => hi ?_, Polynomial.map_injective f hf ?_, fun g i j hij => hi ?_,
      fun s hs i => hi ?_⟩⟩
  · exact (e0 g).trans ((congrArg F (h1 g)).trans (e1 _).symm)
  · rw [hr, hch, h.charpoly, e2]
  · rw [e3, e3, hr, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · rw [e3, hr s, e1, ← map_sub, ← map_mul, ← map_mul, h.inert s hs i, map_zero]
  · exact (e0 g).symm.trans ((h1 g).trans (e1 _))
  · rw [← hch, ← hr, h.charpoly, e2]
  · rw [map_mul, map_mul, ← e3, ← e3, ← hr, h.stable g i j hij, map_zero]
  · rw [map_mul, map_mul, map_sub, ← e3, ← hr, ← e1, h.inert s hs i, map_zero]

private theorem cl_map (f : R →+* K) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r)) ∧
    (Function.Injective f →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have h := cl_eqs f f.mapMatrix (fun a X => by ext i j; simp)
    (fun X => by
      ext i j
      simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul])
    (fun X => Matrix.charpoly_map X f) I ν ps s₀ r (mapRep f r) fun _ => rfl
  exact ⟨h.1, fun hf => h.2 hf fun X Y e => Matrix.map_injective hf e⟩

private def cl_conj (τ : ℤ × ℤ → R) (h0 : τ 0 = 1) (hm : ∀ i j, τ (i + j) = τ i * τ j) : M4 R →+* M4 R where
  toFun X := Matrix.of fun a b => τ (wt a b) * X a b
  map_one' := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [(wt_eq_zero a a).2 rfl, h0]
    · simp [Matrix.one_apply_ne h]
  map_mul' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : wt a b = wt a k + wt k b := by simp [wt]
    rw [this, hm]
    ring
  map_zero' := by ext a b; simp
  map_add' X Y := by ext a b; simp [mul_add]

private theorem cl_tor (t : Multiplicative (ℤ × ℤ) →* Rˣ) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H)
    (r : H →* M4 R) (h : (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) :
    ∃ r' : H →* M4 R, (∀ g a b, r' g a b = t (Multiplicative.ofAdd (wt a b)) * r g a b) ∧
      (∀ g, IsGSp (ν g) (r' g)) ∧ Ord I ps s₀ r' := by
  let F := cl_conj (fun j => (t (Multiplicative.ofAdd j) : R)) (by simp) (fun i j => by simp [ofAdd_add])
  have hF : ∀ X a b, F X a b = t (Multiplicative.ofAdd (wt a b)) * X a b := fun _ _ _ => rfl
  refine ⟨F.toMonoidHom.comp r, fun _ _ _ => rfl,
    (cl_eqs (RingHom.id R) F (fun a X => ?_) (fun X => ?_) (fun X => ?_) I ν ps s₀ r _ fun _ => rfl).1 h⟩
  · ext i j
    simp [hF, mul_left_comm]
  · ext i j
    simp only [adj_apply, hF, wt_rev, mul_smul_comm]
  · let d : Fin 4 → Rˣ := fun a => t (Multiplicative.ofAdd (lamW a, muW a))
    let u : (M4 R)ˣ := ⟨Matrix.diagonal fun a => d a, Matrix.diagonal fun a => ((d a)⁻¹ : Rˣ),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
    have : F X = u.val * X * u⁻¹.val := by
      ext a b
      show _ = (Matrix.diagonal (fun a => (d a : R)) * X * Matrix.diagonal fun a => (((d a)⁻¹ : Rˣ) : R)) a b
      have e : wt a b = (lamW a, muW a) - (lamW b, muW b) := rfl
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hF, e, ofAdd_sub, map_div, div_eq_mul_inv, Units.val_mul]
      ring
    rw [this, Polynomial.map_id, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Gen

private theorem cl_count {n : ℕ} (u : Fin n → ℤ × ℤ) (h : ∀ j, Nat.card {i // u i = j} = dimsL j) : n = 14 := by
  classical
  have h1 : ∀ i, u i ∈ wts := fun i => by
    by_contra hn
    have h2 : dimsL (u i) = 0 := by
      unfold dimsL
      rw [if_neg, if_neg hn]
      rintro (e | e | e | e | e) <;> exact hn (by rw [e]; decide)
    haveI : Nonempty {k // u k = u i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne' ((h _).trans h2)
  have h3 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := wts) (f := u) fun i _ => h1 i
  have h4 : ∀ j, (Finset.univ.filter fun i => u i = j).card = dimsL j := fun j => by
    rw [← h j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [h4, Finset.card_univ, Fintype.card_fin] at h3
  rw [h3]
  decide

theorem UpperTheory.V.Loc.spChartL :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (R : Type) [CommRing R] [Algebra ↥c.O R] [IsCO ↥c.O R] (ρ : Lift c.O (D.rbarAt l) R), Represents D.condL ρ → ∃ (x : R →ₐ[c.O] c.O) (P : Ideal R) (w : Fin 14 → ℤ × ℤ) (φ : R →ₐ[c.O] MvPowerSeries (Fin 14) E), (ρ.map x).hom = D.r0At l ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ j, Nat.card {i // w i = j} = dimsL j) ∧ ∀ g a b, φ (ρ.hom g a b) ∈ wtPart E w (wt a b) := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ R _ _ _ ρ hρ
  haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec (F := ℚ) (D.pl l)).isCompact
  have hmap : ∀ (B B' : Type) [CommRing B] [Algebra c.O B] [CommRing B'] [Algebra c.O B'] (f : B →ₐ[c.O] B')
      (r : D.Gp l →* M4 B), (EqL D r → EqL D (mapRep (f : B →+* B') r)) ∧
        (Function.Injective f → EqL D (mapRep (f : B →+* B') r) → EqL D r) := by
    intro B B' _ _ _ _ f r
    have h := cl_map (f : B →+* B') ((D.Ip l).subgroupOf (D.Gp l)) (fun g => algebraMap c.O B (D.th g))
      (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r
    have hy : ∀ a : c.O, (f : B →+* B') (algebraMap c.O B a) = algebraMap c.O B' a := fun a => f.commutes a
    simp only [hy] at h
    exact h
  obtain ⟨ρ₁, h₁, hpt⟩ := r0pt D hD
  have hr0 : (D.loc ρ₁ l).hom = D.r0At l := congrArg (fun r : G ℚ Ω →* M4 c.O => r.comp (D.Gp l).subtype) h₁
  have h0 : EqL D (D.loc ρ₁ l).hom := by
    obtain ⟨B, _, _, _, _, ρ', h1, -, y, hy⟩ := hpt.atL
    rw [← hy]
    exact (hmap B c.O y ρ'.hom).1 h1
  have hst : ρ.TStable fun a => (lamW a, muW a) := by
    intro R' _ _ _ f t ht
    obtain ⟨r', h1, h2⟩ := cl_tor t _ _ _ _ (ρ.map f).hom ((hρ R').1 f)
    let ρ' : Lift c.O (D.rbarAt l) R' :=
      { hom := r'
        cont := fun a b N => by
          simp only [h1, map_mul]
          exact ((ρ.map f).cont a b N).comp (_ * ·)
        red := fun g a b => by rw [h1, map_mul, ht, one_mul, (ρ.map f).red] }
    obtain ⟨f', hf', -⟩ := (hρ R').2 ρ' h2
    refine ⟨f', fun g a b => ?_⟩
    rw [hf']
    exact h1 g a b
  obtain ⟨x, P, n, u, φ, h1, h2, h3, h4, h5⟩ := liftChart (l := l) (D.rbarAt l) (fun a => (lamW a, muW a)) E R ρ
    (fun B _ _ r => EqL D r) hmap hρ hst (D.loc ρ₁ l) h0
    (fun g a b hab => by
      rw [hr0]
      exact Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) fun e : a = b => hab (by rw [e]))
    (fun B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hπp r' e1 e2 e3 => by
      obtain ⟨r, k1, k2, k3⟩ := spLiftL hP D hD E B π hπ B' π' hπ' p hp hπp r' ⟨hr0 ▸ e1, e2⟩ e3
      exact ⟨r, k1.cont, k2, k3⟩)
  have h6 : ∀ j, Nat.card {i // u i = j} = dimsL j := fun j => by
    obtain ⟨S, hS, hS'⟩ := h5 j
    rw [hr0] at hS'
    exact hS.trans (UpperTheory.tangent_space_deformation_at_l hP D hD E j S hS')
  obtain rfl := cl_count u h6
  exact ⟨x, P, u, φ, by rw [h1, hr0], h2, h3, h6, h4⟩
