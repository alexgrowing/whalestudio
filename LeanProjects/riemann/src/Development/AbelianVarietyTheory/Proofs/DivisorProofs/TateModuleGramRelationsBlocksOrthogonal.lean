import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushEquivPolPull

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

abbrev phiTP (a : Fin p) : letI := H.starRing; (pointA hv ε i X true).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiTQ (b : Fin q) : letI := H.starRing; (pointA hv ε i X false).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A false) hv ε i (X.lin (Sum.inr b))

variable [IsAlgClosed C] [CharZero C]

omit [NumberField K] in

theorem pairT_patT_gram {T T' : PAT H (Sp (𝓞 K))} {f f' : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)
    (hf' : Serre.IsLinearHom T.t.act T'.t.act f') {g : 𝓞 E}
    (h : LamEq T'.t.PP.L f f' T.t.PP.L (T.t.act.act g) (𝟙 _)) : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i T').A ε (patT hv ε i hf s) (patT hv ε i hf' t) =
      pairT (patPoint hv ε i T).A ε ((patPoint hv ε i T).actT g s) t := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f' := hf'.isMonHom
  haveI := (patAct T).hom g
  intro s t
  have e := pairT_homT_of_lamEq (X := T.pol) (Y := T.pol) (A := T'.pol) (B := T.pol) hv ε (embO hv i) (patAct T) (patAct T)
    (patAct T') (patAct T) f f' ((patAct T).act g) (𝟙 _) h s t
  rw [homT_act, homT_id] at e
  exact e

theorem pairT_patT_orth (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {A A' B : PAT H (Sp (𝓞 K))} {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m') {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hf' : Serre.IsLinearHom A'.t.act B.t.act f') : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i B).A ε (patT hv ε i hf s) (patT hv ε i hf' t) = 0 := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A.pol.A) (N := B.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A'.pol.A) (N := B.pol.A) f' := hf'.isMonHom
  haveI : IsMonHom (1 : A'.pol.A ⟶ A.pol.A) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  intro s t
  have e := pairT_homT_of_lamEq (X := A.pol) (Y := A'.pol) (A := B.pol) (B := A.pol) hv ε (embO hv i) (patAct A)
    (patAct A') (patAct B) (patAct A) f f' (𝟙 _) 1 (lamEq_one hρ A A' B hA hA' hf hf') s t
  rw [homT_one, LinearMap.zero_apply, map_zero] at e
  exact e

theorem tateModule_gram_relations_blocks_orthogonal {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTP hv ε i X b t) =
      pairT (pointA hv ε i X true).A ε ((pointA hv ε i X true).actT (gP a b) s) t) ∧
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTQ hv ε i X a s) (phiTQ hv ε i X b t) =
      pairT (pointA hv ε i X false).A ε ((pointA hv ε i X false).actT (gQ a b) s) t) ∧
    ∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTQ hv ε i X b t) = 0 :=
  ⟨fun a b => pairT_patT_gram (T := X.A true) hv ε i (X.lin (.inl a)) (X.lin (.inl b)) ((lamEq_of_isGram X h).1 a b),
    fun a b => pairT_patT_gram (T := X.A false) hv ε i (X.lin (.inr a)) (X.lin (.inr b)) ((lamEq_of_isGram X h).2 a b),
    fun a b => pairT_patT_orth (A := X.A true) (A' := X.A false) hv ε i X.ρ_sq X.typeP X.typeM (X.lin (.inl a))
      (X.lin (.inr b))⟩

end At

theorem exists_inverse_tateModule_sum_up_to_integer (X : CMObj H K ρ σ₁ p q) : letI := H.starRing
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
      [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C),
      ∃ (ψ : Fin p → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T))
        (ψ' : Fin q → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)),
        (∀ t, ∑ k, phiTP hv ε i X k (ψ k t) + ∑ k, phiTQ hv ε i X k (ψ' k t) = N • t) ∧
        ∀ (s : Fin p → (pointA hv ε i X true).T) (s' : Fin q → (pointA hv ε i X false).T),
          (∀ l, ψ l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s l) ∧
          ∀ l, ψ' l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s' l := by
  letI := H.starRing
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨N, ψ, ψ', hN, hψ, hψ', h1, h2⟩ := exists_inverse X
  exact ⟨N, hN, fun ℓ _ C _ v O _ _ hv ε i => ⟨_, _, homT_inverse (B := X.B.pol) (A := (X.A true).pol)
    (A' := (X.A false).pol) hv ε (embO hv i) (patAct X.B) (patAct (X.A true)) (patAct (X.A false)) (phiP X) (phiQ X)
    ψ ψ' h1 h2⟩⟩

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q) [IsAlgClosed C] [CharZero C]

theorem sumT_injective : letI := H.starRing
    Function.Injective fun z : (Fin p → (pointA hv ε i X true).T) × (Fin q → (pointA hv ε i X false).T) =>
      ∑ k, phiTP hv ε i X k (z.1 k) + ∑ k, phiTQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', -, h2⟩ := h ℓ C v O hv ε i
  have key : ∀ (P : Point ℓ v O (𝓞 E)) (x y : P.T), N • x = N • y → x = y := fun P x y e => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]] at e
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') e
  exact fun z z' e => Prod.ext
    (funext fun l => key _ _ _ (((h2 z.1 z.2).1 l).symm.trans ((congrArg (ψ l) e).trans ((h2 z'.1 z'.2).1 l))))
    (funext fun l => key _ _ _ (((h2 z.1 z.2).2 l).symm.trans ((congrArg (ψ' l) e).trans ((h2 z'.1 z'.2).2 l))))

include hv ε i in
theorem gram_det_of_emb {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  letI := H.starRing
  obtain ⟨N, hN, hI⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, -⟩ := hI ℓ C v O hv ε i
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  have hg : ∀ b, 0 < (pointA hv ε i X b).A.g := fun b => (dims X).2.2.trans_eq ((dims X).1 b).symm
  have hi := sumT_injective hv ε i X
  refine ⟨det_ne_zero_of_inverse hN (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
      (hg true) (phiTP hv ε i X) (phiTQ hv ε i X) gP hP hO (fun t => ⟨_, _, h1 t⟩) fun s hs => ?_,
    det_ne_zero_of_inverse hN (A := pointA hv ε i X false) (A' := pointA hv ε i X true) (B := pointB hv ε i X)
      (hg false) (phiTQ hv ε i X) (phiTP hv ε i X) gQ hQ (fun a b s t => ?_)
      (fun t => ⟨_, _, (add_comm _ _).trans (h1 t)⟩) fun s hs => ?_,
    star_gram (A := pointA hv ε i X true) (B := pointB hv ε i X) (hg true) (phiTP hv ε i X) gP hP,
    star_gram (A := pointA hv ε i X false) (B := pointB hv ε i X) (hg false) (phiTQ hv ε i X) gQ hQ⟩
  · exact congrArg Prod.fst (@hi (s, 0) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))
  · exact ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s))
  · exact congrArg Prod.snd (@hi (0, s) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))

variable [Algebra ℤ_[ℓ] C]

theorem gram_V {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVP hv ε i X b y) =
      (pointA hv ε i X true).pairV ((pointA hv ε i X true).actV (gP a b) x) y) ∧
    (∀ a b x y, (pointB hv ε i X).pairV (phiVQ hv ε i X a x) (phiVQ hv ε i X b y) =
      (pointA hv ε i X false).pairV ((pointA hv ε i X false).actV (gQ a b) x) y) ∧
    ∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVQ hv ε i X b y) = 0 := by
  letI := H.starRing
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  refine ⟨fun a b x y => ?_, fun a b x y => ?_, fun a b x y => ?_⟩
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X true) (g₂ := LinearMap.id) (hP a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X false) (g₂ := LinearMap.id) (hQ a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointB hv ε i X) (g₁ := 0) (g₂ := 0)
      (fun s t => (hO a b s t).trans (map_zero _).symm) x y
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero] at e
    exact e

theorem sumV_bijective : letI := H.starRing
    Function.Bijective fun z : (Fin p → (pointA hv ε i X true).V) × (Fin q → (pointA hv ε i X false).V) =>
      ∑ k, phiVP hv ε i X k (z.1 k) + ∑ k, phiVQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, h2⟩ := h ℓ C v O hv ε i
  exact bijective_of_inverse (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiTP hv ε i X) (phiTQ hv ε i X) hN ψ ψ' h1 h2

end At

theorem gram_det (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  exact gram_det_of_emb (PadicComplexInt.integers 2) ε (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[2])).toRingHom X h

theorem exists_patT_equiv {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) {C' : Type} [Field C']
    {v' : Valuation C' ℝ≥0} {O' : Type} [CommRing O'] [Algebra O' C'] [IsAlgClosed C'] [CharZero C']
    (hv' : v'.Integers O') (ε' : Eps ℓ C') (i' : K →+* C') : letI := H.starRing
    ∃ e : ∀ T : PAT H (Sp (𝓞 K)), (patPoint hv ε i T).T ≃ₗ[ℤ_[ℓ]] (patPoint hv' ε' i' T).T,
      (∀ T a t, e T ((patPoint hv ε i T).actT a t) = (patPoint hv' ε' i' T).actT a (e T t)) ∧
      ∀ (T T' : PAT H (Sp (𝓞 K))) (f : T.t.G ⟶ T'.t.G) (hf : Serre.IsLinearHom T.t.act T'.t.act f) (t),
        e T' (patT hv ε i hf t) = patT hv' ε' i' hf (e T t) := by
  letI := H.starRing
  have lift : ∀ {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
      (hv : v.Integers O) (i : K →+* C), ∃ κ : AlgebraicClosure K →+* C,
        κ.comp (algebraMap (𝓞 K) (AlgebraicClosure K)) = (algebraMap O C).comp (embO hv i) := by
    intro C _ _ v O _ _ hv i
    letI := i.toAlgebra
    refine ⟨(IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := C)).toRingHom, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_embO, IsScalarTower.algebraMap_apply (𝓞 K) K]
    exact AlgHom.commutes _ _
  obtain ⟨κ, hκ⟩ := lift hv i
  obtain ⟨κ', hκ'⟩ := lift hv' i'
  obtain ⟨e, he⟩ := exists_tateEquiv (Λ := 𝓞 E) hv ε (embO hv i) _ κ hκ
  obtain ⟨e', he'⟩ := exists_tateEquiv (Λ := 𝓞 E) hv' ε' (embO hv' i') _ κ' hκ'
  have key : ∀ (B B' : Out.PolAV (Sp (𝓞 K))) (o : B.OAct (𝓞 E)) (o' : B'.OAct (𝓞 E)) (f : B.A ⟶ B'.A) [IsMonHom f] (t),
      e' B' o' ((e B' o').symm (homT hv ε (embO hv i) o o' f t)) =
        homT hv' ε' (embO hv' i') o o' f (e' B o ((e B o).symm t)) := fun B B' o o' f _ t => by
    rw [← he', (e B' o').symm_apply_eq.2 ((congrArg _ ((e B o).apply_symm_apply t).symm).trans (he B B' o o' f _).symm)]
  refine ⟨fun T => (e T.pol (patAct T)).symm.trans (e' T.pol (patAct T)), fun T a t => ?_, fun T T' f hf t => ?_⟩
  · haveI := (patAct T).hom a
    have h := key T.pol T.pol (patAct T) (patAct T) ((patAct T).act a) t
    rw [homT_act, homT_act] at h
    exact h
  · haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
    exact key T.pol T'.pol (patAct T) (patAct T') f t

example (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ]) (i : K →+* ℂ_[ℓ]) :
    letI := H.starRing; letI := algPadicField ℓ
    ∀ a b x y, (pointB (PadicComplexInt.integers ℓ) ε i X).pairV (phiVP (PadicComplexInt.integers ℓ) ε i X a x)
      (phiVQ (PadicComplexInt.integers ℓ) ε i X b y) = 0 :=
  letI := algPadicField ℓ
  (gram_V (PadicComplexInt.integers ℓ) ε i X h).2.2

end Object

end GlobalTheory.GramAt
