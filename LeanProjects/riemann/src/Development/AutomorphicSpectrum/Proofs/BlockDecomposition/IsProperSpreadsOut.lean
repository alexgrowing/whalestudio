import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteAffineCover

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter

namespace GlobalTheory.CompanionTheory.Ultra

section Core

variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))

def baseHom (W : X.affineOpens) : R₀ →+* Γ(X, W.1) :=
  (Spec.preimage (W.2.fromSpec ≫ f₀)).hom

lemma fromSpec_comp (W : X.affineOpens) :
    W.2.fromSpec ≫ f₀ = Spec.map (CommRingCat.ofHom (baseHom f₀ W)) := by
  simp [baseHom]

lemma spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    Spec.map (CommRingCat.ofHom (p.comp q)) =
      Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

lemma spec_inj {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B}
    (h : Spec.map (CommRingCat.ofHom p) = Spec.map (CommRingCat.ofHom q)) : p = q :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

lemma pt_comp (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    pt W p ≫ f₀ = Spec.map (CommRingCat.ofHom (p.comp (baseHom f₀ W))) := by
  rw [pt, Category.assoc, fromSpec_comp, spec_comp]

lemma base_eq {T A : Type} [CommRing T] [CommRing A] (ψ : R₀ →+* T) (W : X.affineOpens)
    (p : Γ(X, W.1) →+* A) (t : T →+* A)
    (l : Spec (CommRingCat.of A) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h1 : l ≫ pullback.fst _ _ = pt W p)
    (h2 : l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom t)) :
    p.comp (baseHom f₀ W) = t.comp ψ := by
  apply spec_inj
  rw [← pt_comp, ← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, spec_comp]

variable {f₀}

lemma val_lift {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] (ρ : R →+* B) (a₀ : Spec (CommRingCat.of L) ⟶ X)
    (H : a₀ ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp (ρ.comp φ)))) :
    (∃ ℓ : Spec (CommRingCat.of B) ⟶ X, ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀) ∧
    ∀ ℓ₁ ℓ₂ : Spec (CommRingCat.of B) ⟶ X,
      ℓ₁ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      ℓ₂ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₁ = a₀ →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₂ = a₀ → ℓ₁ = ℓ₂ := by
  let ã : Spec (CommRingCat.of L) ⟶ Y :=
    hpb.lift a₀ (Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)))
      (by rw [H, ← spec_comp])
  have ã₁ : ã ≫ π = a₀ := hpb.lift_fst _ _ _
  have ã₂ : ã ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)) := hpb.lift_snd _ _ _
  let sq : ValuativeCommSq f :=
    { R := B, K := L, i₁ := ã, i₂ := Spec.map (CommRingCat.ofHom ρ),
      commSq := ⟨by rw [ã₂, spec_comp]⟩ }
  obtain ⟨u⟩ := hval sq
  refine ⟨?_, ?_⟩
  · let l := (u.default : sq.commSq.LiftStruct)
    have l₁ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ l.l = ã := l.fac_left
    have l₂ : l.l ≫ f = Spec.map (CommRingCat.ofHom ρ) := l.fac_right
    refine ⟨l.l ≫ π, ?_, ?_⟩
    · rw [Category.assoc, hpb.w, ← Category.assoc, l₂, spec_comp]
    · rw [← Category.assoc, l₁, ã₁]
  · intro ℓ₁ ℓ₂ e₁ e₂ d₁ d₂
    have mk : ∀ ℓ : Spec (CommRingCat.of B) ⟶ X,
        ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
        Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀ →
        ∃ l : sq.commSq.LiftStruct, l.l ≫ π = ℓ := by
      intro ℓ e d
      let m : Spec (CommRingCat.of B) ⟶ Y :=
        hpb.lift ℓ (Spec.map (CommRingCat.ofHom ρ)) (by rw [e, spec_comp])
      have m₁ : m ≫ π = ℓ := hpb.lift_fst _ _ _
      have m₂ : m ≫ f = Spec.map (CommRingCat.ofHom ρ) := hpb.lift_snd _ _ _
      refine ⟨⟨m, ?_, m₂⟩, m₁⟩
      change Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ m = ã
      apply hpb.hom_ext
      · rw [Category.assoc, m₁, d, ã₁]
      · rw [Category.assoc, m₂, ã₂, spec_comp]
    obtain ⟨l₁, rfl⟩ := mk ℓ₁ e₁ d₁
    obtain ⟨l₂, rfl⟩ := mk ℓ₂ e₂ d₂
    rw [show l₁ = l₂ from (u.uniq l₁).trans (u.uniq l₂).symm]

variable (f₀)

variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)

omit [∀ i, IsFractionRing (V i) (K i)] [∀ i, Field (K i)] [∀ i, Algebra (V i) (K i)] in
lemma isLocalRing_ult : IsLocalRing (Ult U V) := ValuationRing.isLocalRing _

omit [∀ i, ValuationRing (V i)] [∀ i, IsFractionRing (V i) (K i)] in
lemma rep_alg {B : Type} [CommRing B] {h : ∀ i, B → V i} {g : B →+* Ult U V} (r : Rep U h g) :
    Rep U (fun i b => algebraMap (V i) (K i) (h i b))
      ((algebraMap (Ult U V) (Ult U K)).comp g) := by
  refine ⟨?_, fun b => ?_⟩
  · filter_upwards [r.1] with i ⟨p, hp⟩
    exact ⟨(algebraMap (V i) (K i)).comp p, by funext b; simp [← hp]⟩
  · rw [RingHom.comp_apply, r.2, algebraMap_mk]

theorem exists_limit_point [CompactSpace X] (φ : R₀ →+* R)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∃ (W₁ : X.affineOpens) (h₁ : ∀ i, Γ(X, W₁.1) → K i) (P : Γ(X, W₁.1) →+* Ult U K),
      Rep U h₁ P ∧
      (∀ᶠ i in (U : Filter ι), ∃ p : Γ(X, W₁.1) →+* K i, ⇑p = h₁ i ∧
        a i ≫ pullback.fst _ _ = pt W₁ p) ∧
      P.comp (baseHom f₀ W₁) = (algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ) := by
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ p : Γ(X, W.1) →+* K i,
      a i ≫ pullback.fst _ _ = pt W p := by
    refine Filter.Eventually.of_forall fun i => ?_
    obtain ⟨W, hW, hx⟩ := hS2 ((a i ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (K i) : PrimeSpectrum (K i))) trivial
    exact ⟨W, hW, exists_pt_of_isLocalRing _ W hx⟩
  obtain ⟨W₁, -, hQ⟩ := exists_of_finite U hSf hQ
  obtain ⟨h₁, hh⟩ := exists_family U hQ
  have ae : IsAEHom U h₁ := by
    filter_upwards [hh] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  refine ⟨W₁, h₁, homOf U h₁ ae, rep_homOf U h₁ ae, hh, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, homOf_apply, RingHom.comp_apply, RingHom.comp_apply, hρ, algebraMap_mk,
    mk_eq_mk_iff]
  filter_upwards [hh] with i ⟨p, hp, e⟩
  have := base_eq f₀ (ψ i) W₁ p ((algebraMap (V i) (K i)).comp (β i)) (a i) e (hsq i)
  rw [← hp]
  exact RingHom.congr_fun this r

theorem ae_exists_lift [CompactSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), ∃ l : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))),
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have H : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  obtain ⟨⟨ℓ, e1, e2⟩, -⟩ := val_lift hpb hval ρ (pt W₁ P) H
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨W₂, hx, -⟩ := exists_affine_le (show ℓ (IsLocalRing.closedPoint (Ult U V) :
    PrimeSpectrum (Ult U V)) ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨γ, rfl⟩ := exists_pt_of_isLocalRing ℓ W₂ hx
  haveI := hfp W₂
  obtain ⟨h₂, r₂⟩ := exists_rep U γ
  have hγ : γ.comp (baseHom f₀ W₂) = ρ.comp φ := spec_inj (by rw [← pt_comp, e1])
  have c1 : ∀ᶠ i in (U : Filter ι), (fun b => h₂ i (baseHom f₀ W₂ b)) = fun r => β i (ψ i r) := by
    refine ae_eq_of_fg U (h := fun i b => h₂ i (baseHom f₀ W₂ b)) (h' := fun i r => β i (ψ i r))
      ?_ (Filter.Eventually.of_forall fun i => ⟨(β i).comp (ψ i), rfl⟩) ?_
    · filter_upwards [r₂.1] with i ⟨p, hp⟩
      exact ⟨p.comp (baseHom f₀ W₂), by funext b; simp [← hp]⟩
    · intro r
      rw [← r₂.2, ← hρ]
      exact RingHom.congr_fun hγ r
  have c2 := ae_pt_eq_of_pt_eq U hfp (rep_alg U (K := K) r₂) rP (by rw [← map_pt, e2])
  filter_upwards [r₂.1, c1, c2, ha] with i ⟨p, hp⟩ d1 d2 ⟨q, hq, eq⟩
  have hb : p.comp (baseHom f₀ W₂) = (β i).comp (ψ i) := by
    refine RingHom.ext fun r => ?_
    have := congrFun d1 r
    rw [← hp] at this
    exact this
  refine ⟨pullback.lift (pt W₂ p) (Spec.map (CommRingCat.ofHom (β i)))
    (by rw [pt_comp, hb, spec_comp]), ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, map_pt, eq]
    exact d2 ((algebraMap (V i) (K i)).comp p) q (by funext b; simp [← hp]) hq
  · rw [Category.assoc, pullback.lift_snd, hsq, spec_comp]

lemma limit_lift [QuasiSeparatedSpace X] {φ : R₀ →+* R}
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    {W W₁ : X.affineOpens} {h : ∀ i, Γ(X, W.1) → V i} {G : Γ(X, W.1) →+* Ult U V} (r : Rep U h G)
    {h₁ : ∀ i, Γ(X, W₁.1) → K i} {P : Γ(X, W₁.1) →+* Ult U K} (rP : Rep U h₁ P)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W.1) →+* V i) (q : Γ(X, W₁.1) →+* K i)
      (l : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))),
      ⇑p = h i ∧ ⇑q = h₁ i ∧ l ≫ pullback.fst _ _ = pt W p ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      a i ≫ pullback.fst _ _ = pt W₁ q) :
    pt W G ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
    Spec.map (CommRingCat.ofHom (algebraMap (Ult U V) (Ult U K))) ≫ pt W G = pt W₁ P := by
  refine ⟨?_, ?_⟩
  · rw [pt_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, r.2, RingHom.comp_apply, hρ, mk_eq_mk_iff]
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    have := base_eq f₀ (ψ i) W p (β i) l h1 h2
    rw [← hp]
    exact RingHom.congr_fun this x
  · rw [map_pt]
    refine pt_eq_of_ae_pt_eq U (rep_alg U (K := K) r) rP ?_
    filter_upwards [H] with i ⟨p, q, l, hp, hq, h1, h2, h3, h4⟩
    refine ⟨(algebraMap (V i) (K i)).comp p, q, by funext b; simp [← hp], hq, ?_⟩
    rw [← map_pt, ← h1, ← Category.assoc, h3, h4]

theorem not_ae_two_lifts [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    (H : ∀ᶠ i in (U : Filter ι), ∃ l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i))) : False := by
  obtain ⟨W₁, h₁, P, rP, ha, hP⟩ := exists_limit_point f₀ U ψ a β φ hsq ρ hρ
  have HP : pt W₁ P ≫ f₀ = Spec.map (CommRingCat.ofHom
      ((algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ))) := by rw [pt_comp, hP]
  haveI := isLocalRing_ult U (V := V)
  obtain ⟨S, hSf, -, hS2⟩ := exists_finite_affine_cover (⊤ : X.Opens) (by simpa using isCompact_univ)
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ w ∈ S ×ˢ S, ∃ (p : Γ(X, w.1.1) →+* V i)
      (q : Γ(X, w.2.1) →+* V i) (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt w.1 p ∧ l₂ ≫ pullback.fst _ _ = pt w.2 q := by
    filter_upwards [H] with i ⟨l₁, l₂, hne, a1, a2, s1, s2⟩
    obtain ⟨A₁, hA₁, x₁⟩ := hS2 ((l₁ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨A₂, hA₂, x₂⟩ := hS2 ((l₂ ≫ pullback.fst _ _)
      (IsLocalRing.closedPoint (V i) : PrimeSpectrum (V i))) trivial
    obtain ⟨p, hp⟩ := exists_pt_of_isLocalRing _ A₁ x₁
    obtain ⟨q, hq⟩ := exists_pt_of_isLocalRing _ A₂ x₂
    exact ⟨(A₁, A₂), ⟨hA₁, hA₂⟩, p, q, l₁, l₂, hne, a1, a2, s1, s2, hp, hq⟩
  obtain ⟨⟨W₂, W₃⟩, -, hQ⟩ := exists_of_finite U (hSf.prod hSf) hQ
  dsimp only at hQ
  obtain ⟨h₂, hh₂⟩ := exists_family U hQ
  have hQ' : ∀ᶠ i in (U : Filter ι), ∃ (q : Γ(X, W₃.1) →+* V i) (p : Γ(X, W₂.1) →+* V i)
      (l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))), ⇑p = h₂ i ∧ l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₁ ≫ pullback.fst _ _ = pt W₂ p ∧ l₂ ≫ pullback.fst _ _ = pt W₃ q := by
    filter_upwards [hh₂] with i ⟨p, hp, q, l₁, l₂, hne, a1, a2, s1, s2, f1, f2⟩
    exact ⟨q, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩
  obtain ⟨h₃, hh₃⟩ := exists_family U hQ'
  have ae₂ : IsAEHom U h₂ := by
    filter_upwards [hh₂] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have ae₃ : IsAEHom U h₃ := by
    filter_upwards [hh₃] with i ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have L₂ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₂ ae₂) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨p, t, l₁, hp, ht, f1, s1, a1, et⟩)
  have L₃ := limit_lift f₀ U ψ a β ρ hρ (rep_homOf U h₃ ae₃) rP (by
    filter_upwards [hh₃, ha] with i ⟨q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ ⟨t, ht, et⟩
    exact ⟨q, t, l₂, hq, ht, f2, s2, a2, et⟩)
  have E := (val_lift hpb hval ρ (pt W₁ P) HP).2 _ _ L₂.1 L₃.1 L₂.2 L₃.2
  have c := ae_pt_eq_of_pt_eq U hfp (rep_homOf U h₂ ae₂) (rep_homOf U h₃ ae₃) E
  obtain ⟨i, d, q, hq, p, l₁, l₂, hp, hne, a1, a2, s1, s2, f1, f2⟩ := (c.and hh₃).exists
  apply hne
  apply pullback.hom_ext
  · rw [f1, f2]
    exact d p q hp hq
  · rw [s1, s2]

theorem ae_unique_lift [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {ι : Type} (U : Ultrafilter ι) {T : ι → Type} [∀ i, CommRing (T i)] (ψ : ∀ i, R₀ →+* T i)
    (S : ∀ i, ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (ψ i)))))
    (β : ∀ i, T i →+* (S i).R) (hβ : ∀ i, (S i).i₂ = Spec.map (CommRingCat.ofHom (β i)))
    (ρ : R →+* Ult U (fun i => (S i).R))
    (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), Nonempty (Unique (S i).commSq.LiftStruct) := by
  have hsq : ∀ i, (S i).i₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      ((algebraMap (S i).R (S i).K).comp (β i))) := fun i => by
    rw [(S i).commSq.w, hβ, spec_comp]
  have E := ae_exists_lift f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
    (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ
  have Uq : ∀ᶠ i in (U : Filter ι), Subsingleton (S i).commSq.LiftStruct := by
    by_contra hc
    have hc' := Ultrafilter.eventually_not.2 hc
    refine not_ae_two_lifts f₀ U (V := fun i => (S i).R) (K := fun i => (S i).K) ψ
      (fun i => (S i).i₁) β hfp hpb hval hsq ρ hρ ?_
    filter_upwards [hc'] with i hi
    obtain ⟨l₁, l₂, hne⟩ := (not_subsingleton_iff_nontrivial.1 hi).exists_pair_ne
    exact ⟨l₁.l, l₂.l, fun h => hne (CommSq.LiftStruct.ext h), l₁.fac_left, l₂.fac_left,
      l₁.fac_right.trans (hβ i), l₂.fac_right.trans (hβ i)⟩
  filter_upwards [E, Uq] with i ⟨l, h1, h2⟩ hs
  have hn : Nonempty (S i).commSq.LiftStruct := ⟨⟨l, h1, h2.trans (hβ i).symm⟩⟩
  exact unique_iff_subsingleton_and_nonempty _ |>.2 ⟨hs, hn⟩

omit [CommRing R] in
lemma fp_sections [LocallyOfFinitePresentation f₀] [Algebra.FiniteType ℤ R₀] (W : X.affineOpens) :
    Algebra.FinitePresentation ℤ Γ(X, W.1) := by
  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (baseHom f₀ W))) := by
    rw [← fromSpec_comp]; infer_instance
  have h2 : (baseHom f₀ W).FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h1
  have h3 : Algebra.FinitePresentation ℤ R₀ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have h4 := h2.comp ((RingHom.finitePresentation_algebraMap).2 h3)
  rw [← RingHom.finitePresentation_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

end Core

def lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) (S₀ : Set R₀) (F : Finset R) :
    Subalgebra ℤ R :=
  Algebra.adjoin ℤ (φ '' S₀ ∪ (F : Set R))

lemma map_mem_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) (r : R₀) : φ r ∈ lvl φ S₀ F := by
  have hr : r ∈ Algebra.adjoin ℤ S₀ := hS₀ ▸ Algebra.mem_top
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  | algebraMap z => simpa using (lvl φ S₀ F).algebraMap_mem z
  | add x y _ _ hx hy => simpa using (lvl φ S₀ F).add_mem hx hy
  | mul x y _ _ hx hy => simpa using (lvl φ S₀ F).mul_mem hx hy

lemma finiteType_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : S₀.Finite) (F : Finset R) : Algebra.FiniteType ℤ (lvl φ S₀ F) :=
  (Subalgebra.fg_iff_finiteType _).1
    (Subalgebra.fg_def.2 ⟨_, (hS₀.image φ).union F.finite_toSet, rfl⟩)

def lvlHom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) : R₀ →+* lvl φ S₀ F :=
  φ.codRestrict (lvl φ S₀ F) (map_mem_lvl φ hS₀ F)

lemma exists_limit_hom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) {V : Finset R → Type} [∀ F, CommRing (V F)]
    (β : ∀ F, lvl φ S₀ F →+* V F) (U : Ultrafilter (Finset R))
    (hU : (U : Filter (Finset R)) ≤ atTop) :
    ∃ ρ : R →+* Ult U V, ∀ r, ρ (φ r) = mk U (fun F => β F (lvlHom φ hS₀ F r)) := by
  classical
  have hmem : ∀ r : R, ∀ᶠ F in (U : Filter (Finset R)), r ∈ lvl φ S₀ F := by
    intro r
    filter_upwards [hU (eventually_ge_atTop ({r} : Finset R))] with F hF
    exact Algebra.subset_adjoin (Or.inr (by simpa using hF))
  let h : ∀ F, R → V F := fun F r => if hr : r ∈ lvl φ S₀ F then β F ⟨r, hr⟩ else 0
  have hv : ∀ (F : Finset R) (r : R) (hr : r ∈ lvl φ S₀ F), h F r = β F ⟨r, hr⟩ :=
    fun F r hr => dif_pos hr
  refine ⟨ofFamily U h ?_ ?_ ?_, fun r => ?_⟩
  · filter_upwards [hmem 1] with F h1
    rw [hv F 1 h1]
    exact map_one (β F)
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a + b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_add]
    rfl
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a * b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_mul]
    rfl
  · refine (ofFamily_apply U h _ _ _ (φ r)).trans ((mk_eq_mk_iff U).2 ?_)
    refine Filter.Eventually.of_forall fun F => ?_
    rw [hv F _ (map_mem_lvl φ hS₀ F r)]
    rfl

end GlobalTheory.CompanionTheory.Ultra

namespace GlobalTheory.CompanionTheory.SpreadingModels

open GlobalTheory.CompanionTheory.Ultra

theorem properSpreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hft, hlfp, hqc, hqs, hpb⟩ hprop
  have hprop' : IsProper f := hprop
  have hval : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hprop'
    exact hprop'.1.1.1
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  haveI : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  have hfp := fp_sections f₀ (R₀ := R₀)
  obtain ⟨S₀, hS₀⟩ := hft.out
  have hS₀f : (S₀ : Set R₀).Finite := S₀.finite_toSet
  suffices h : ∃ F, IsProper (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (lvlHom φ hS₀ F)))) by
    obtain ⟨F, hF⟩ := h
    exact ⟨lvl φ S₀ F, inferInstance, lvlHom φ hS₀ F, (lvl φ S₀ F).val.toRingHom, rfl,
      finiteType_lvl φ hS₀f F, hF⟩
  by_contra hcon
  push_neg at hcon
  have hS : ∀ F, ∃ S : ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom
      (lvlHom φ hS₀ F)))), ¬ Nonempty (Unique S.commSq.LiftStruct) := by
    intro F
    by_contra h
    push_neg at h
    apply hcon F
    rw [IsProper.eq_valuativeCriterion]
    exact ⟨⟨⟨h, inferInstance⟩, inferInstance⟩, inferInstance⟩
  choose S hS using hS
  let U : Ultrafilter (Finset R) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset R)) ≤ atTop := Ultrafilter.of_le _
  let β : ∀ F, lvl φ S₀ F →+* (S F).R := fun F => (Spec.preimage (S F).i₂).hom
  have hβ : ∀ F, (S F).i₂ = Spec.map (CommRingCat.ofHom (β F)) := fun F => by simp [β]
  obtain ⟨ρ, hρ⟩ := exists_limit_hom φ hS₀ (V := fun F => (S F).R) β U hU
  obtain ⟨F, hF⟩ := (ae_unique_lift f₀ hfp hpb hval U (lvlHom φ hS₀) S β hβ ρ hρ).exists
  exact hS F hF

end GlobalTheory.CompanionTheory.SpreadingModels
