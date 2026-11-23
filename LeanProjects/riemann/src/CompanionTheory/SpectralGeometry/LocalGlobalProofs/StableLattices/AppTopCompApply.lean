import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.ObstructionLift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace GlobalTheory.CompanionTheory.FlatHilbert90

def toLine (T : Scheme.{0}) (s : Γ(T, ⊤)) : T ⟶ Spec (.of (Polynomial ℤ)) :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) s))

lemma comp_toLine {T T' : Scheme.{0}} (g : T' ⟶ T) (s : Γ(T, ⊤)) :
    g ≫ toLine T s = toLine T' (g.appTop s) := by
  unfold toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext p
  · simp
  · simp

lemma toLine_appTop (T : Scheme.{0}) (s : Γ(T, ⊤)) :
    (toLine T s).appTop ((Scheme.ΓSpecIso (.of (Polynomial ℤ))).inv Polynomial.X) = s := by
  have h : (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom Γ(T, ⊤)) s))).appTop
      ((Scheme.ΓSpecIso (.of (Polynomial ℤ))).inv Polynomial.X) = (Scheme.ΓSpecIso Γ(T, ⊤)).inv s := by
    have h' := congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom Γ(T, ⊤)) s))) Polynomial.X)
    refine h'.symm.trans ?_
    change (Scheme.ΓSpecIso _).inv (Polynomial.eval₂RingHom (Int.castRingHom Γ(T, ⊤)) s Polynomial.X) = _
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  unfold toLine
  rw [Scheme.Hom.comp_appTop]
  change T.toSpecΓ.appTop ((Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom Γ(T, ⊤)) s))).appTop
      ((Scheme.ΓSpecIso (.of (Polynomial ℤ))).inv Polynomial.X)) = s
  rw [h, Scheme.toSpecΓ_appTop]
  simp

lemma appTop_injective {W Z : Scheme.{0}} (q : W ⟶ Z) [Epi q] (s s' : Γ(Z, ⊤))
    (h : q.appTop s = q.appTop s') : s = s' := by
  have : toLine Z s = toLine Z s' := by
    rw [← cancel_epi q, comp_toLine, comp_toLine, h]
  rw [← toLine_appTop Z s, this, toLine_appTop]

lemma exists_descent {W Z : Scheme.{0}} (q : W ⟶ Z) [EffectiveEpi q] (v : Γ(W, ⊤))
    (h : ∀ (T : Scheme.{0}) (g₁ g₂ : T ⟶ W), g₁ ≫ q = g₂ ≫ q → g₁.appTop v = g₂.appTop v) :
    ∃ t : Γ(Z, ⊤), q.appTop t = v := by
  let e := EffectiveEpi.desc q (toLine W v) (fun {T} g₁ g₂ hg => by
    rw [comp_toLine, comp_toLine, h T g₁ g₂ hg])
  have he : q ≫ e = toLine W v := EffectiveEpi.fac q _ _
  refine ⟨e.appTop ((Scheme.ΓSpecIso (.of (Polynomial ℤ))).inv Polynomial.X), ?_⟩
  have := toLine_appTop W v
  rw [← he, Scheme.Hom.comp_appTop] at this
  simpa using this

section Alg

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

abbrev pr {C : Type} [CommRing C] [Algebra A C] (α β : B →ₐ[A] C) : B ⊗[A] B →ₐ[A] C :=
  Algebra.TensorProduct.lift α β (fun _ _ => .all _ _)

lemma exists_invariant [Module.Flat A B] (u w : B ⊗[A] B) (huw : u * w = 1)
    (hc : ∀ (C : Type) [CommRing C] [Algebra A C] (α β γ : B →ₐ[A] C),
      pr α γ u = pr α β u * pr β γ u)
    (q : Ideal B) (hq : q ≠ ⊤) :
    ∃ n : B, n ∉ q ∧ n ⊗ₜ[A] (1 : B) = u * ((1 : B) ⊗ₜ[A] n) := by
  classical
  let d : B →ₗ[A] B ⊗[A] B :=
    (TensorProduct.mk A B B).flip 1 - (LinearMap.mulLeft A u) ∘ₗ (TensorProduct.mk A B B 1)
  have hd : ∀ b, d b = b ⊗ₜ[A] (1 : B) - u * ((1 : B) ⊗ₜ[A] b) := fun b => rfl
  have hex : Function.Exact (LinearMap.ker d).subtype d := LinearMap.exact_subtype_ker_map d
  have hex' := Module.Flat.lTensor_exact B hex

  let e₁ : B →ₐ[A] B ⊗[A] (B ⊗[A] B) := Algebra.TensorProduct.includeLeft
  let e₂ : B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let e₃ : B →ₐ[A] B ⊗[A] (B ⊗[A] B) := (Algebra.TensorProduct.includeRight).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  have h23 : ∀ z : B ⊗[A] B, pr e₂ e₃ z = (1 : B) ⊗ₜ[A] z := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp [ha, hb, TensorProduct.tmul_add]
    | tmul a b => simp [e₂, e₃, Algebra.TensorProduct.tmul_mul_tmul]
  have hl : ∀ z : B ⊗[A] B, d.lTensor B z = pr e₁ e₂ z - pr e₂ e₃ u * pr e₁ e₃ z := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, mul_add]; ring
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, hd, TensorProduct.tmul_sub, h23]
      congr 1
      · simp [e₁, e₂, pr, Algebra.TensorProduct.tmul_mul_tmul]
      · simp [e₁, e₃, pr, Algebra.TensorProduct.tmul_mul_tmul]
  have hcu := hc _ e₁ e₂ e₃
  have hw : d.lTensor B w = 0 := by
    rw [hl]
    have h12 : pr e₁ e₂ u * pr e₁ e₂ w = 1 := by rw [← map_mul, huw, map_one]
    have h13 : pr e₁ e₃ u * pr e₁ e₃ w = 1 := by rw [← map_mul, huw, map_one]
    rw [hcu] at h13
    linear_combination (- pr e₁ e₂ w) * h13 + (pr e₂ e₃ u * pr e₁ e₃ w) * h12
  obtain ⟨y, hy⟩ := (hex' w).1 hw

  let m : B ⊗[A] B →ₐ[A] B := pr (AlgHom.id A B) (AlgHom.id A B)
  have hmu : m u = 1 := by
    have h1 := hc B (AlgHom.id A B) (AlgHom.id A B) (AlgHom.id A B)
    have h2 : m u * m w = 1 := by rw [← map_mul, huw, map_one]
    change m u = m u * m u at h1
    linear_combination (- m w) * h1 - (m u - 1) * h2
  have hmw : m w = 1 := by
    have h2 : m u * m w = 1 := by rw [← map_mul, huw, map_one]
    rwa [hmu, one_mul] at h2
  have hspan : ∀ z : B ⊗[A] (LinearMap.ker d),
      m ((LinearMap.ker d).subtype.lTensor B z) ∈ Ideal.span ((LinearMap.ker d : Submodule A B) : Set B) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simpa using Ideal.add_mem _ ha hb
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, m]
      simpa using Ideal.mul_mem_left _ a (Ideal.subset_span b.2)
  have h1 : (1 : B) ∈ Ideal.span ((LinearMap.ker d : Submodule A B) : Set B) := by
    rw [← hmw, ← hy]; exact hspan y
  have : ¬ Ideal.span ((LinearMap.ker d : Submodule A B) : Set B) ≤ q := fun hle =>
    hq ((Ideal.eq_top_iff_one q).2 (hle h1))
  rw [Ideal.span_le, Set.not_subset] at this
  obtain ⟨n, hn, hnq⟩ := this
  refine ⟨n, hnq, ?_⟩
  have : d n = 0 := hn
  rw [hd] at this
  exact sub_eq_zero.1 this

end Alg

section Extend

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (u : Γ(pullback f f, ⊤))

lemma appTop_comp_apply {T₁ T₂ T₃ : Scheme.{0}} (g : T₁ ⟶ T₂) (h : T₂ ⟶ T₃) (s : Γ(T₃, ⊤)) :
    (g ≫ h).appTop s = g.appTop (h.appTop s) := by
  rw [Scheme.Hom.comp_appTop]; rfl

lemma lift_appTop_comp {W W' : Scheme.{0}} (s : W' ⟶ W) (a b : W ⟶ X) (h : a ≫ f = b ≫ f)
    (h' : (s ≫ a) ≫ f = (s ≫ b) ≫ f) :
    (pullback.lift (s ≫ a) (s ≫ b) h').appTop u = s.appTop ((pullback.lift a b h).appTop u) := by
  have : pullback.lift (s ≫ a) (s ≫ b) h' = s ≫ pullback.lift a b h := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [this, appTop_comp_apply]

lemma lift_congr {W : Scheme.{0}} {a a' b b' : W ⟶ X} (ha : a = a') (hb : b = b')
    (h : a ≫ f = b ≫ f) (h' : a' ≫ f = b' ≫ f) :
    (pullback.lift a b h).appTop u = (pullback.lift a' b' h').appTop u := by
  subst ha hb; rfl

lemma effectiveEpi_fst {V T : Scheme.{0}} (G : V ⟶ Y) [Flat G] [LocallyOfFinitePresentation G]
    (c : T ⟶ Y) (h : ∀ w : T, c w ∈ Set.range G) : EffectiveEpi (pullback.fst c G) := by
  have : Surjective (pullback.fst c G) := ⟨fun w => by
    obtain ⟨v, hv⟩ := h w
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := G) w v hv.symm
    exact ⟨z, hz⟩⟩
  infer_instance

theorem extend {Z V : Scheme.{0}} (ι : Z ⟶ X) (e : V ⟶ X) [Flat (e ≫ f)]
    [LocallyOfFinitePresentation (e ≫ f)]
    (hZ : ∀ z : Z, f (ι z) ∈ Set.range (e ≫ f)) (hu : IsUnit u)
    (hc : ∀ (W : Scheme.{0}) (a b c : W ⟶ X) (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u)
    (t₀ : Γ(V, ⊤)) (ht₀ : IsUnit t₀)
    (P : ∀ (W : Scheme.{0}) (a b : W ⟶ V) (h : (a ≫ e) ≫ f = (b ≫ e) ≫ f),
      a.appTop t₀ = (pullback.lift (a ≫ e) (b ≫ e) h).appTop u * b.appTop t₀) :
    ∃ t : Γ(Z, ⊤), IsUnit t ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : (a ≫ ι) ≫ f = (b ≫ ι) ≫ f),
      a.appTop t = (pullback.lift (a ≫ ι) (b ≫ ι) hab).appTop u * b.appTop t := by
  let q : pullback (ι ≫ f) (e ≫ f) ⟶ Z := pullback.fst _ _
  let p : pullback (ι ≫ f) (e ≫ f) ⟶ V := pullback.snd _ _
  have hqp : (q ≫ ι) ≫ f = (p ≫ e) ≫ f := by
    simpa [q, p] using pullback.condition (f := ι ≫ f) (g := e ≫ f)
  have : EffectiveEpi q := effectiveEpi_fst (e ≫ f) (ι ≫ f) (fun z => by simpa using hZ z)
  let v : Γ(pullback (ι ≫ f) (e ≫ f), ⊤) :=
    (pullback.lift (q ≫ ι) (p ≫ e) hqp).appTop u * p.appTop t₀
  have hvf : ∀ {T : Scheme.{0}} (g : T ⟶ pullback (ι ≫ f) (e ≫ f))
      (h : ((g ≫ q) ≫ ι) ≫ f = ((g ≫ p) ≫ e) ≫ f),
      g.appTop v = (pullback.lift ((g ≫ q) ≫ ι) ((g ≫ p) ≫ e) h).appTop u * (g ≫ p).appTop t₀ := by
    intro T g h
    simp only [v, map_mul]
    rw [← lift_appTop_comp f u g _ _ hqp (by simpa using h), appTop_comp_apply g p]
    congr 1
  have hqp' : q ≫ ι ≫ f = p ≫ e ≫ f := by simpa using hqp
  have hv : ∀ (T : Scheme.{0}) (g₁ g₂ : T ⟶ pullback (ι ≫ f) (e ≫ f)), g₁ ≫ q = g₂ ≫ q →
      g₁.appTop v = g₂.appTop v := by
    intro T g₁ g₂ hg
    have h₁ : ((g₁ ≫ q) ≫ ι) ≫ f = ((g₁ ≫ p) ≫ e) ≫ f := by simp only [Category.assoc]; rw [hqp']
    have h₂ : ((g₂ ≫ q) ≫ ι) ≫ f = ((g₂ ≫ p) ≫ e) ≫ f := by simp only [Category.assoc]; rw [hqp']
    have hb : ((g₁ ≫ p) ≫ e) ≫ f = ((g₂ ≫ p) ≫ e) ≫ f := by rw [← h₁, ← h₂, hg]
    rw [hvf g₁ h₁, hvf g₂ h₂, P T _ _ hb, ← mul_assoc, ← hc T _ _ _ h₁ hb]
    congr 1
    exact lift_congr f u (by rw [hg]) rfl _ _
  obtain ⟨t, ht⟩ := exists_descent q v hv
  have hvu : IsUnit v := (hu.map (pullback.lift (q ≫ ι) (p ≫ e) hqp).appTop.hom).mul
    (ht₀.map p.appTop.hom)
  obtain ⟨v', hv'⟩ := hvu.exists_right_inv
  have hv'' : ∀ (T : Scheme.{0}) (g₁ g₂ : T ⟶ pullback (ι ≫ f) (e ≫ f)), g₁ ≫ q = g₂ ≫ q →
      g₁.appTop v' = g₂.appTop v' := by
    intro T g₁ g₂ hg
    have h0 := hv T g₁ g₂ hg
    have h1 : g₁.appTop v * g₁.appTop v' = 1 := by rw [← map_mul, hv', map_one]
    have h2 : g₂.appTop v * g₂.appTop v' = 1 := by rw [← map_mul, hv', map_one]
    rw [h0] at h1
    linear_combination (g₂.appTop v') * h1 - (g₁.appTop v') * h2
  obtain ⟨t', ht'⟩ := exists_descent q v' hv''
  have htt : t * t' = 1 := by
    apply appTop_injective q
    rw [map_mul, ht, ht', hv', map_one]
  refine ⟨t, IsUnit.of_mul_eq_one _ htt, ?_⟩
  have key : ∀ {T : Scheme.{0}} (s : T ⟶ Z) (r : T ⟶ V) (h : s ≫ ι ≫ f = r ≫ e ≫ f)
      (h' : (s ≫ ι) ≫ f = (r ≫ e) ≫ f),
      s.appTop t = (pullback.lift (s ≫ ι) (r ≫ e) h').appTop u * r.appTop t₀ := by
    intro T s r h h'
    let g : T ⟶ pullback (ι ≫ f) (e ≫ f) := pullback.lift s r h
    have hgq : g ≫ q = s := pullback.lift_fst _ _ _
    have hgp : g ≫ p = r := pullback.lift_snd _ _ _
    have h'' : ((g ≫ q) ≫ ι) ≫ f = ((g ≫ p) ≫ e) ≫ f := by rw [hgq, hgp]; exact h'
    have h3 : s.appTop t = g.appTop v := by rw [← ht, ← appTop_comp_apply, hgq]
    have h4 : (g ≫ p).appTop t₀ = r.appTop t₀ := by rw [hgp]
    rw [h3, hvf g h'', h4]
    congr 1
    exact lift_congr f u (by rw [hgq]) (by rw [hgp]) _ _
  intro W a b hab
  let π : pullback ((a ≫ ι) ≫ f) (e ≫ f) ⟶ W := pullback.fst _ _
  let r : pullback ((a ≫ ι) ≫ f) (e ≫ f) ⟶ V := pullback.snd _ _
  have hπ : EffectiveEpi π := effectiveEpi_fst (e ≫ f) ((a ≫ ι) ≫ f) (fun w => by simpa using hZ (a w))
  have hr : π ≫ (a ≫ ι) ≫ f = r ≫ e ≫ f := pullback.condition
  have ha : (π ≫ a) ≫ ι ≫ f = r ≫ e ≫ f := by simpa using hr
  have hb : (π ≫ b) ≫ ι ≫ f = r ≫ e ≫ f := by
    rw [← hr]; simp only [Category.assoc]; simpa using congr(π ≫ $hab.symm)
  have ha' : ((π ≫ a) ≫ ι) ≫ f = (r ≫ e) ≫ f := by simpa using ha
  have hb' : ((π ≫ b) ≫ ι) ≫ f = (r ≫ e) ≫ f := by simpa using hb
  have hab' : ((π ≫ a) ≫ ι) ≫ f = ((π ≫ b) ≫ ι) ≫ f := ha'.trans hb'.symm
  apply appTop_injective π
  rw [map_mul, ← appTop_comp_apply π a, ← appTop_comp_apply π b, key _ r ha ha', key _ r hb hb']
  have h₃ : π.appTop ((pullback.lift (a ≫ ι) (b ≫ ι) hab).appTop u) =
      (pullback.lift ((π ≫ a) ≫ ι) ((π ≫ b) ≫ ι) hab').appTop u := by
    rw [← lift_appTop_comp f u π (a ≫ ι) (b ≫ ι) hab (by simpa using hab')]
    exact lift_congr f u (by simp) (by simp) _ _
  rw [h₃, ← mul_assoc, ← hc _ _ _ _ hab' hb']

end Extend

section Local

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (u : Γ(pullback f f, ⊤))

lemma spec_appTop {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom ψ)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of S)).inv (ψ r) :=
  (congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)) r)).symm

theorem local_unit {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (i : Spec (.of B) ⟶ X) (j : Spec (.of A) ⟶ Y) [Mono j] [IsOpenImmersion i]
    (hij : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j = i ≫ f)
    (hu : IsUnit u)
    (hc : ∀ (W : Scheme.{0}) (a b c : W ⟶ X) (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u)
    (x : PrimeSpectrum B) :
    ∃ (V : Scheme.{0}) (e : V ⟶ X) (_ : IsOpenImmersion e) (t₀ : Γ(V, ⊤)),
      i x ∈ Set.range e ∧ IsUnit t₀ ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ V) (h : (a ≫ e) ≫ f = (b ≫ e) ≫ f),
        a.appTop t₀ = (pullback.lift (a ≫ e) (b ≫ e) h).appTop u * b.appTop t₀ := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let sl : Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let sr : Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)
  have hsl : (pullbackSpecIso A B B).hom ≫ sl = pullback.fst _ _ := pullbackSpecIso_hom_fst A B B
  have hsr : (pullbackSpecIso A B B).hom ≫ sr = pullback.snd _ _ := pullbackSpecIso_hom_snd A B B
  have hslr : sl ≫ g = sr ≫ g := by
    rw [← cancel_epi (pullbackSpecIso A B B).hom, reassoc_of% hsl, reassoc_of% hsr]
    exact pullback.condition
  have hij' : g ≫ j = i ≫ f := hij
  have hρ : (sl ≫ i) ≫ f = (sr ≫ i) ≫ f := by
    simp only [Category.assoc]
    rw [← hij', reassoc_of% hslr]
  let ρ := pullback.lift (sl ≫ i) (sr ≫ i) hρ
  have hF : ∀ {W : Scheme.{0}} (c : W ⟶ Spec (.of (B ⊗[A] B))) (a b : W ⟶ X) (h : a ≫ f = b ≫ f),
      c ≫ sl ≫ i = a → c ≫ sr ≫ i = b → pullback.lift a b h = c ≫ ρ := by
    intro W c a b h ha hb
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hb]
  let uB : B ⊗[A] B := (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom (ρ.appTop u)
  have huB : ρ.appTop u = (Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv uB := by
    simp [uB]
  have hBu : IsUnit uB := (hu.map ρ.appTop.hom).map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom
  obtain ⟨w, hw⟩ := hBu.exists_right_inv
  have hcB : ∀ (C : Type) [CommRing C] [Algebra A C] (α β γ : B →ₐ[A] C),
      pr α γ uB = pr α β uB * pr β γ uB := by
    intro C _ _ α β γ
    have hαg : ∀ α : B →ₐ[A] C, Spec.map (CommRingCat.ofHom α.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
      intro α
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact α.comp_algebraMap
    have hf : ∀ α β : B →ₐ[A] C, (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i) ≫ f =
        (Spec.map (CommRingCat.ofHom β.toRingHom) ≫ i) ≫ f := by
      intro α β
      simp only [Category.assoc]
      rw [← hij', reassoc_of% (hαg α), reassoc_of% (hαg β)]
    have L1 : ∀ (α β : B →ₐ[A] C) (h),
        (pullback.lift (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i)
          (Spec.map (CommRingCat.ofHom β.toRingHom) ≫ i) h).appTop u =
        (Scheme.ΓSpecIso (.of C)).inv (pr α β uB) := by
      intro α β h
      rw [hF (Spec.map (CommRingCat.ofHom (pr α β).toRingHom)) _ _ h, appTop_comp_apply, huB, spec_appTop]
      · rfl
      · rw [← Category.assoc]
        congr 1
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext b
        simp
      · rw [← Category.assoc]
        congr 1
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext b
        simp
    have := hc _ _ _ _ (hf α β) (hf β γ)
    rw [L1, L1, L1, ← map_mul] at this
    have h2 := congr((Scheme.ΓSpecIso (.of C)).hom $this)
    simpa using h2
  obtain ⟨n, hnx, hn⟩ := exists_invariant uB w hw hcB x.asIdeal x.isPrime.ne_top
  let l : B →+* Localization.Away n := algebraMap B (Localization.Away n)
  let sn := Spec.map (CommRingCat.ofHom l)
  have : IsOpenImmersion sn := IsOpenImmersion.of_isLocalization n
  let t₀ : Γ(Spec (.of (Localization.Away n)), ⊤) := (Scheme.ΓSpecIso (.of (Localization.Away n))).inv (l n)
  have ht : sn.appTop ((Scheme.ΓSpecIso (.of B)).inv n) = t₀ := spec_appTop l n
  refine ⟨_, sn ≫ i, inferInstance, t₀, ?_, ?_, ?_⟩
  · have hp : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away n))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away n) n]
      exact hnx
    obtain ⟨z, hz⟩ := hp
    refine ⟨z, ?_⟩
    have hz' : sn z = x := hz
    change i (sn z) = i x
    rw [hz']
  · exact (IsLocalization.Away.algebraMap_isUnit n).map
      (Scheme.ΓSpecIso (.of (Localization.Away n))).inv.hom
  · intro W a b h
    have hab' : (a ≫ sn) ≫ g = (b ≫ sn) ≫ g := by
      rw [← cancel_mono j]
      simp only [Category.assoc]
      rw [hij']
      simpa using h
    let c := pullback.lift (a ≫ sn) (b ≫ sn) hab' ≫ (pullbackSpecIso A B B).hom
    have hca : c ≫ sl = a ≫ sn := by
      change (_ ≫ _) ≫ sl = _
      rw [Category.assoc, hsl, pullback.lift_fst]
    have hcb : c ≫ sr = b ≫ sn := by
      change (_ ≫ _) ≫ sr = _
      rw [Category.assoc, hsr, pullback.lift_snd]
    have hta : a.appTop t₀ = c.appTop ((Scheme.ΓSpecIso _).inv (n ⊗ₜ[A] (1 : B))) := by
      rw [← ht, ← appTop_comp_apply, ← hca, appTop_comp_apply, spec_appTop]
      rfl
    have htb : b.appTop t₀ = c.appTop ((Scheme.ΓSpecIso _).inv ((1 : B) ⊗ₜ[A] n)) := by
      rw [← ht, ← appTop_comp_apply, ← hcb, appTop_comp_apply, spec_appTop]
      rfl
    rw [hta, htb, hF c _ _ h (by rw [reassoc_of% hca])
      (by rw [reassoc_of% hcb]), appTop_comp_apply c ρ, huB, ← map_mul, ← map_mul, hn]

end Local

theorem h90 : CompanionTheory.ObstructionTrivialLocus.H90 := by
  intro X Y f hfl hlfp hsurj u hu hc y
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f x) trivial
  obtain ⟨O, hO, hxO, hOV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ V) (x := x) hxV
  have hle : O ≤ f ⁻¹ᵁ V := hOV
  letI := (f.appLE V O hle).hom.toAlgebra
  have hfl' : Module.Flat Γ(Y, V) Γ(X, O) := f.flat_appLE hV hO hle
  have hij := IsAffineOpen.SpecMap_appLE_fromSpec f hV hO hle
  obtain ⟨V', e, _, t₀, hx, ht₀, P⟩ := local_unit f u (A := Γ(Y, V)) (B := Γ(X, O)) hO.fromSpec
    hV.fromSpec hij hu hc (hO.primeIdealOf ⟨x, hxO⟩)
  have hx' : x ∈ Set.range e := by
    have := hO.fromSpec_primeIdealOf ⟨x, hxO⟩
    rwa [this] at hx
  let U : Y.Opens := ⟨Set.range (e ≫ f), (e ≫ f).isOpenMap.isOpen_range⟩
  obtain ⟨z, rfl⟩ := hx'
  refine ⟨U, ⟨z, by simp⟩, ?_⟩
  exact extend f u (f ⁻¹ᵁ U).ι e (fun z => z.2) hu hc t₀ ht₀ P

end GlobalTheory.CompanionTheory.FlatHilbert90
