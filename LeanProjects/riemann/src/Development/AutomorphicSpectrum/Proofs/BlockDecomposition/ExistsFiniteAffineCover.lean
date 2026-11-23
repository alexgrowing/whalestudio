import Mathlib

set_option autoImplicit false

noncomputable section

open Filter

namespace GlobalTheory.CompanionTheory.Ultra

variable {ι : Type} (U : Ultrafilter ι)

section Ring

variable (A : ι → Type) [∀ i, CommRing (A i)]

def nullIdeal : Ideal (∀ i, A i) where
  carrier := {a | ∀ᶠ i in (U : Filter ι), a i = 0}
  add_mem' := by
    intro a b ha hb
    filter_upwards [ha, hb] with i h1 h2
    simp [h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    filter_upwards [ha] with i h1
    simp [h1]

abbrev Ult : Type := (∀ i, A i) ⧸ nullIdeal U A

variable {A}

def mk : (∀ i, A i) →+* Ult U A := Ideal.Quotient.mk _

lemma mk_surjective : Function.Surjective (mk U (A := A)) := Ideal.Quotient.mk_surjective

lemma mk_eq_mk_iff {a b : ∀ i, A i} : mk U a = mk U b ↔ ∀ᶠ i in (U : Filter ι), a i = b i := by
  unfold mk
  rw [Ideal.Quotient.eq]
  change (∀ᶠ i in (U : Filter ι), (a - b) i = 0) ↔ _
  simp [sub_eq_zero]

lemma mk_eq_zero_iff {a : ∀ i, A i} : mk U a = 0 ↔ ∀ᶠ i in (U : Filter ι), a i = 0 := by
  rw [← map_zero (mk U), mk_eq_mk_iff]; rfl

lemma nullIdeal_isPrime [∀ i, IsDomain (A i)] : (nullIdeal U A).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    obtain ⟨i, hi⟩ := Filter.Eventually.exists (show ∀ᶠ i in (U : Filter ι), (1 : ∀ i, A i) i = 0 from h)
    exact one_ne_zero hi
  · intro a b h
    have h' : ∀ᶠ i in (U : Filter ι), a i = 0 ∨ b i = 0 := by
      filter_upwards [show ∀ᶠ i in (U : Filter ι), (a * b) i = 0 from h] with i hi
      simpa using hi
    exact Ultrafilter.eventually_or.1 h'

instance [∀ i, IsDomain (A i)] : IsDomain (Ult U A) :=
  haveI := nullIdeal_isPrime U (A := A)
  Ideal.Quotient.isDomain _

end Ring

section Field

variable (K : ι → Type) [∀ i, Field (K i)]

lemma isField_ult : IsField (Ult U K) := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := mk_surjective U x
  refine ⟨mk U (fun i => (a i)⁻¹), ?_⟩
  rw [← map_mul, ← map_one (mk U), mk_eq_mk_iff]
  have : ∀ᶠ i in (U : Filter ι), a i ≠ 0 := by
    have h := (not_congr (mk_eq_zero_iff U)).1 hx
    exact Ultrafilter.eventually_not.2 h
  filter_upwards [this] with i hi
  simp [hi]

instance : Field (Ult U K) := (isField_ult U K).toField

end Field

section Val

variable (V : ι → Type) [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)]

instance : ValuationRing (Ult U V) := by
  refine ValuationRing.iff_dvd_total.2 ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := mk_surjective U x
  obtain ⟨b, rfl⟩ := mk_surjective U y
  have key : ∀ (a b : ∀ i, V i), (∀ᶠ i in (U : Filter ι), a i ∣ b i) → mk U a ∣ mk U b := by
    intro a b h
    have h' : ∀ i, ∃ c, a i ∣ b i → b i = a i * c := by
      intro i
      by_cases hi : a i ∣ b i
      · obtain ⟨c, hc⟩ := hi
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose c hc using h'
    refine ⟨mk U c, ?_⟩
    rw [← map_mul, mk_eq_mk_iff]
    filter_upwards [h] with i hi
    exact hc i hi
  have h : ∀ᶠ i in (U : Filter ι), a i ∣ b i ∨ b i ∣ a i :=
    Filter.Eventually.of_forall fun i => ValuationRing.dvd_total (a i) (b i)
  rcases Ultrafilter.eventually_or.1 h with h | h
  · exact Or.inl (key a b h)
  · exact Or.inr (key b a h)

end Val

section Map

variable {A B : ι → Type} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]

def map (g : ∀ i, A i →+* B i) : Ult U A →+* Ult U B :=
  Ideal.Quotient.lift _ ((mk U).comp (Pi.ringHom fun i => (g i).comp (Pi.evalRingHom A i))) (by
    intro a ha
    have ha' : ∀ᶠ i in (U : Filter ι), a i = 0 := ha
    change mk U _ = 0
    rw [mk_eq_zero_iff]
    filter_upwards [ha'] with i hi
    change g i (a i) = 0
    rw [hi, map_zero])

end Map

section Frac

variable (V K : ι → Type) [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)]

instance : Algebra (Ult U V) (Ult U K) := (map U fun i => algebraMap (V i) (K i)).toAlgebra

lemma algebraMap_mk (a : ∀ i, V i) :
    algebraMap (Ult U V) (Ult U K) (mk U a) = mk U (fun i => algebraMap (V i) (K i) (a i)) := rfl

instance [∀ i, IsFractionRing (V i) (K i)] : IsFractionRing (Ult U V) (Ult U K) := by
  have hinj : Function.Injective (algebraMap (Ult U V) (Ult U K)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := mk_surjective U x
    rw [algebraMap_mk, mk_eq_zero_iff] at hx
    rw [mk_eq_zero_iff]
    filter_upwards [hx] with i hi
    exact (map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 hi
  haveI : FaithfulSMul (Ult U V) (Ult U K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field _ _ ?_
  intro z
  obtain ⟨k, rfl⟩ := mk_surjective U z
  have h : ∀ i, ∃ x y : V i, y ≠ 0 ∧ algebraMap (V i) (K i) x / algebraMap (V i) (K i) y = k i := by
    intro i
    obtain ⟨x, y, hy, e⟩ := IsFractionRing.div_surjective (A := V i) (k i)
    exact ⟨x, y, nonZeroDivisors.ne_zero hy, e⟩
  choose x y hy e using h
  have hy' : algebraMap (Ult U V) (Ult U K) (mk U y) ≠ 0 := by
    rw [algebraMap_mk]
    intro h0
    rw [mk_eq_zero_iff] at h0
    obtain ⟨i, hi⟩ := h0.exists
    exact hy i ((map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 hi)
  refine ⟨mk U x, mk U y, ?_⟩
  rw [eq_div_iff hy', algebraMap_mk, algebraMap_mk, ← map_mul, mk_eq_mk_iff]
  refine Filter.Eventually.of_forall fun i => ?_
  have : algebraMap (V i) (K i) (y i) ≠ 0 := fun h0 =>
    hy i ((map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 h0)
  simp only [Pi.mul_apply]
  rw [← e i]
  field_simp

end Frac

section Rep

variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]

def IsAEHom (h : ∀ i, B → A i) : Prop := ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, ⇑p = h i

def ofFamily (h : ∀ i, B → A i) (h1 : ∀ᶠ i in (U : Filter ι), h i 1 = 1)
    (hadd : ∀ a b, ∀ᶠ i in (U : Filter ι), h i (a + b) = h i a + h i b)
    (hmul : ∀ a b, ∀ᶠ i in (U : Filter ι), h i (a * b) = h i a * h i b) : B →+* Ult U A where
  toFun b := mk U (fun i => h i b)
  map_one' := by
    rw [← map_one (mk U), mk_eq_mk_iff]
    exact h1
  map_mul' a b := by
    rw [← map_mul, mk_eq_mk_iff]
    exact hmul a b
  map_zero' := by
    rw [mk_eq_zero_iff]
    filter_upwards [hadd 0 0] with i hi
    simpa using hi
  map_add' a b := by
    rw [← map_add, mk_eq_mk_iff]
    exact hadd a b

lemma ofFamily_apply (h : ∀ i, B → A i) (h1 hadd hmul) (b : B) :
    ofFamily U h h1 hadd hmul b = mk U (fun i => h i b) := rfl

def homOf (h : ∀ i, B → A i) (hh : IsAEHom U h) : B →+* Ult U A :=
  ofFamily U h
    (by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_one])
    (fun a b => by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_add])
    (fun a b => by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_mul])

lemma homOf_apply (h : ∀ i, B → A i) (hh : IsAEHom U h) (b : B) :
    homOf U h hh b = mk U (fun i => h i b) := rfl

def Rep (h : ∀ i, B → A i) (g : B →+* Ult U A) : Prop :=
  IsAEHom U h ∧ ∀ b, g b = mk U (fun i => h i b)

lemma rep_homOf (h : ∀ i, B → A i) (hh : IsAEHom U h) : Rep U h (homOf U h hh) :=
  ⟨hh, fun _ => rfl⟩

lemma exists_family {Q : ∀ i, (B →+* A i) → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, Q i p) :
    ∃ h : ∀ i, B → A i, ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, ⇑p = h i ∧ Q i p := by
  classical
  refine ⟨fun i => if hx : ∃ p : B →+* A i, Q i p then ⇑hx.choose else 0, ?_⟩
  filter_upwards [H] with i hi
  exact ⟨hi.choose, by simp [dif_pos hi], hi.choose_spec⟩

lemma ae_eq_of_fg [Algebra.FiniteType ℤ B] {h h' : ∀ i, B → A i} (hh : IsAEHom U h)
    (hh' : IsAEHom U h') (H : ∀ b, mk U (fun i => h i b) = mk U (fun i => h' i b)) :
    ∀ᶠ i in (U : Filter ι), h i = h' i := by
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  have h1 : ∀ᶠ i in (U : Filter ι), ∀ s ∈ S, h i s = h' i s :=
    (Filter.eventually_all_finset S).2 fun s _ => (mk_eq_mk_iff U).1 (H s)
  filter_upwards [h1, hh, hh'] with i hi ⟨p, hp⟩ ⟨q, hq⟩
  have : p.toIntAlgHom = q.toIntAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top hS ?_
    intro s hs
    have := hi s hs
    rw [← hp, ← hq] at this
    exact this
  rw [← hp, ← hq]
  ext b
  exact DFunLike.congr_fun this b

lemma exists_rep [Algebra.FinitePresentation ℤ B] (g : B →+* Ult U A) :
    ∃ h : ∀ i, B → A i, Rep U h g := by
  obtain ⟨n, π, hπ, hfg⟩ := (Algebra.FinitePresentation.out : ∃ (n : ℕ)
    (f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] B), Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG)
  choose c hc using fun k => mk_surjective U (g (π (MvPolynomial.X k)))
  let e : ∀ i, MvPolynomial (Fin n) ℤ →+* A i := fun i =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun k => c k i)
  have key : (mk U).comp (Pi.ringHom e) = g.comp π.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← hc k]
      congr 1
      ext i
      change e i (MvPolynomial.X k) = c k i
      simp [e]
  have key' : ∀ x, mk U (fun i => e i x) = g (π x) := fun x => RingHom.congr_fun key x
  obtain ⟨S, hS⟩ := hfg
  have h1 : ∀ᶠ i in (U : Filter ι), ∀ s ∈ S, e i s = 0 := by
    refine (Filter.eventually_all_finset S).2 fun s hs => ?_
    have hs' : s ∈ RingHom.ker π.toRingHom := hS ▸ Ideal.subset_span hs
    have := key' s
    rw [show π s = 0 from hs', map_zero, mk_eq_zero_iff] at this
    exact this
  refine ⟨fun i b => e i (Function.surjInv hπ b), ?_, ?_⟩
  · filter_upwards [h1] with i hi
    have hk : RingHom.ker π.toRingHom ≤ RingHom.ker (e i) := by
      rw [← hS, Ideal.span_le]
      exact fun s hs => hi s hs
    let p : B →+* A i := (RingHom.liftOfRightInverse π.toRingHom _
      (Function.rightInverse_surjInv hπ)) ⟨e i, hk⟩
    refine ⟨p, ?_⟩
    funext b
    have : p (π.toRingHom (Function.surjInv hπ b)) = e i (Function.surjInv hπ b) :=
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
    rw [← this]
    simp [Function.surjInv_eq hπ]
  · intro b
    rw [key', Function.surjInv_eq hπ]

end Rep

section Scheme

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X : Scheme.{0}}

instance (W : X.affineOpens) : IsOpenImmersion W.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec W.2

def pt (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    Spec (CommRingCat.of A) ⟶ X :=
  Spec.map (CommRingCat.ofHom p) ≫ W.2.fromSpec

lemma map_pt (W : X.affineOpens) {A B : Type} [CommRing A] [CommRing B] (p : Γ(X, W.1) →+* A)
    (q : A →+* B) :
    Spec.map (CommRingCat.ofHom q) ≫ pt W p = pt W (q.comp p) := by
  simp [pt, CommRingCat.ofHom_comp, Spec.map_comp]

lemma pt_injective (W : X.affineOpens) {A : Type} [CommRing A] {p q : Γ(X, W.1) →+* A}
    (h : pt W p = pt W q) : p = q := by
  have h' := (cancel_mono W.2.fromSpec).1 h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

def res {W W' : X.affineOpens} (h : W.1 ≤ W'.1) : Γ(X, W'.1) →+* Γ(X, W.1) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma pt_res {W W' : X.affineOpens} (h : W.1 ≤ W'.1) {A : Type} [CommRing A]
    (p : Γ(X, W.1) →+* A) : pt W' (p.comp (res h)) = pt W p := by
  have := IsAffineOpen.map_fromSpec W'.2 W.2 (homOfLE h).op
  simp only [pt, res, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  simp [this]

lemma pt_mem (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A)
    (x : Spec (CommRingCat.of A)) : (pt W p) x ∈ W.1 := by
  have : (W.2.fromSpec) ((Spec.map (CommRingCat.ofHom p)) x) ∈ Set.range W.2.fromSpec :=
    ⟨_, rfl⟩
  rw [W.2.range_fromSpec] at this
  simpa [pt] using this

lemma exists_pt_of_isLocalRing {A : Type} [CommRing A] [IsLocalRing A]
    (g : Spec (CommRingCat.of A) ⟶ X) (W : X.affineOpens)
    (hW : g (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ W.1) : ∃ p, g = pt W p := by
  have hr : Set.range g ⊆ Set.range W.2.fromSpec := by
    rw [W.2.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hs : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
    exact (hs.map g.continuous).mem_open W.1.2 hW
  refine ⟨(Spec.preimage (IsOpenImmersion.lift W.2.fromSpec g hr)).hom, ?_⟩
  simp [pt]

lemma exists_of_finite {α : Type} {S : Set α} (hS : S.Finite) {Q : α → ι → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, Q W i) : ∃ W ∈ S, ∀ᶠ i in (U : Filter ι), Q W i := by
  by_contra hcon
  push_neg at hcon
  have : ∀ᶠ i in (U : Filter ι), ∀ W ∈ S, ¬ Q W i :=
    (Filter.eventually_all_finite hS).2 fun W hW => hcon W hW
  obtain ⟨i, ⟨W, hW, h1⟩, h2⟩ := (H.and this).exists
  exact h2 W hW h1

lemma exists_affine_le {O : X.Opens} {x : X} (hx : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ O := by
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨W, hW⟩, hxW, hWO⟩

lemma exists_finite_affine_cover (O : X.Opens) (hO : IsCompact (O : Set X)) :
    ∃ S : Set X.affineOpens, S.Finite ∧ (∀ W ∈ S, W.1 ≤ O) ∧ ∀ x ∈ O, ∃ W ∈ S, x ∈ W.1 := by
  classical
  have h : ∀ x : X, ∃ W : X.affineOpens, x ∈ O → x ∈ W.1 ∧ W.1 ≤ O := by
    intro x
    by_cases hx : x ∈ O
    · obtain ⟨W, h1, h2⟩ := exists_affine_le hx
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · obtain ⟨W, h1, h2⟩ := exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨W, fun h => absurd h hx⟩
  choose w hw using h
  obtain ⟨t, ht, hcov⟩ := hO.elim_nhds_subcover (fun x => ((w x).1 : Set X))
    (fun x hx => ((w x).1.2.mem_nhds (hw x hx).1))
  refine ⟨w '' (t : Set X), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hw x (ht x hx)).2
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact ⟨w y, ⟨y, hy, rfl⟩, hxy⟩

variable {A : ι → Type} [∀ i, CommRing (A i)]

theorem ae_pt_eq_of_pt_eq [IsLocalRing (Ult U A)]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂) (H : pt W₁ g₁ = pt W₂ g₂) :
    ∀ᶠ i in (U : Filter ι), ∀ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i → ⇑q = h₂ i → pt W₁ p = pt W₂ q := by
  set x : X := (pt W₁ g₁) (IsLocalRing.closedPoint (Ult U A) : PrimeSpectrum (Ult U A)) with hx
  have hx₁ : x ∈ W₁.1 := pt_mem _ _ _
  have hx₂ : x ∈ W₂.1 := by rw [hx, H]; exact pt_mem _ _ _
  obtain ⟨W, hxW, hle⟩ := exists_affine_le (show x ∈ W₁.1 ⊓ W₂.1 from ⟨hx₁, hx₂⟩)
  have hle₁ : W.1 ≤ W₁.1 := hle.trans inf_le_left
  have hle₂ : W.1 ≤ W₂.1 := hle.trans inf_le_right
  obtain ⟨T, hT⟩ := exists_pt_of_isLocalRing (pt W₁ g₁) W hxW
  have e₁ : g₁ = T.comp (res hle₁) := pt_injective W₁ (by rw [pt_res]; exact hT)
  have e₂ : g₂ = T.comp (res hle₂) := pt_injective W₂ (by rw [pt_res, ← H]; exact hT)
  haveI := hfp W
  haveI := hfp W₁
  haveI := hfp W₂
  obtain ⟨h, hr⟩ := exists_rep U T
  have aeh : ∀ {W' : X.affineOpens} (hl : W.1 ≤ W'.1),
      IsAEHom U (fun i b => h i (res hl b)) := by
    intro W' hl
    filter_upwards [hr.1] with i ⟨t, ht⟩
    exact ⟨t.comp (res hl), by funext b; simp [← ht]⟩
  have a₁ := ae_eq_of_fg U r₁.1 (aeh hle₁) (fun b => by
    rw [← r₁.2, e₁]; exact hr.2 _)
  have a₂ := ae_eq_of_fg U r₂.1 (aeh hle₂) (fun b => by
    rw [← r₂.2, e₂]; exact hr.2 _)
  filter_upwards [a₁, a₂, hr.1] with i b₁ b₂ ⟨t, ht⟩ p q hp hq
  have p_eq : p = t.comp (res hle₁) := by
    ext b
    have := congrFun b₁ b
    rw [← hp] at this
    simpa [← ht] using this
  have q_eq : q = t.comp (res hle₂) := by
    ext b
    have := congrFun b₂ b
    rw [← hq] at this
    simpa [← ht] using this
  rw [p_eq, q_eq, pt_res, pt_res]

theorem pt_eq_of_ae_pt_eq [QuasiSeparatedSpace X] [∀ i, IsLocalRing (A i)]
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i ∧ ⇑q = h₂ i ∧ pt W₁ p = pt W₂ q) :
    pt W₁ g₁ = pt W₂ g₂ := by
  have hc : IsCompact (((W₁.1 ⊓ W₂.1 : X.Opens)) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ W₁.1.2 W₁.2.isCompact W₂.1.2 W₂.2.isCompact
  obtain ⟨S, hSf, hS1, hS2⟩ := exists_finite_affine_cover (W₁.1 ⊓ W₂.1) hc
  have hQ : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, ∃ t : Γ(X, W.1) →+* A i,
      ∃ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
        ⇑p = h₁ i ∧ ⇑q = h₂ i ∧ pt W t = pt W₁ p ∧ pt W t = pt W₂ q := by
    filter_upwards [H] with i ⟨p, q, hp, hq, e⟩
    have hx₁ : (pt W₁ p) (IsLocalRing.closedPoint (A i) : PrimeSpectrum (A i)) ∈ W₁.1 :=
      pt_mem _ _ _
    have hx₂ : (pt W₁ p) (IsLocalRing.closedPoint (A i) : PrimeSpectrum (A i)) ∈ W₂.1 := by
      rw [e]; exact pt_mem _ _ _
    obtain ⟨W, hW, hxW⟩ := hS2 _ (show _ ∈ W₁.1 ⊓ W₂.1 from ⟨hx₁, hx₂⟩)
    obtain ⟨t, ht⟩ := exists_pt_of_isLocalRing (pt W₁ p) W hxW
    exact ⟨W, hW, t, p, q, hp, hq, ht.symm, ht.symm.trans e⟩
  obtain ⟨W, hW, hQ⟩ := exists_of_finite U hSf hQ
  obtain ⟨h, hh⟩ := exists_family U hQ
  have ae : IsAEHom U h := by
    filter_upwards [hh] with i ⟨t, ht, _⟩
    exact ⟨t, ht⟩
  have hle₁ : W.1 ≤ W₁.1 := (hS1 W hW).trans inf_le_left
  have hle₂ : W.1 ≤ W₂.1 := (hS1 W hW).trans inf_le_right
  have e₁ : g₁ = (homOf U h ae).comp (res hle₁) := by
    refine RingHom.ext fun b => ?_
    rw [r₁.2, RingHom.comp_apply, homOf_apply, mk_eq_mk_iff]
    filter_upwards [hh] with i ⟨t, ht, p, q, hp, hq, e1, e2⟩
    have : p = t.comp (res hle₁) := pt_injective W₁ (by rw [pt_res]; exact e1.symm)
    rw [← hp, ← ht, this]
    rfl
  have e₂ : g₂ = (homOf U h ae).comp (res hle₂) := by
    refine RingHom.ext fun b => ?_
    rw [r₂.2, RingHom.comp_apply, homOf_apply, mk_eq_mk_iff]
    filter_upwards [hh] with i ⟨t, ht, p, q, hp, hq, e1, e2⟩
    have : q = t.comp (res hle₂) := pt_injective W₂ (by rw [pt_res]; exact e2.symm)
    rw [← hq, ← ht, this]
    rfl
  rw [e₁, e₂, pt_res, pt_res]

end Scheme

end GlobalTheory.CompanionTheory.Ultra
