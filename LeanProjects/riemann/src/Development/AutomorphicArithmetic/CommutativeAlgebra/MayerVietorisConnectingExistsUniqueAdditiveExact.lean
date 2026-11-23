import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.MVd

section Abstract
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

private abbrev pb {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (x : Cochain L M n) : Cochain K M n :=
  (Cochain.ofHom h).comp x (zero_add n)

private theorem pb_add {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (x y : Cochain L M n) :
    pb h (x + y) = pb h x + pb h y := Cochain.comp_add _ _ _ _

private theorem pb_sub {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (x y : Cochain L M n) :
    pb h (x - y) = pb h x - pb h y := Cochain.comp_sub _ _ _ _

private theorem pb_zero {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} :
    pb h (0 : Cochain L M n) = 0 := Cochain.comp_zero _ _

private theorem pb_comp {K L L' M : CochainComplex C ℤ} (h : K ⟶ L) (k : L ⟶ L') {n : ℤ} (x : Cochain L' M n) :
    pb (h ≫ k) x = pb h (pb k x) := by
  simp only [pb, Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ _

private theorem pb_hadd {K L M : CochainComplex C ℤ} (h k : K ⟶ L) {n : ℤ} (x : Cochain L M n) :
    pb (h + k) x = pb h x + pb k x := by
  simp only [pb, Cochain.ofHom_add]
  exact Cochain.add_comp _ _ _ _

private theorem pb_hsub {K L M : CochainComplex C ℤ} (h k : K ⟶ L) {n : ℤ} (x : Cochain L M n) :
    pb (h - k) x = pb h x - pb k x := by
  have := pb_hadd (h - k) k x
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

private theorem δ_pb {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (m : ℤ) (x : Cochain L M n) :
    δ n m (pb h x) = pb h (δ n m x) := δ_ofHom_comp _ _ _

private def zp {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (z : Cocycle L M n) : Cocycle K M n :=
  zcomp (Cocycle.ofHom h) z (zero_add n)

private theorem zp_coe {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (z : Cocycle L M n) :
    (zp h z).1 = pb h z.1 := rfl

private abbrev cp {K L : CochainComplex C ℤ} (h : K ⟶ L) (M : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L M n →+ CohomologyClass K M n :=
  cpre (Cocycle.ofHom h) M n n (zero_add n)

private theorem cp_mk {K L M : CochainComplex C ℤ} (h : K ⟶ L) {n : ℤ} (z : Cocycle L M n) :
    cp h M n (CohomologyClass.mk z) = CohomologyClass.mk (zp h z) := rfl

private structure MVX {P A B E : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p : P ⟶ A) (q : P ⟶ B) (i : A ⟶ E) (j : B ⟶ E) :
    Prop where
  comm : p ≫ i = q ≫ j
  e1 : ∀ (n : ℤ) (γ : Cochain P I n), ∃ (α : Cochain A I n) (β : Cochain B I n), pb p α - pb q β = γ
  e2 : ∀ (n : ℤ) (α : Cochain A I n) (β : Cochain B I n), pb p α = pb q β → ∃ c : Cochain E I n, pb i c = α ∧ pb j c = β
  e3 : ∀ (n : ℤ) (c : Cochain E I n), pb i c = 0 → pb j c = 0 → c = 0

private def Rel {P A B E : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p : P ⟶ A) (q : P ⟶ B) (i : A ⟶ E) (j : B ⟶ E) (n : ℤ)
    (c : CohomologyClass P I n) (x : CohomologyClass E I (n + 1)) : Prop :=
  ∃ (γ : Cocycle P I n) (ζ : Cocycle E I (n + 1)) (α : Cochain A I n) (β : Cochain B I n),
    CohomologyClass.mk γ = c ∧ CohomologyClass.mk ζ = x ∧ pb p α - pb q β = γ.1 ∧
    δ n (n + 1) α = pb i ζ.1 ∧ δ n (n + 1) β = pb j ζ.1

variable {P A B E I : CochainComplex C ℤ} {p : P ⟶ A} {q : P ⟶ B} {i : A ⟶ E} {j : B ⟶ E} {n : ℤ}

private theorem Rel.exists (X : MVX I p q i j) (c : CohomologyClass P I n) : ∃ x, Rel I p q i j n c x := by
  obtain ⟨γ, rfl⟩ := c.mk_surjective
  obtain ⟨α, β, h⟩ := X.e1 n γ.1
  have hδ : pb p (δ n (n + 1) α) = pb q (δ n (n + 1) β) := by
    rw [← δ_pb, ← δ_pb, ← sub_eq_zero, ← δ_sub, h]
    simp
  obtain ⟨ζ, h1, h2⟩ := X.e2 (n + 1) _ _ hδ
  have hz : δ (n + 1) (n + 1 + 1) ζ = 0 := X.e3 (n + 1 + 1) _
    (by rw [← δ_pb, h1, δ_δ]) (by rw [← δ_pb, h2, δ_δ])
  exact ⟨CohomologyClass.mk (Cocycle.mk ζ (n + 1 + 1) rfl hz), γ, Cocycle.mk ζ (n + 1 + 1) rfl hz, α, β, rfl, rfl, h,
    h1.symm, h2.symm⟩

private theorem Rel.add {c c' : CohomologyClass P I n} {x x' : CohomologyClass E I (n + 1)}
    (h : Rel I p q i j n c x) (h' : Rel I p q i j n c' x') : Rel I p q i j n (c + c') (x + x') := by
  obtain ⟨γ, ζ, α, β, rfl, rfl, h0, h1, h2⟩ := h
  obtain ⟨γ', ζ', α', β', rfl, rfl, h0', h1', h2'⟩ := h'
  refine ⟨γ + γ', ζ + ζ', α + α', β + β', CohomologyClass.mk_add _ _, CohomologyClass.mk_add _ _, ?_, ?_, ?_⟩
  · rw [pb_add, pb_add, add_sub_add_comm, h0, h0']
    rfl
  · rw [δ_add, h1, h1', ← pb_add]
    rfl
  · rw [δ_add, h2, h2', ← pb_add]
    rfl

private theorem Rel.sub {c c' : CohomologyClass P I n} {x x' : CohomologyClass E I (n + 1)}
    (h : Rel I p q i j n c x) (h' : Rel I p q i j n c' x') : Rel I p q i j n (c - c') (x - x') := by
  obtain ⟨γ, ζ, α, β, rfl, rfl, h0, h1, h2⟩ := h
  obtain ⟨γ', ζ', α', β', rfl, rfl, h0', h1', h2'⟩ := h'
  refine ⟨γ - γ', ζ - ζ', α - α', β - β', CohomologyClass.mk_sub _ _, CohomologyClass.mk_sub _ _, ?_, ?_, ?_⟩
  · rw [pb_sub, pb_sub, sub_sub_sub_comm, h0, h0']
    rfl
  · rw [δ_sub, h1, h1', ← pb_sub]
    rfl
  · rw [δ_sub, h2, h2', ← pb_sub]
    rfl

private theorem Rel.eq_zero (X : MVX I p q i j) {x : CohomologyClass E I (n + 1)}
    (h : Rel I p q i j n 0 x) : x = 0 := by
  obtain ⟨γ, ζ, α, β, hγ, rfl, h0, h1, h2⟩ := h
  rw [CohomologyClass.mk_eq_zero_iff] at hγ ⊢
  obtain ⟨m, hm, τ, hτ⟩ := hγ
  obtain ⟨a, b, hab⟩ := X.e1 m τ
  have e : pb p α - pb q β = δ m n (pb p a) - δ m n (pb q b) := by rw [h0, ← hτ, ← hab, δ_sub]
  have hc : pb p (α - δ m n a) = pb q (β - δ m n b) := by
    rw [pb_sub, pb_sub, ← δ_pb, ← δ_pb]
    exact sub_eq_sub_iff_sub_eq_sub.1 e
  obtain ⟨c, c1, c2⟩ := X.e2 n _ _ hc
  have hz : ζ.1 - δ n (n + 1) c = 0 := X.e3 (n + 1) _
    (by rw [pb_sub, ← δ_pb, c1, δ_sub, δ_δ, sub_zero, h1, sub_self])
    (by rw [pb_sub, ← δ_pb, c2, δ_sub, δ_δ, sub_zero, h2, sub_self])
  exact ⟨n, rfl, c, (sub_eq_zero.1 hz).symm⟩

private theorem Rel.unique (X : MVX I p q i j) {c : CohomologyClass P I n} {x x' : CohomologyClass E I (n + 1)}
    (h : Rel I p q i j n c x) (h' : Rel I p q i j n c x') : x = x' := by
  have h2 := h.sub h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (Rel.eq_zero X h2)

private theorem Rel.of_cocycles (a : Cocycle A I n) (b : Cocycle B I n) :
    Rel I p q i j n (cp p I n (CohomologyClass.mk a) - cp q I n (CohomologyClass.mk b)) 0 := by
  refine ⟨zp p a - zp q b, 0, a.1, b.1, CohomologyClass.mk_sub _ _, CohomologyClass.mk_zero _ _ _, rfl, ?_, ?_⟩
  · simp
  · simp

private theorem Rel.iff_zero (X : MVX I p q i j) {c : CohomologyClass P I n} {x : CohomologyClass E I (n + 1)}
    (h : Rel I p q i j n c x) : x = 0 ↔ ∃ a b, c = cp p I n a - cp q I n b := by
  constructor
  · obtain ⟨γ, ζ, α, β, rfl, rfl, h0, h1, h2⟩ := h
    intro hz
    rw [CohomologyClass.mk_eq_zero_iff] at hz
    obtain ⟨m, hm, τ, hτ⟩ := hz
    obtain rfl : m = n := by omega
    have ha : δ m (m + 1) (α - pb i τ) = 0 := by rw [δ_sub, δ_pb, hτ, h1, sub_self]
    have hb : δ m (m + 1) (β - pb j τ) = 0 := by rw [δ_sub, δ_pb, hτ, h2, sub_self]
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (m + 1) rfl ha), CohomologyClass.mk (Cocycle.mk _ (m + 1) rfl hb), ?_⟩
    rw [cp_mk, cp_mk, ← CohomologyClass.mk_sub]
    congr 1
    apply Cocycle.ext
    change γ.1 = pb p (α - pb i τ) - pb q (β - pb j τ)
    rw [pb_sub, pb_sub, ← pb_comp, ← pb_comp, X.comm, ← h0]
    abel
  · rintro ⟨a, b, rfl⟩
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨b, rfl⟩ := b.mk_surjective
    exact Rel.unique X h (Rel.of_cocycles a b)

private theorem Rel.iff_pull (X : MVX I p q i j) (x : CohomologyClass E I (n + 1)) :
    (cp i I (n + 1) x = 0 ∧ cp j I (n + 1) x = 0) ↔ ∃ c, Rel I p q i j n c x := by
  constructor
  · obtain ⟨ζ, rfl⟩ := x.mk_surjective
    rintro ⟨h1, h2⟩
    rw [cp_mk, CohomologyClass.mk_eq_zero_iff] at h1 h2
    obtain ⟨m, hm, α, hα⟩ := h1
    obtain ⟨m', hm', β, hβ⟩ := h2
    obtain rfl : m = n := by omega
    obtain rfl : m' = m := by omega
    have hγ : δ m' (m' + 1) (pb p α - pb q β) = 0 := by
      have e : pb p (pb i ζ.1) = pb q (pb j ζ.1) := by rw [← pb_comp, ← pb_comp, X.comm]
      have hα' : δ m' (m' + 1) α = pb i ζ.1 := hα
      have hβ' : δ m' (m' + 1) β = pb j ζ.1 := hβ
      rw [δ_sub, δ_pb, δ_pb, hα', hβ', e, sub_self]
    exact ⟨_, Cocycle.mk _ (m' + 1) rfl hγ, ζ, α, β, rfl, rfl, rfl, hα, hβ⟩
  · rintro ⟨c, γ, ζ, α, β, -, rfl, -, h1, h2⟩
    rw [cp_mk, cp_mk, CohomologyClass.mk_eq_zero_iff, CohomologyClass.mk_eq_zero_iff]
    exact ⟨⟨n, rfl, α, h1⟩, ⟨n, rfl, β, h2⟩⟩

private theorem Rel.nat {P' A' B' E' : CochainComplex C ℤ} {p' : P' ⟶ A'} {q' : P' ⟶ B'} {i' : A' ⟶ E'} {j' : B' ⟶ E'}
    (m : P ⟶ P') (u : A ⟶ A') (v : B ⟶ B') (w : E ⟶ E') (h1 : m ≫ p' = p ≫ u) (h2 : m ≫ q' = q ≫ v)
    (h3 : i ≫ w = u ≫ i') (h4 : j ≫ w = v ≫ j') {c : CohomologyClass P' I n} {x : CohomologyClass E' I (n + 1)}
    (h : Rel I p' q' i' j' n c x) : Rel I p q i j n (cp m I n c) (cp w I (n + 1) x) := by
  obtain ⟨γ, ζ, α, β, rfl, rfl, h0, e1, e2⟩ := h
  refine ⟨zp m γ, zp w ζ, pb u α, pb v β, rfl, rfl, ?_, ?_, ?_⟩
  · rw [zp_coe, ← h0, pb_sub, ← pb_comp, ← pb_comp, ← pb_comp, ← pb_comp, h1, h2]
  · rw [δ_pb, e1, zp_coe, ← pb_comp, ← pb_comp, h3]
  · rw [δ_pb, e2, zp_coe, ← pb_comp, ← pb_comp, h4]

private theorem pb_id {K M : CochainComplex C ℤ} {n : ℤ} (x : Cochain K M n) : pb (𝟙 K) x = x := Cochain.id_comp _

private theorem pb_hzero {K L M : CochainComplex C ℤ} {n : ℤ} (x : Cochain L M n) : pb (0 : K ⟶ L) x = 0 := by
  have := pb_hsub (0 : K ⟶ L) 0 x
  rwa [sub_zero, sub_self] at this

end Abstract

private theorem mvx_of_se {R : Type} [CommRing R] {P A B E I : Cx R} {p : P ⟶ A} {q : P ⟶ B} {i : A ⟶ E} {j : B ⟶ E}
    (comm : p ≫ i = q ≫ j) (w)
    (hS : (ShortComplex.mk (biprod.lift p (-q)) (biprod.desc i j) w).ShortExact) (hI : ∀ n, Injective (I.X n)) :
    MVX I p q i j := by
  have hl : biprod.lift p (-q) = p ≫ biprod.inl - q ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have hd : biprod.desc i j = biprod.fst ≫ i + biprod.snd ≫ j := by
    apply biprod.hom_ext' <;> simp
  refine ⟨comm, fun n γ => ?_, fun n α β h => ?_, fun n c h1 h2 => ?_⟩
  · obtain ⟨b, hb⟩ := (GlobalTheory.T.etaleCochain_shortExact_of_injective_terms R I hI _ hS n).1 γ
    have hb' : pb (biprod.lift p (-q)) b = γ := hb
    refine ⟨pb biprod.inl b, pb biprod.inr b, ?_⟩
    rw [← pb_comp, ← pb_comp, ← pb_hsub, ← hl, hb']
  · have hb1 : pb biprod.inl (pb biprod.fst α + pb biprod.snd β) = α := by
      rw [pb_add, ← pb_comp, ← pb_comp, biprod.inl_fst, biprod.inl_snd, pb_id, pb_hzero, add_zero]
    have hb2 : pb biprod.inr (pb biprod.fst α + pb biprod.snd β) = β := by
      rw [pb_add, ← pb_comp, ← pb_comp, biprod.inr_fst, biprod.inr_snd, pb_id, pb_hzero, zero_add]
    have hf : pb (biprod.lift p (-q)) (pb biprod.fst α + pb biprod.snd β) = 0 := by
      rw [hl, pb_hsub, pb_comp, pb_comp, hb1, hb2, h, sub_self]
    obtain ⟨c, hc⟩ := (GlobalTheory.T.etaleCochain_shortExact_of_injective_terms R I hI _ hS n).2.1 _ hf
    have hc' : pb (biprod.desc i j) c = pb biprod.fst α + pb biprod.snd β := hc
    refine ⟨c, ?_, ?_⟩
    · rw [← biprod.inl_desc i j, pb_comp, hc', hb1]
    · rw [← biprod.inr_desc i j, pb_comp, hc', hb2]
  · refine (GlobalTheory.T.etaleCochain_shortExact_of_injective_terms R I hI _ hS n).2.2 c ?_
    change pb (biprod.desc i j) c = 0
    rw [hd, pb_hadd, pb_comp, pb_comp, h1, h2, pb_zero, pb_zero, add_zero]

private theorem mvx (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    MVX (res R F) ((chains R).map (pullback.fst f g)) ((chains R).map (pullback.snd f g)) ((chains R).map f) ((chains R).map g) := by
  obtain ⟨w, hS⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact mvx_of_se (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]) w hS (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1

end UpperTheory.MVd

open UpperTheory.MVd in
theorem UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact :
    ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ),
        (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
          (∀ c : H R (pullback f g) F n, ∃ x, IsMVd f g F n c x) ∧
          (∀ c x x', IsMVd f g F n c x → IsMVd f g F n c x' → x = x') ∧
          (∀ c c' x x', IsMVd f g F n c x → IsMVd f g F n c' x' → IsMVd f g F n (c + c') (x + x')) ∧
          (∀ c x, IsMVd f g F n c x → (x = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b)) ∧
          (∀ x : H R E F (n + 1), (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, IsMVd f g F n c x) ∧
          (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b)) ∧
        ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V')
          (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g'), Cover2 R f g → Cover2 R f' g' → ∀ c x, IsMVd f' g' F n c x →
          IsMVd f g F n (pull R (pullback.map f g f' g' u v p hu hv) F n c) (pull R p F (n + 1) x) := by
  intro R _ F n
  refine ⟨?_, ?_⟩
  · intro U V E f g h
    have X := mvx R F f g h
    obtain ⟨d, hd, -⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
    exact ⟨fun c => Rel.exists X c, fun c x x' => Rel.unique X, fun c c' x x' => Rel.add,
      fun c x hx => Rel.iff_zero X hx, fun x => Rel.iff_pull X x, fun a b => (hd f g h n).1 a b⟩
  · intro U V E U' V' E' f g f' g' p u v hu hv _ _ c x hx
    refine Rel.nat ((chains R).map (pullback.map f g f' g' u v p hu hv)) ((chains R).map u) ((chains R).map v)
      ((chains R).map p) ?_ ?_ ?_ ?_ hx
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd]
    · rw [← Functor.map_comp, ← Functor.map_comp, hu]
    · rw [← Functor.map_comp, ← Functor.map_comp, hv]
