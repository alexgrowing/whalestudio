import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem isNilpotent_of_mem_J (hp : b.p ≠ 0) {L : b.Fun} (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := T.adm.1 hp
  obtain ⟨c, hc⟩ : b.p ∣ b.p.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hp) le_rfl
  refine ⟨b.p * N, ?_⟩
  rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hc, Nat.cast_mul, mul_assoc, mul_pow, hN, zero_mul]

def push (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : Thick (F.cr b ht κ) where
  B := B'
  i := g.comp T.i
  J := T.J.map g
  δ := δ'
  adm := ⟨fun h => by simpa using (T.adm.1 h).map g, fun h => by
    obtain ⟨n, hn⟩ := T.adm.2 h
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩⟩
  compat := IsDPMorphism.comp δ' hg T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map)) T.y
  inα := trivial
  w r := by
    rw [(F.cr b ht κ).str_map]
    change (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w]; rfl
  x j := j.elim
  v j := j.elim
  s := Units.map g.toMonoidHom T.s
  hx j := j.elim
  hs := by
    have h := congrArg g T.hs
    have e : ∏ j, T.x j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, map_one, map_mul] at h
    exact (Finset.prod_of_isEmpty (ι := Empty) _).trans h
  hv := by
    have h := T.hv
    have e : ∏ j, T.v j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e] at h
    refine Eq.trans ?_ (Finset.prod_of_isEmpty (ι := Empty) _).symm
    ext
    have h' := congrArg (fun u : (T.B ⧸ T.J)ˣ => Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map (u : T.B ⧸ T.J)) h
    simpa using h'

def pushHom (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : T ⟶ push T g δ' hg where
  φ := g
  u j := j.elim
  comm _ := rfl
  dp := hg
  hle := Ideal.le_comap_map
  pt := rfl
  hx j := j.elim
  hs := by
    have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : (push T g δ' hg).Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, one_mul]; rfl
  hv j := j.elim

def pushDesc (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'') (χ : B' →+* T''.B) (h : χ.comp g = ψ.φ) :
    push T g δ' hg ⟶ T'' :=
  have hdp : IsDPMorphism δ' T''.δ χ := (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ g δ' hg).2 T''.δ χ (h ▸ ψ.dp)
  have hle : T.J.map g ≤ T''.J.comap χ := Ideal.map_le_iff_le_comap.1 hdp.1
  have e2 : CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ≫
      CommRingCat.ofHom (Ideal.quotientMap T''.J χ hle) = CommRingCat.ofHom (Ideal.quotientMap T''.J ψ.φ ψ.hle) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (χ (g x)) = Ideal.Quotient.mk _ (ψ.φ x)
    rw [← RingHom.comp_apply χ g, h]
  { φ := χ
    u := fun j => j.elim
    comm := fun r => by
      change χ (g (T.i r)) = _
      rw [← RingHom.comp_apply χ g, h]; exact ψ.comm r
    dp := hdp
    hle := hle
    pt := by
      refine Eq.trans ?_ ψ.pt
      change (F.cr b ht κ).Pt.map _ ((F.cr b ht κ).Pt.map _ T.y) = (F.cr b ht κ).Pt.map _ T.y
      rw [← e2, Functor.map_comp]
      rfl
    hx := fun j => j.elim
    hs := by
      have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : T''.Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e, one_mul, ψ.hs]
      have e' : ∏ j, ψ.u j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e', one_mul]
      ext
      change ψ.φ _ = χ (g _)
      rw [← RingHom.comp_apply χ g, h]
    hv := fun j => j.elim }

theorem hom_ext_cr {T T' : Thick (F.cr b ht κ)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  Thick.Hom.ext h (funext fun j => j.elim)

def locT (T : Thick (F.cr b ht κ)) (a : T.B) : Thick (F.cr b ht κ) :=
  push T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

def locHom (T : Thick (F.cr b ht κ)) (a : T.B) : T ⟶ locT T a :=
  pushHom T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

theorem locHom_φ (T : Thick (F.cr b ht κ)) (a : T.B) :
    (locHom T a).φ = algebraMap T.B (Localization.Away a) := rfl

theorem comp_φ {L : b.Fun} {T T' T'' : Thick L} (f : T ⟶ T') (g : T' ⟶ T'') : (f ≫ g).φ = g.φ.comp f.φ := rfl

theorem locT_univ (T : Thick (F.cr b ht κ)) (a : T.B) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'')
    (hu : IsUnit (ψ.φ a)) : ∃! χ : locT T a ⟶ T'', locHom T a ≫ χ = ψ := by
  let l : Localization.Away a →+* T''.B := IsLocalization.Away.lift a hu
  have hl : l.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := IsLocalization.Away.lift_comp a hu
  refine ⟨pushDesc T _ _ _ ψ l hl, hom_ext_cr hl, fun χ hχ => hom_ext_cr ?_⟩
  let χ' : Localization.Away a →+* T''.B := χ.φ
  have h1 : χ'.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := congrArg Thick.Hom.φ hχ
  have h2 : χ' = l := IsLocalization.ringHom_ext (Submonoid.powers a) (h1.trans hl.symm)
  exact h2

theorem unit_of_mem (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (S : Finset (Fin m)) {k : Fin m} (hk : k ∈ S) :
    IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := by
  have h : IsUnit (algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (∏ k ∈ S, f k)) :=
    IsLocalization.Away.algebraMap_isUnit _
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f hk)) h

theorem pdPow_locT (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) :
    (locT T a).pdPow r = (T.pdPow r).map (algebraMap T.B (Localization.Away a)) :=
  (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ (algebraMap T.B (Localization.Away a)) _
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))).1 r

theorem loc_surj (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) (y : Localization.Away a)
    (hy : y ∈ (T.pdPow r).map (algebraMap T.B (Localization.Away a))) :
    ∃ (n : ℕ) (x : T.B), x ∈ T.pdPow r ∧
      algebraMap T.B (Localization.Away a) (a ^ n) * y = algebraMap T.B (Localization.Away a) x := by
  obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a) _).1 hy
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, x.1, x.2, ?_⟩
  have hn' : a ^ n = s := hn
  rw [mul_comm, hn']
  exact hx

theorem span_lift (hp : b.p ≠ 0) (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (s : Fin m → T.B ⧸ T.J)
    (hf : ∀ k, Ideal.Quotient.mk T.J (f k) = s k) (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range f) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) = ⊤ := by
    rw [Ideal.map_span, ← Set.range_comp, ← hs]
    congr 2
    exact funext hf
  have h2 : (1 : T.B ⧸ T.J) ∈ Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ T.J := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (isNilpotent_of_mem_J hp T hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Mod

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r : ℕ)

def mulR (T : Thick (F.cr b ht κ)) : T.B →+* Module.End Λ ((pdS (F.cr b ht κ) c r).fn.obj T) where
  toFun a :=
    { toFun := fun x => ⟨(show T.B from a * (show T.B from x.1)), (T.pdPow r).mul_mem_left a x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a (show T.B from x.1) (show T.B from y.1))
      map_smul' := fun e x => Subtype.ext (mul_left_comm a (T.i (c e)) (show T.B from x.1)) }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_mul (show T.B from x.1))
  map_mul' a a' := LinearMap.ext fun x => Subtype.ext (mul_assoc a a' (show T.B from x.1))
  map_zero' := LinearMap.ext fun x => Subtype.ext (zero_mul (show T.B from x.1))
  map_add' a a' := LinearMap.ext fun x => Subtype.ext (add_mul a a' (show T.B from x.1))

def locMod (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (hf : Ideal.span (Set.range f) = ⊤) :
    LocMod (pdS (F.cr b ht κ) c r).fn T (fun S => locT T (∏ k ∈ S, f k)) (fun S => locHom T (∏ k ∈ S, f k)) where
  Λ := T.B
  f := f
  span := hf
  ρ₀ := mulR c r T
  ρ S := (mulR c r (locT T (∏ k ∈ S, f k))).comp (locHom T (∏ k ∈ S, f k)).φ
  lam_ρ S a x := Subtype.ext (map_mul (locHom T (∏ k ∈ S, f k)).φ a (show T.B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : t.φ.comp (locHom T (∏ k ∈ S, f k)).φ = (locHom T (∏ k ∈ S', f k)).φ := congrArg Thick.Hom.φ ht'
    refine Subtype.ext ?_
    change t.φ ((locHom T (∏ k ∈ S, f k)).φ a * (show (locT T (∏ k ∈ S, f k)).B from x.1)) =
      (locHom T (∏ k ∈ S', f k)).φ a * t.φ (show (locT T (∏ k ∈ S, f k)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply t.φ, e]
  unit S k hk := by
    have hu : IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := unit_of_mem T f S hk
    obtain ⟨u, hu⟩ := hu
    have hinv : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
    have hinv' : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    change Function.Bijective (mulR c r _ ((locHom T (∏ k ∈ S, f k)).φ (f k)))
    rw [← hu]
    exact ⟨Function.LeftInverse.injective hinv', Function.RightInverse.surjective hinv⟩
  surj S y := by
    obtain ⟨n, x, hx, e⟩ := loc_surj T (∏ k ∈ S, f k) r y.1 ((pdPow_locT T _ r).le y.2)
    exact ⟨n, ⟨x, hx⟩, Subtype.ext e⟩
  ker S x hx := by
    have h0 : algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (show T.B from x.1) = 0 := congrArg Subtype.val hx
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ k ∈ S, f k)) _ _).1 h0
    exact ⟨n, Subtype.ext hn⟩

end Mod

theorem zarCov_pdS : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type}
    [CommRing Λ] (c : Λ →+* b.R) {d : ℕ} (𝒜 : F.Atlas d), b.p ≠ 0 → ∀ r : ℕ,
    ZarCov (pdS (F.cr b ht κ) c r).fn fun T => ∃ α, (𝒜.V α).In T.y.1.2 := by
  intro O _ F b ht κ Λ _ c d 𝒜 hp r
  refine ⟨fun T T' φ ⟨α, hα⟩ => ⟨α, ?_⟩, fun T => ?_⟩
  · have h := (𝒜.V α).in_map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) hα
    rw [← φ.pt]
    exact h
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2
  choose f hf using fun k => Ideal.Quotient.mk_surjective (s k)
  have hspan : Ideal.span (Set.range f) = ⊤ := span_lift hp T f s hf hs
  refine ⟨m, fun k _ ψ => IsUnit (ψ.φ (f k)), fun k T₁ T₂ ψ χ h => h.map χ.φ, fun k T₁ ψ h => ?_, fun T' φ => ?_⟩
  · have hu : IsUnit ((CommRingCat.ofHom (Ideal.quotientMap T₁.J ψ.φ ψ.hle)).hom (s k)) := by
      rw [← hf k]; exact h.map (Ideal.Quotient.mk T₁.J)
    obtain ⟨α, hα⟩ := hcov k _ _ hu
    refine ⟨α, ?_⟩
    rw [← ψ.pt]
    exact hα
  refine ⟨fun S => locT T' (∏ k ∈ S, φ.φ (f k)), fun S => locHom T' _, fun S k hk => unit_of_mem T' _ S hk,
    fun S T'' ψ h => locT_univ T' _ ψ ?_, ⟨locMod c r T' (fun k => φ.φ (f k)) ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one h
  · have h := congrArg (Ideal.map φ.φ) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h

end GlobalTheory.CompanionTheory.ThickZar
