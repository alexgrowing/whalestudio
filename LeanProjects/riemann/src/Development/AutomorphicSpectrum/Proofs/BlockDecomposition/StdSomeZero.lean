import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBcOfNe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmorFrFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartLocBc

section Alg

theorem tens_of_ring {R R' : Type} [CommRing R] [CommRing R'] (A₁ A₂ : Algebra R R') (hA : A₁ = A₂)
    {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] {B B' : Type} [CommRing B] [CommRing B']
    [Algebra R B] (u : B ≃ₗ[R] M) (v : B' ≃+ M') (i : R' →+* B') (φ : B →+* B')
    (t : letI := A₁; R' ⊗[R] B ≃+* B') (h1 : letI := A₁; ∀ r, t (r ⊗ₜ 1) = i r)
    (h2 : letI := A₁; ∀ x, t (1 ⊗ₜ x) = φ x) (f : Unit → R' → M → M')
    (hf : ∀ n y, f () n (u y) = v (i n * φ y)) :
    letI := A₂; Tens R (N := fun _ : Unit => R') (M := fun _ => M) (M' := M') f := by
  subst hA
  letI := A₁
  let w : R' ⊗[R] M ≃+ M' :=
    ((TensorProduct.congr (LinearEquiv.refl R R') u.symm).toAddEquiv.trans t.toAddEquiv).trans v
  refine ⟨(LinearEquiv.funUnique Unit R (R' ⊗[R] M)).toAddEquiv.trans w, ?_⟩
  rintro ⟨⟩ n x
  obtain ⟨y, rfl⟩ := u.surjective x
  have e : t (n ⊗ₜ y) = i n * φ y := by
    have : n ⊗ₜ[R] y = (n ⊗ₜ[R] (1 : B)) * ((1 : R') ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, h1, h2]
  rw [hf, ← e]
  simp [w]

end Alg

section Sub

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def sqEquiv (a b : IdF A) (T : C) (ha : a.S T = ⊤) (hb : b.S T = ⊥) : A.obj T ≃ₗ[R] sqM a b T :=
  LinearEquiv.ofBijective
    { toFun := fun x => sqMk a b x (by rw [ha]; trivial)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨fun x y h => by
      have h' : Ideal.Quotient.mk (b.S T) x = Ideal.Quotient.mk (b.S T) y := congrArg Subtype.val h
      have := Ideal.Quotient.eq.1 h'
      rw [hb, Ideal.mem_bot] at this
      exact sub_eq_zero.1 this,
     fun ⟨z, hz⟩ => by
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨w, rfl⟩⟩

end Sub

section Poly

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

open CrystallineSemistableComparison.Pb.Site

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem univ_poly (T : Thick (nlFun γ p X q κ)) (hp : p ≠ 0) {T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T')
    (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : polyT T hp ⟶ T', polyJ T hp ≫ ψ = φ ∧ ψ.φ ((pq T.B).e 1) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hle : (pq T.B).ext T.J ≤ T'.J.comap F := Ideal.map_le_iff_le_comap.1 hF3.1
  refine ⟨descOf φ F hF1 hF3 hle, ⟨hom_ext hF1, hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = F
  exact hFu ψ.φ ⟨congrArg Thick.Hom.φ h1, h2, ψ.dp⟩

def polyS (hp : p ≠ 0) (𝒱 : Set X.Opens) : Poly (sP (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱)) where
  P T := ⟨polyT T.obj hp, trivial, by
    obtain ⟨V, hV, h⟩ := T.property.2
    exact ⟨V, hV, inU_hom (polyJ T.obj hp) h⟩⟩
  j T := ObjectProperty.homMk (polyJ T.obj hp)
  X T := (pq T.obj.B).e 1
  X_mem T := e_mem _ _
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_poly T.obj hp φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ z

end Poly

section Std

variable {b : Base} {L : b.Fun}

theorem std_some_top (Q : ObjectProperty (Thick L)) (c : b.R) {r : ℤ} (hr : r ≤ 0) (T : Q.FullSubcategory) :
    (stdI Q (some r) c).S T = ⊤ := by
  have h : (sFil Q r).S T = ⊤ := by
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  change (sFil Q r).S T ⊔ _ = ⊤
  rw [h, top_sup_eq]

theorem mem_some (Q : ObjectProperty (Thick L)) (c : b.R) {r : ℤ} (hr : r ≤ 0) (T : Q.FullSubcategory)
    (x : (sP Q).A.obj T) : x ∈ (stdI Q (some r) c).S T := by
  rw [std_some_top Q c hr T]
  trivial

theorem std_none_bot (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) :
    (stdI Q none 0).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

theorem std_some_zero (Q : ObjectProperty (Thick L)) (r : ℤ) (T : Q.FullSubcategory) :
    (stdI Q (some r) 0).S T = (sFil Q r).S T := by
  change (sFil Q r).S T ⊔ Ideal.span {algebraMap b.R _ 0} = _
  simp

end Std

section Crit

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem crit_some (hp : p ≠ 0) (𝒱 : Set X.Opens) (c : R) {r : ℤ} (hr : r ≤ 0) :
    (polyS (γ := γ) (q := q) (κ := κ) hp 𝒱).Crit (fun r => stdI _ (some r) c) r := fun T b =>
  ⟨fun _ k => mem_some _ _ (by omega) _ _, fun _ => mem_some _ _ hr _ _⟩

theorem crit_none (hp : p ≠ 0) (𝒱 : Set X.Opens) (r : ℤ) :
    (polyS (γ := γ) (q := q) (κ := κ) hp 𝒱).Crit (fun _ => stdI _ none 0) r := by
  intro T b
  have key := GlobalTheory.CompanionTheory.SiteTrCrit.repr_sum T.obj.δ b
  refine ⟨fun h k => ?_, fun h => ?_⟩
  · have h0 := h
    change _ ∈ (stdI _ none 0).S _ at h0
    rw [std_none_bot, Ideal.mem_bot] at h0
    change _ ∈ (stdI _ none 0).S T
    rw [std_none_bot, Ideal.mem_bot]
    have h1 : b = 0 := by
      rw [← key]
      exact (congrArg _ h0).trans (map_zero _)
    rw [h1]
    rfl
  · have h1 : b = 0 := by
      ext k
      have := h k
      change _ ∈ (stdI _ none 0).S T at this
      rw [std_none_bot, Ideal.mem_bot] at this
      exact this
    subst h1
    exact Ideal.zero_mem _

theorem ladder (hp : p ≠ 0) (𝒱 : Set X.Opens) :
    (polyS (γ := γ) (q := q) (κ := κ) hp 𝒱).Ladder (fun r => stdI _ (some r) 0) (fun _ => stdI _ none 0) 0 where
  le r' T := by
    change (stdI _ none 0).S T ≤ (stdI _ (some r') 0).S T
    rw [std_none_bot]
    exact bot_le
  ca _ h := crit_some hp 𝒱 0 h
  cb r' _ := crit_none hp 𝒱 r'

end Crit

end GlobalTheory.CompanionTheory.ChartLocBc

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartLocBc

section Main

variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'}

theorem leC_some (m : NMor γ q κ γ' q κ' σ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    (Q' : ObjectProperty (Thick (nlFun γ' p X q κ'))) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (c : R') (r : ℤ) :
    (m.smor Q Q' h).LeC c (stdI Q (some r) 0) (stdI Q' (some r) 0) := by
  intro T x hx
  rw [std_some_zero] at hx ⊢
  exact Ideal.mul_mem_left _ _ hx

theorem leC_none (m : NMor γ q κ γ' q κ' σ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    (Q' : ObjectProperty (Thick (nlFun γ' p X q κ'))) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (c : R') :
    (m.smor Q Q' h).LeC c (stdI Q none 0) (stdI Q' none 0) := by
  intro T x hx
  rw [std_none_bot, Ideal.mem_bot] at hx
  subst hx
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

end Main

theorem local_bc : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) {V : X.Opens} {d : ℕ} (c : Coord q V d)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {V}) (hQ' : Q' = St ⊤ {V}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  intro O R R' _ _ _ _ _ I I' γ γ' p hp hn X q κ κ' m hu hg V d c Q Q' hQ hQ' h ha hb j
  subst hQ hQ'
  obtain ⟨c₀, -, -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart γ p hp hn q κ c
  obtain ⟨c', e, he, -, f, hf1, hf2⟩ := GlobalTheory.CompanionTheory.ChartBc.chart_bc_of_ne m hp hu hg c₀
  have g₀ := GlobalTheory.CompanionTheory.ChartMaps.good c₀
  have g' := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hV : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, hW⟩
    exact hW
  have hV' : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, hW⟩
    exact hW
  have hD : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} c₀.D := ⟨trivial, V, rfl, c₀.inV⟩
  have hD' : St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ {V} c'.D := ⟨trivial, V, rfl, c'.inV⟩
  have hFr := GlobalTheory.CompanionTheory.ChartFrames.smor_Fr_frame m c₀ c' g₀ g' _ _ h hV hD hV' hD' e he
  letI := c₀.D.i.toAlgebra
  exact GlobalTheory.CompanionTheory.LocBC.local_base_change (m.smor _ _ h) (polyS hp {V}) (polyS hp {V})
    (c₀.frame g₀ _ hV hD) (c'.frame g' _ hV' hD') (ObjectProperty.homMk e) hFr (fun _ => Function.injective_id) (ι := Unit) (fun _ => R')
    (fun _ => LinearMap.id) (fun _ r => stdI _ (some r) 0) (fun _ _ => stdI _ none 0)
    (fun r => stdI _ (some r) 0) (fun _ => stdI _ none 0) 0 (fun _ => ladder hp _) (ladder hp _)
    (fun _ n r' => leC_some m _ _ h n r') (fun _ n _ => leC_none m _ _ h n)
    (fun r' _ hr' => by
      refine tens_of_ring (B := c₀.D.B) (B' := c'.D.B) (algebraMap R R').toAlgebra inferInstance
        (Algebra.algebra_ext _ _ fun _ => rfl)
        (sqEquiv (stdI _ (some r') 0) (stdI _ none 0) (⟨c₀.D, hD⟩ : (St ⊤ {V}).FullSubcategory)
          (std_some_top _ _ hr' _) (std_none_bot _ _))
        (sqEquiv (stdI _ (some r') 0) (stdI _ none 0) (⟨c'.D, hD'⟩ : (St ⊤ {V}).FullSubcategory)
          (std_some_top _ _ hr' _) (std_none_bot _ _)).toAddEquiv
        c'.D.i e.φ f hf1 hf2 _ ?_
      intro n y
      exact Subtype.ext rfl) j

end GlobalTheory.CompanionTheory.ChartLocBc
