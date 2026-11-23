import Mathlib
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TraitDataOfDataAtTraits

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Host

variable (D : D7) (H : Geo.Tor.Host D.host.E)

theorem isAbelianGalois_host : IsAbelianGalois ℚ D.host.E := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have : IsMulCommutative Gal(D.host.E/ℚ) := ⟨⟨fun σ τ => hbij.1 (by rw [hmul, hmul, _root_.mul_comm])⟩⟩
  exact {}

theorem not_cube_dvd (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ¬ w.asIdeal ^ 3 ∣ Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have hp := D.host.hyp.2.1
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := w.isPrime
  have hmax : (Ideal.span {(D.host.d : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have : w.asIdeal.LiesOver (Ideal.span {(D.host.d : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simpa using hw)⟩
  have hb : (Ideal.span {(D.host.d : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have hIn : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) =
        Nat.card ({1, D.R.toFrame.iod} : Set (D.R.GG)) :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) fun σ => by
        rw [AddSubgroup.mem_inertia]
        exact D.host.der.inertia_d w.asIdeal σ)
    rw [e, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    have := congrArg (fun g : D.R.GG => g.1.2) h
    exact absurd (show (1 : ℤˣ) = -1 from this) (by decide)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(D.host.d : ℤ)}) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(D.host.d : ℤ)}) w.asIdeal hb] at hIn
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 D.host.E)) (Ideal.span {(D.host.d : ℤ)}) =
      Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity (by rw [hm]; simpa using hp.ne_zero) w.isPrime, hm] at hIn
  have hf : FiniteMultiplicity w.asIdeal (Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)}) := by
    by_contra hn
    rw [multiplicity_eq_one_of_not_finiteMultiplicity hn] at hIn
    omega
  have := hf.le_multiplicity_of_pow_dvd h
  omega

theorem isHostField (hd : H.d = D.host.d) : EigenvectorLieDegree.IsHostField H := by
  have hA := isAbelianGalois_host D
  obtain ⟨-, -, hdisc, hmov⟩ := PlaceInt.host_galois_discr_moves D H
  refine (HostRamif.isHostField_iff _ H).2 ⟨hA, fun l w hl hdv hw hlw => ?_⟩
  have h1 : l ∣ D.host.condN := hdisc l hl hdv
  have h2 : l ∈ D.host.small ∨ l = D.host.q ∨ l = D.host.d := (D.host.toHostRaw.dvd_condN_iff_small hl).1 h1
  refine ⟨fun h => ?_, fun h => (HostRamif.isSquare_iff H hl hw hlw h).1 ?_, fun h h3 => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (hmov l (Nat.mem_primeFactors.2 ⟨hl, h1, D.host.toHostRaw.condN_ne_zero⟩)).2 w hw.isPrime hlw
    exact hx' (h ▸ Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hx)
  · rcases h2 with h2 | rfl | h2
    · by_cases e2 : l = 2
      · subst e2
        exact FiniteField.isSquare_of_char_two (ZMod.ringChar_zmod_n 2) _
      · have := Fact.mk hl
        have := ZMod.isSquare_of_jacobiSym_eq_one
          (D.host.QS_split l hl e2 ((D.host.toHostRaw.mem_small_iff).1 h2).2)
        rw [hd]
        simpa using this
    · have := Fact.mk hl
      have := ZMod.isSquare_of_jacobiSym_eq_one D.host.hyp.2.2.2.2
      rw [hd]
      simpa using this
    · exact absurd (h2.trans hd.symm) h
  · obtain rfl : l = D.host.d := h.trans hd
    have hb : w ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hlw
      exact hl.ne_zero (by exact_mod_cast hlw)
    exact not_cube_dvd D ⟨w, hw.isPrime, hb⟩ hlw (Ideal.dvd_span_singleton.2 h3)

end Host

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_eigenBasis {S : Scheme.{0}} {T : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {t : SAB H (Sp R)}
    (n : SABMap t T x) {χ : 𝓞 E →+* R} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)} (hv : EigenvectorLieDegree.IsEigBasis t.act χ v) :
    ∃ u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G), FramedFlatCoordinates.IsEigenBasis T.act x χ u ∧ ∀ i, (v i).left ≫ n.φ = (u i).left := by
  have h := n.cart
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  have one : (1 : Over.mk x ⟶ T.G).left = η[t.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ t.G), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have hP : ∀ v : epsR R ⟶ t.G, EigenvectorLieDegree.IsEigVec t.act χ v ↔ FramedFlatCoordinates.IsEigenTangent T.act x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[t.G]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ t.act.act c) = e v ≫ T.act.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, n.act, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin m → (epsR R ⟶ t.G), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine ⟨fun i => e (v i), ⟨fun i => (hP _).1 (hv.1 i), fun w hw => ?_⟩, fun i => (he _).symm⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (hv.2 w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

variable {Y : Model Xo c β} {Xc : (Xo.XF c).Opens} {τ : E →+* ℂ}

def LiesOver {R : Type} [CommRing R] {j : c.F →+* R} (a : FramedFlatCoordinates.Framed Y Xc τ R j) (y : Sp R ⟶ Xo.XF c) : Prop :=
  a.x = y ≫ Y.jQ ∧ ∀ z, y z ∈ Xc

def IsFibre {R : Type} [CommRing R] {j : c.F →+* R} (a : FramedFlatCoordinates.Framed Y Xc τ R j) (t : SAB H (Sp R))
    (v : Fin Dw.p → (epsR R ⟶ t.G)) (w : Fin Dw.q → (epsR R ⟶ t.G)) : Prop :=
  ∃ n : SABMap t Y.t (a.x ≫ pullback.fst _ _),
    (∀ i, (v i).left ≫ n.φ = (a.v i).left) ∧ ∀ i, (w i).left ≫ n.φ = (a.w i).left

def NormAtAlgebraic (sig : FramedFlatCoordinates.Rule Y Xc τ) (R : (c.F →+* ℂ) → ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (j : c.F →+* L) (a : FramedFlatCoordinates.Framed Y Xc τ L j) (y : Sp L ⟶ Xo.XF c)
    (t : SAB H (Sp L)) (v : Fin Dw.p → (epsR L ⟶ t.G)) (w : Fin Dw.q → (epsR L ⟶ t.G)) (σ : L →+* ℂ) (N N' : ℝ),
    LiesOver a y → IsFibre a t v w → EigenvectorLieDegree.IsArchSq t.G t.PP.L v σ N → EigenvectorLieDegree.IsArchSq t.G t.PP.L w σ N' →
    ‖σ (sig L j a)‖ ^ 2 * (N / N') = R (σ.comp j) ^ 2

def ValAtAlgebraic (sig : FramedFlatCoordinates.Rule Y Xc τ) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (j : c.F →+* L) (a : FramedFlatCoordinates.Framed Y Xc τ L j) (y : Sp L ⟶ Xo.XF c)
    (t : SAB H (Sp L)) (v : Fin Dw.p → (epsR L ⟶ t.G)) (w : Fin Dw.q → (epsR L ⟶ t.G))
    (𝔭 : HeightOneSpectrum (𝓞 c.F)) (𝔓 : HeightOneSpectrum (𝓞 L)) (e : ℕ) (r r' : ℝ),
    LiesOver a y → IsFibre a t v w → (∀ z, 𝔓.valuation L (j z) = 𝔭.valuation c.F z ^ e) →
    EigenvectorLieDegree.IsLocOrd t.G v 𝔓 r → EigenvectorLieDegree.IsLocOrd t.G w 𝔓 r' →
    (vAdd 𝔓 (sig L j a) : ℝ) + (r - r' - Dw.q * (EigenvectorLieDegree.ordTwist H (EigenvectorLieDegree.embIn c j τ) 𝔓 : ℝ)) = e * ρ 𝔭

theorem adDeg_sq {K : Type} [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (R : (K →+* ℂ) → ℝ) :
    EigenvectorLieDegree.adDeg ρ (fun σ => R σ ^ 2) = FlatLine.lineDeg R ρ := by
  simp only [EigenvectorLieDegree.adDeg, FlatLine.lineDeg, lw, Real.log_pow, ← Finset.mul_sum, div_eq_mul_inv, ← _root_.mul_assoc]
  rw [← finsum_mul]
  push_cast
  ring

theorem adDeg_mul {K : Type} [Field K] [NumberField K] {s : K} (hs : s ≠ 0) {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (hρ : (Function.support ρ).Finite) {N : (K →+* ℂ) → ℝ} (hN : ∀ σ, 0 < N σ) :
    EigenvectorLieDegree.adDeg (fun 𝔭 => (vAdd 𝔭 s : ℝ) + ρ 𝔭) (fun σ => ‖σ s‖ ^ 2 * N σ) = EigenvectorLieDegree.adDeg ρ N := by
  have h := FlatLine.lineDeg_mul (r := fun σ : K →+* ℂ => ‖σ s‖) (r' := fun σ => √(N σ))
    (fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hs)) (fun σ => Real.sqrt_pos.2 (hN σ)) (FlatLine.finite_vAdd hs) hρ
  rw [FlatLine.lineDeg_num hs, zero_add, ← adDeg_sq, ← adDeg_sq] at h
  simp only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hN _).le] at h
  exact h

end Point

section Record

theorem finite_up {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}
    {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (h : IsUnder i π ε) {ρ : HeightOneSpectrum (𝓞 k) → ℝ} (hρ : (Function.support ρ).Finite) :
    (Function.support (up π ε ρ)).Finite := by
  choose s hs _ using h.sum
  refine (hρ.biUnion fun 𝔭 _ => (s 𝔭).finite_toSet).subset fun 𝔓 h𝔓 => ?_
  simp only [Set.mem_iUnion, Finset.mem_coe]
  exact ⟨π 𝔓, right_ne_zero_of_mul h𝔓, (hs _ _).2 rfl⟩

variable {D : D7} (large₂ : SizeData₂ D) {X : DivX D} (Lc : placeRankTwoOne.Loc D X)

end Record

end GlobalTheory.FlatRow
