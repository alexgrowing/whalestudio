import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmallStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomComplexOfCountableOfRelations
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AevalArcTxEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcIdentity

theorem exists_form {O O' : Type} [CommRing O] [CommRing O'] {N : NumD O} {N' : NumD O'} (e : N.X ≃+ N'.X) {k : ℕ}
    (β : N'.Form k) : ∃ b : N.Form k, ∀ y z, b.be y z = β.be (e y) (e z) := by
  refine ⟨⟨β.be.compl₁₂ e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap, fun y z => ?_,
    fun y hy => ?_, fun y z => ?_⟩, fun y z => ?_⟩
  · simpa using β.symm (e y) (e z)
  · simpa using β.pos (e y) (fun h => hy (e.injective (by rw [h, map_zero])))
  · simpa using β.dvd (e y) (e z)
  · simp

theorem arcTx_qEq {O : Type} [CommRing O] (N : NumD O) (be : LinearMap.BilinForm ℤ N.X) {m : ℕ} (ho : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.arcTx be m p' = N.arcTx be m p := by
  obtain ⟨z, h1, h2⟩ := h
  ext n
  simp only [NumD.arcTx, PowerSeries.coeff_mk]
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (m • z))]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • χ = p.1.1.toAdd + m • (χ + m • z) := by
    rw [h1, smul_add, smul_smul, ← pow_two]
    abel
  simp only [Equiv.coe_addRight, hx, (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m ho p p' χ).1 z h1 h2]

private theorem map_finsum_of_injective' {α M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (φ : M →+ M')
    (hφ : Function.Injective φ) (g : α → M) : φ (∑ᶠ a, g a) = ∑ᶠ a, φ (g a) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum φ h
  · have hs : Function.support (fun a => φ (g a)) = Function.support g := by
      ext a
      simp only [Function.mem_support, ne_eq]
      exact ⟨fun h1 h2 => h1 (by rw [h2, map_zero]), fun h1 h2 => h1 (hφ (by rw [h2, map_zero]))⟩
    have h' : (Function.support (fun a => φ (g a))).Infinite := by
      rw [hs]
      exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem unit_mul_map_finsum {α F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (g : α → F) :
    (c : F') * f (∑ᶠ a, g a) = ∑ᶠ a, (c : F') * f (g a) := by
  refine map_finsum_of_injective' ((AddMonoidHom.mulLeft (c : F')).comp f.toAddMonoidHom) ?_ g
  intro a b hab
  have hab' : (c : F') * f a = (c : F') * f b := hab
  exact f.injective (mul_left_cancel₀ c.ne_zero hab')

private theorem unit_mul_map_finsum_prop {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (P : Prop)
    (x : F) : (c : F') * f (∑ᶠ (_ : P), x) = ∑ᶠ (_ : P), (c : F') * f x := by
  classical
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem arcTx_hom {F F' : Type} [Field F] [Field F'] {f : F →+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom f N N')
    (be : LinearMap.BilinForm ℤ N.X) (be' : LinearMap.BilinForm ℤ N'.X) (hb : ∀ y z, be y z = be' (I.e y) (I.e z))
    {m : ℕ} (ho : Odd m) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h1 : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (h2 : I.Rel p.1.2 p'.1.2) :
    N'.arcTx be' m p' = PowerSeries.C (I.lam : F') * PowerSeries.map f (N.arcTx be m p) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp only [NumD.arcTx, PowerSeries.coeff_mk, unit_mul_map_finsum f I.lam, unit_mul_map_finsum_prop f I.lam]
  conv_lhs => rw [← finsum_comp_equiv I.e.toEquiv]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • I.e χ = I.e (p.1.1.toAdd + m • χ) := by
    rw [h1, map_add, map_nsmul]
  have hχ : I.e.toEquiv χ = I.e χ := rfl
  rw [hχ]
  simp only [hx, ← hb, I.txT_eq ho p p' h1 h2 χ]

private theorem eval2_smul_of_isHomogeneous {J S T : Type*} [CommSemiring S] [CommSemiring T] (g : S →+* T) (c : T)
    (w : J → T) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun x => c * w x) G = c ^ d * MvPolynomial.eval₂ g w G := by
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hG.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem aeval_smul_map {J S F F' : Type} [CommRing S] [CommRing F] [CommRing F'] (f : F →+* F') (c : S →+* F)
    (l : F') (v : J → PowerSeries F) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval (fun x => PowerSeries.C l * PowerSeries.map f (v x)) (MvPolynomial.map (f.comp c) G) =
      PowerSeries.C l ^ d * PowerSeries.map f (MvPolynomial.aeval v (MvPolynomial.map c G)) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
    eval2_smul_of_isHomogeneous _ _ (fun x => PowerSeries.map f (v x)) hG, MvPolynomial.eval₂_comp_left]
  have hr : (PowerSeries.map f).comp ((algebraMap F (PowerSeries F)).comp c) =
      (algebraMap F' (PowerSeries F')).comp (f.comp c) :=
    RingHom.ext fun a => by simp [PowerSeries.map_C]
  rw [hr]
  rfl

theorem cf_comp {F F' : Type} [CommRing F] [CommRing F'] (f : F →+* F') (a b : F) :
    cf (f a) (f b) = f.comp (cf a b) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
  {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F']

theorem over_iff {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : A.Over f A') :
    ∃ e : A.N.X ≃+ A'.N.X, ∀ (k : ℕ) (β : A.N.Form k) (β' : A'.N.Form k), (∀ y z, β.be y z = β'.be (e y) (e z)) →
      (A.Bal β ↔ A'.Bal β') ∧ ∀ m : ℕ, Odd m → ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ),
        G.IsHomogeneous d →
        (MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x))
            (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 ↔
          MvPolynomial.aeval (fun x => A'.N.arcTx β'.be m (A'.q _ x))
            (MvPolynomial.map (cf (A'.I.ζ (m ^ 2) : F') A'.ρ) G) = 0) := by
  obtain ⟨I, hρ, hζ, hact, hq⟩ := h
  refine ⟨I.e, fun k β β' hbe => ⟨?_, fun m hm G d hG => ?_⟩⟩
  · constructor
    · intro hB a y' z'
      obtain ⟨y, rfl⟩ := I.e.surjective y'
      obtain ⟨z, rfl⟩ := I.e.surjective z'
      have h1 := hB a y z
      rw [hbe, hbe, hact, hact] at h1
      exact h1
    · intro hB a y z
      rw [hbe, hbe, hact, hact]
      exact hB _ _ _
  · have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
    have hv : ∀ x, A'.N.arcTx β'.be m (A'.q _ x) =
        PowerSeries.C (I.lam : F') * PowerSeries.map f (A.N.arcTx β.be m (A.q (m ^ 2) x)) := by
      intro x
      obtain ⟨p', h1, h2, h3⟩ := hq (m ^ 2) x hpos
      rw [arcTx_qEq A'.N β'.be hm h3]
      exact arcTx_hom I β.be β'.be hbe hm h1 h2
    have hcf : cf (A'.I.ζ (m ^ 2) : F') A'.ρ = f.comp (cf (A.I.ζ (m ^ 2) : F) A.ρ) := by
      rw [← hρ, ← hζ _ hpos, cf_comp]
    simp only [hv, hcf]
    rw [aeval_smul_map f (cf (A.I.ζ (m ^ 2) : F) A.ρ) (I.lam : F') (fun x => A.N.arcTx β.be m (A.q (m ^ 2) x)) hG]
    have hC : PowerSeries.C (I.lam : F') ^ d ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr I.lam.ne_zero)
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      have h0' := (mul_eq_zero.mp h0).resolve_left hC
      exact PowerSeries.map_injective f f.injective (by rw [h0', map_zero])

theorem aeval_arcTx_eq_zero_of_vanishC : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  intro hHV h6 hU hE hT hEnd hTU
  have hHV' := hHV
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := hHV'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hWp := GlobalTheory.WeilValues.weil_eq_values hGt (GlobalTheory.Ex.brFam hL hL2)
  have hC4400 := GlobalTheory.T.exists_thetaPoint_complexDegeneration_small hHV h6 hU hE hT hEnd hTU
  have hdown := GlobalTheory.FieldPull.exists_countable_model hL hGt hWp
  have hup := GlobalTheory.ArcExt.exists_arcF_over hL hGt hWp
  unfold AllD at hC4400 hdown hup ⊢
  intro E _ _ _ H D R _ _ F _ _ _ _ A k β hB m hmk hm hC G hV
  obtain ⟨-, ⟨d, hG⟩, hVan⟩ := hV
  have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
  obtain ⟨R₁, F₁, _, _, _, _, _, _, f, A₁, hA₁⟩ := hdown E H D R F A
  haveI : CharZero F₁ := A₁.charZero
  obtain ⟨e₁, he₁⟩ := over_iff hA₁
  obtain ⟨β₁, hβ₁⟩ := exists_form e₁ β
  have h1 := he₁ k β₁ β hβ₁
  rw [← h1.2 m hm G d hG]
  obtain ⟨I₁, hρ₁, hζ₁, _, _⟩ := hA₁
  have hC₁ : Compat H (m ^ 2) (A₁.I.ζ (m ^ 2) : F₁) A₁.ρ := by
    intro c hc
    have h0 := hC c hc
    rw [← hρ₁, ← hζ₁ _ hpos, cf_comp, RingHom.comp_apply] at h0
    exact f.injective (by rw [h0, map_zero])
  have halg : ∀ i, IsAlgebraic ℚ (![zeta (m ^ 2), H.rt0] i) := by
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (zeta (m ^ 2))
      have hz : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := by
        unfold zeta
        exact Complex.isPrimitiveRoot_exp _ hpos.ne'
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow hpos ?_)
      rw [hz.pow_eq_one]
      exact isIntegral_one
    · show IsAlgebraic ℚ H.rt0
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow (n := 2) two_pos ?_)
      rw [H.sqrt_neg_disc_sq]
      have hd := isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := -(H.d : ℚ))
      simpa using hd
  obtain ⟨g, hg⟩ := GlobalTheory.exists_ringHom_complex_of_countable_of_relations F₁
    ![(A₁.I.ζ (m ^ 2) : F₁), A₁.ρ] ![zeta (m ^ 2), H.rt0] halg hC₁
  have hg0 : g (A₁.I.ζ (m ^ 2) : F₁) = zeta (m ^ 2) := by simpa using hg 0
  have hg1 : g A₁.ρ = H.rt0 := by simpa using hg 1
  letI : Algebra (FractionRing R₁) ℂ := (g.comp (algebraMap (FractionRing R₁) F₁)).toAlgebra
  obtain ⟨A₂, -, hA₂⟩ := hup E H D R₁ F₁ ℂ g (fun x => rfl) A₁
  obtain ⟨e₂, he₂⟩ := over_iff hA₂
  obtain ⟨β₂, hβ₂⟩ := exists_form e₂.symm β₁
  have hb12 : ∀ y z, β₁.be y z = β₂.be (e₂ y) (e₂ z) := by
    intro y z
    rw [hβ₂]
    simp
  have h2 := he₂ k β₁ β₂ hb12
  rw [h2.2 m hm G d hG]
  obtain ⟨I₂, hρ₂, hζ₂, _, _⟩ := hA₂
  have hρ₂' : A₂.ρ = H.rt0 := by rw [← hρ₂, hg1]
  have hζ₂' : (A₂.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) := by rw [← hζ₂ _ hpos, hg0]
  have hB₂ : A₂.Bal β₂ := h2.1.mp (h1.1.mpr hB)
  obtain ⟨ε, hε, hsmall⟩ := hC4400 E H D R₁ A₂ hρ₂' k β₂ hB₂ m hmk hm
  rw [hζ₂', hρ₂']
  refine GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero A₂.N k β₂ m hmk hm D.La (fun x => A₂.q _ x) _ ε hε
    fun u hu => ⟨(hsmall u hu).1, ?_⟩
  obtain ⟨o, hoρ, hoζ, hθ⟩ := (hsmall u hu).2
  rw [MvPolynomial.eval_map]
  exact hVan o hoρ (by rw [hoζ]; exact hζ₂') _ hθ

end GlobalTheory.ArcIdentity
