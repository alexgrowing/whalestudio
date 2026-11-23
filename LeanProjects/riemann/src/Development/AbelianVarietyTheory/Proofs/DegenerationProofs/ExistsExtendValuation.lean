import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObjectStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesAlgebraicClosureCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcPoint

theorem spMap_cancel {V L K : Type} [CommRing V] [CommRing L] [CommRing K] {f : L →+* K} (hf : Function.Injective f)
    {x : Sp L ⟶ Sp V} {φ : V →+* L} (h : spMap f ≫ x = spMap (f.comp φ)) : x = spMap φ := by
  obtain ⟨α, rfl⟩ := Spec.map_surjective x
  have e : spMap (f.comp α.hom) = spMap (f.comp φ) := (spMap_comp' _ _).trans h
  have e' : f.comp α.hom = f.comp φ := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have e'' : α.hom = φ := RingHom.ext fun v => hf (RingHom.congr_fun e' v)
  rw [← e'']
  rfl

theorem exists_finite_factor {V K₀ K : Type} [CommRing V] [Field K₀] [Field K] [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K]
    {X : Scheme.{0}} (s : X ⟶ Sp V) [LocallyOfFiniteType s] (φ : V →+* K₀) (x : Sp K ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap K₀ K).comp φ)) :
    ∃ L : IntermediateField K₀ K, FiniteDimensional K₀ L ∧ ∃ x' : Sp L ⟶ X, spMap (algebraMap L K) ≫ x' = x ∧
      x' ≫ s = spMap ((algebraMap K₀ L).comp φ) := by
  obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues (pullback s (spMap φ)) K
    (pullback.lift x (spMap (algebraMap K₀ K)) (hx.trans (spMap_comp' _ _)))
  obtain ⟨L, hL, hE⟩ := h₃ K₀ (pullback.snd _ _) inferInstance (pullback.lift_snd _ _ _) inferInstance
  obtain ⟨y, hy⟩ := (h₂ L (algebraMap L K)).1 (fun z hz => ⟨⟨z, by rw [← hE] at hz; exact hz⟩, rfl⟩)
  have e : spMap (algebraMap L K) ≫ y ≫ pullback.fst _ _ = x := by rw [← Category.assoc, hy, pullback.lift_fst]
  refine ⟨L, hL, y ≫ pullback.fst _ _, e, spMap_cancel (f := algebraMap L K) (algebraMap L K).injective ?_⟩
  rw [← Category.assoc, e, hx]
  rfl

theorem exists_normal_order (A L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (g : A →+* R) (e : L ≃+* FractionRing R), Function.Injective g ∧ g.Finite ∧
      IsIntegrallyClosed R ∧ ∀ x, e (algebraMap (FractionRing A) L (algebraMap A _ x)) = algebraMap R _ (g x) := by
  letI : Algebra A L := ((algebraMap (FractionRing A) L).comp (algebraMap A _)).toAlgebra
  haveI : IsScalarTower A (FractionRing A) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A (FractionRing A) L _
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A (FractionRing A) L _
  refine ⟨integralClosure A L, inferInstance, inferInstance, algebraMap A _,
    (FractionRing.algEquiv (integralClosure A L) L).symm.toRingEquiv, fun x y h => ?_, hfin,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A), fun x => ?_⟩
  · exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective (congrArg Subtype.val h))
  · exact (FractionRing.algEquiv (integralClosure A L) L).symm.commutes (algebraMap A _ x)

theorem exists_extend {L K C : Type} [Field L] [Field K] [Algebra L K] [Algebra.IsAlgebraic L K] [Field C] [IsAlgClosed C]
    (f : L →+* C) : ∃ g : K →+* C, ∀ x, g (algebraMap L K x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : K →ₐ[L] C), fun x => (IsAlgClosed.lift : K →ₐ[L] C).commutes x⟩

theorem exists_extend_valuation {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (b : V →+* K) : ∃ f : F →+* K, ∀ x : V, f x = b x := by
  have hb : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have ha : IsAlgebraic ℤ (x : F) := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have ha' : IsAlgebraic ℤ x := (isAlgebraic_algHom_iff V.subtype.toIntAlgHom Subtype.val_injective).1 ha
    refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker b) h0 hx ha' (eq_bot_iff.2 fun n hn => ?_)
    simpa using hn
  exact ⟨IsFractionRing.lift hb, fun x => IsFractionRing.lift_algebraMap hb x⟩

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) : x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rwa [map_pow, pow_le_one_iff hn] at h

theorem exists_prime_unit (O : Type) [CommRing O] [IsLocalRing O] {d : ℕ} (hd : d ≠ 0) :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) ∧ ¬ n ∣ d := by
  obtain ⟨p, hp, pp⟩ := Nat.exists_infinite_primes (d + 3)
  obtain ⟨q, hq, qp⟩ := Nat.exists_infinite_primes (p + 1)
  have key : ∀ n : ℕ, n.Prime → d + 3 ≤ n → IsUnit (n : O) → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) ∧ ¬ n ∣ d :=
    fun n hn h hu => ⟨n, hn, hn.odd_of_ne_two (by omega), hu, fun h' => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) h'; omega⟩
  obtain ⟨a, b, hab⟩ : IsCoprime (p : O) (q : O) :=
    Nat.Coprime.cast ((Nat.coprime_primes pp qp).2 (by omega))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key p pp hp (isUnit_of_mul_isUnit_right h)
  · exact key q qp (by omega) (isUnit_of_mul_isUnit_right h)

theorem valuation_comap_eq_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') (S : ValuationSubring K') (x : K) :
    (S.comap f).valuation x = 1 ↔ S.valuation (f x) = 1 := by
  have key : ∀ {F : Type} [Field F] (T : ValuationSubring F) (y : F), T.valuation y = 1 ↔ y ≠ 0 ∧ y ∈ T ∧ y⁻¹ ∈ T := by
    intro F _ T y
    rw [← T.valuation_le_one_iff, ← T.valuation_le_one_iff, map_inv₀]
    constructor
    · intro h
      refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
      rw [h0, map_zero] at h
      exact zero_ne_one h
    · rintro ⟨h0, h₁, h₂⟩
      have : 0 < T.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 h0)
      exact le_antisymm h₁ ((inv_le_one₀ this).1 h₂)
  rw [key, key, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, map_ne_zero]

section
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem summable_txT (h : N.Int q) {m : ℕ} (hm : m ≠ 0) (p : N.QT (m ^ 2)) : Summable (N.txT m p) := by
  have hp : p.1.2 ^ m ^ 2 = N.io p.1.1.toAdd := p.2
  exact (summable_vt_QT C N q h m hm ⟨(p.1.1, p.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, ← sq, hp]⟩).mul_left _

theorem summable_evT (h : N.Int q) {m j : ℕ} (hm : m ≠ 0) (hj : j ≠ 0) (p : N.QT (m ^ 2)) (z : N.QT j) :
    Summable (N.evT m p z.1.2) := by
  have hp : p.1.2 ^ m ^ 2 = N.io p.1.1.toAdd := p.2
  have hz : z.1.2 ^ j = N.io z.1.1.toAdd := z.2
  refine (summable_vt_QT C N q h (m * j) (mul_ne_zero hm hj)
    ⟨(Multiplicative.ofAdd (m ^ 2 • z.1.1.toAdd + j • p.1.1.toAdd), (z.1.2 * p.1.2) ^ m), ?_⟩).mul_left _
  rw [NumD.mem_QT, toAdd_ofAdd, N.io_add, N.io_nsmul, N.io_nsmul, ← hp, ← hz, ← pow_mul, ← pow_mul, ← pow_mul, mul_pow]
  congr 2 <;> ring
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K] [CharZero K]

theorem coord_scale (hL : Laws) (o : Full D K) {m : ℕ} (hm : Odd m) {z : baseOver (Sp K) ⟶ o.P.A} {v v' : D.La → K}
    (s : Kˣ) (hs : ∀ x, v x = s * v' x) (h : o.Coord m z v) : o.Coord m z v' := by
  haveI := o.closed
  have hc := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K _ o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
    (o.I.ev (m ^ 2)) fun x => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨x, rfl⟩
  refine (hc.2.1 z _ _ h).2 ⟨s⁻¹, funext fun x => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Units.inv_mul_cancel_left]

theorem theta_scale (hL : Laws) (o : Full D K) {m : ℕ} (hm : Odd m) {v v' : D.La → K}
    (s : Kˣ) (hs : ∀ x, v x = s * v' x) (h : o.Theta m v) : o.Theta m v' := by
  haveI := o.closed
  have hc := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K _ o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
    (o.I.ev (m ^ 2)) fun x => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨x, rfl⟩
  exact (hc.2.2.1 _).2 (coord_scale hL o hm s hs ((hc.2.2.1 _).1 h))
end

theorem realises_of_has : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → AllA fun {_} _ _ _ {_} {D} {_} {_} {_} {_} _ {O'} _ _ {_} a =>
    ∀ (K : Type) [Field K] [CharZero K] [Algebra (FractionRing O') K] (i : PowerSeries O' →+* K) (S : Ser a K i) (o : Full D K),
      S.Has o → AllC (RingHom.id _) i fun {C} _ _ gam u => ∃ (A : Lift a C) (r : ℕ → Cˣ) (o' : Full D C),
        A.ν.IntN ∧ Roots u r ∧ FullExt gam o o' ∧ Realises o' A.arc A.be u r := by
  intro hV h6 hU hH hT hE hA E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ i S o ho C _ _ _ _ _ gam u h₁ h₂ h₃ h₄
  have hL := hV.1.1
  haveI := o.closed
  haveI : CharZero C := (RingHom.charZero_iff gam.injective).1 inferInstance
  obtain ⟨A, r, hint, ⟨-, hAρ, hAζ, -⟩, hr', hser⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hr : Roots u r := ⟨Units.ext ((hr' 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n m hn hm => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hr', hr', ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n m hn hm])⟩
  obtain ⟨o', hext, hθ, hco⟩ := GlobalTheory.T.fullTorsionPolarizedCMObject_extends_algClosed hV h6 hU hH hT hE hA E H D K C gam o
  have hO : CExt O' ⊥ C := ⟨fun x => by rw [h₁]; exact h₂ _, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  obtain ⟨q, hq, -⟩ := (UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hO A hint).2.2 u h₄
  refine ⟨A, r, o', hint, hr, hext, hr, ?_, fun n hn => Units.ext ?_, fun m hm p hp => ?_⟩
  · rw [hext.1, ho.1]; exact hAρ
  · rw [hext.2.1 n hn, ho.2.1 n hn]; exact hAζ n hn
  obtain ⟨⟨s, hs⟩, hw⟩ := hser m hm p hp
  refine ⟨fun x => summable_txT hq hm.pos.ne' _, theta_scale hL o' hm s hs (hθ _ _ (ho.2.2 m hm).1), fun j hj z t ht => ?_⟩
  obtain ⟨s', hs'⟩ := hw j hj z t ht
  exact ⟨fun x => summable_evT hq hm.pos.ne' hj.ne' _ _,
    coord_scale hL o' hm s' hs' (hco m j z _ hj ((ho.2.2 m hm).2 j hj z))⟩

theorem intFam_map {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {R R' K K' : Type}
    [CommRing R] [CommRing R'] [Field K] [Field K'] {u : R} {i : R →+* K} {s : ℕ} {v : D.La → K}
    (h : IntFam (D := D) u i s v) (g : R →+* R') (i' : R' →+* K') (f : K →+* K') (e : ∀ x, f (i x) = i' (g x)) :
    IntFam (D := D) (g u) i' s fun x => f (v x) := by
  intro S hS
  obtain ⟨h₁, h₂, h₃⟩ := h (S.comap f) fun r => by rw [ValuationSubring.mem_comap, e]; exact hS _
  simp only [valuation_comap_eq_one, e] at h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

theorem exists_point : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g ∧ g.Finite ∧ IsIntegrallyClosed R₁ ∧ y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ RealAt Y a g y₁ ∧ ThetaInt Y g y₁ := by
  intro hV h6 hU hH hT hE hA E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb
  have hloc : IsLocalRing O' ∧ IsPrincipalIdealRing O' := by
    rcases hb with h | h
    · letI := h.1.toField
      exact ⟨inferInstance, inferInstance⟩
    · haveI := h.1
      exact ⟨inferInstance, inferInstance⟩
  haveI := hloc.1
  haveI := hloc.2
  haveI : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  let K₀ := FractionRing (PowerSeries O')
  let K := AlgebraicClosure K₀
  haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
    IsFractionRing.injective (PowerSeries O') K₀ ((algebraMap K₀ K).injective h)
  haveI : Algebra.IsAlgebraic (PowerSeries O') K :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K₀)).2 inferInstance
  have hC : Function.Injective ((algebraMap (PowerSeries O') K).comp (PowerSeries.C (R := O'))) :=
    fun x y h => PowerSeries.C_injective (FaithfulSMul.algebraMap_injective (PowerSeries O') K h)
  letI : Algebra (FractionRing O') K := (IsFractionRing.lift hC).toAlgebra
  have hK : ∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x) :=
    fun x => IsFractionRing.lift_algebraMap hC x
  obtain ⟨S⟩ := GlobalTheory.T.exists_arcSeries_integral_algebraic_over_powerSeries hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK
  obtain ⟨n, hn, hodd, hu, hd⟩ := exists_prime_unit O' H.d_prime.ne_zero
  obtain ⟨o₀, hρ₀, h₀⟩ := GlobalTheory.T.thetaPoints_allPrimePowerLevels_of_single_object hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n hn hodd fun j hj =>
    GlobalTheory.T.exists_object_with_thetaPoint_of_degenerationSeries hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n j hn hodd hu hd hj
  obtain ⟨o, ho⟩ := GlobalTheory.T.power_series_algebraic_closure_compatible hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n hn hodd hu o₀ hρ₀ h₀
  haveI := c.fin
  obtain ⟨bF, hbF⟩ := exists_extend_valuation (c.V W₀)
    ((algebraMap (PowerSeries O') K₀).comp ((PowerSeries.C (R := O')).comp b))
  have hbK : ∀ x : c.V W₀, (algebraMap K₀ K).comp bF x = algebraMap (FractionRing O') K (algebraMap O' _ (b x)) :=
    fun x => by rw [hK, RingHom.comp_apply, hbF]; rfl
  obtain ⟨hpt, -, hext⟩ := GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hH hT hE hA E H D l Xo c W₀ Y K ((algebraMap K₀ K).comp bF)
  obtain ⟨y, ⟨hy, hfull⟩, -⟩ := hpt o (fun r hr => by
      have hm : r ∈ c.V W₀ := mem_of_pow_mem _ two_ne_zero (by
        have : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [hr] using H.sqrt_neg_disc_sq)
        rw [this]
        exact neg_mem (natCast_mem _ _))
      exact ho.1.trans ((S.A.ρ_eq ⟨r, hm⟩ hr).trans (hbK ⟨r, hm⟩).symm))
    (fun z hz => by
      have hm : z ∈ c.V W₀ := mem_of_pow_mem _ l.A_pos.ne' (by
        have : z ^ l.A = 1 := Subtype.ext (by
          simpa [hz, zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one)
        rw [this]
        exact one_mem _)
      rw [ho.2.1 _ l.A_pos]
      exact (S.A.ζ_eq ⟨z, hm⟩ hz).trans (hbK ⟨z, hm⟩).symm)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨L, hLf, y', hy', hy's⟩ := exists_finite_factor (pullback.snd Xo.s _) bF y hy
  obtain ⟨R₁, _, _, g, e, hgi, hgf, hRn, he⟩ := exists_normal_order (PowerSeries O') L
  have hover : (spMap (e : L →+* FractionRing R₁) ≫ y') ≫ Y.j ≫ Y.s =
      jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have e₁ : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W₀).subtype := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [e₁, Category.assoc, ← Category.assoc y', hy's, ← spMap_comp', ← spMap_comp', ← spMap_comp', ← spMap_comp']
    refine Eq.trans (congrArg spMap (RingHom.ext fun x => ?_)) (spMap_comp' _ (algebraMap R₁ _))
    exact (congrArg (fun t => e (algebraMap K₀ L t)) (hbF x)).trans (he _)
  have hx : ∀ (C : Type) [Field C] [IsAlgClosed C] (gam : FractionRing R₁ →+* C), ∃ f : K →+* C,
      spMap f ≫ y = spMap gam ≫ spMap (e : L →+* FractionRing R₁) ≫ y' ∧
      ∀ x, f (algebraMap (PowerSeries O') K x) = gam (algebraMap R₁ _ (g x)) := by
    intro C _ _ gam
    obtain ⟨f, hf⟩ := exists_extend (K := K) (gam.comp (e : L →+* FractionRing R₁))
    refine ⟨f, ?_, fun x => ?_⟩
    · rw [← hy', ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
      exact congrArg (fun t => spMap t ≫ y') (RingHom.ext hf)
    · rw [← he]
      exact hf (algebraMap K₀ L (algebraMap _ K₀ x))
  refine ⟨R₁, inferInstance, inferInstance, g, _, hgi, hgf, hRn, hover, ⟨⟨hgi, hgf, hover⟩, ?_⟩, ?_⟩
  · intro C _ _ _ _ _ gam u h₁ h₂ h₃ h₄
    obtain ⟨f, hf, hf'⟩ := hx C gam
    obtain ⟨A, r, o', p₁, p₂, p₃, p₄⟩ := realises_of_has hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K _ S o ho C f u
      (fun x => (h₁ x).trans (hf' _).symm) (fun x => by rw [hf']; exact h₂ _) (h₃.trans (hf' _).symm) h₄
    exact ⟨A, r, o', p₁, p₂, hf ▸ hext C f y o o' hfull p₃, p₄⟩
  · obtain ⟨f, hf, hf'⟩ := hx (AlgebraicClosure (FractionRing R₁)) (algebraMap _ _)
    obtain ⟨o', p₁, p₂, -⟩ := GlobalTheory.T.fullTorsionPolarizedCMObject_extends_algClosed hV h6 hU hH hT hE hA E H D K _ f o
    exact ⟨o', hf ▸ hext _ f y o o' hfull p₁, fun n j hn ho' hu hj =>
      ⟨_, p₂ _ _ (ho.2.2 _ ho'.pow).1, intFam_map (S.int n j hn ho' hu hj) g _ f hf'⟩⟩

end GlobalTheory.ArcPoint
