import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibresStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOfSameRatios

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecLevel

theorem eq_zero_of_rational_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((Points.le_preimage_basicOpen_iff _ hU f).1 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem fib_fst {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.fst G.hom y = x.left := pullback.lift_fst _ _ _

theorem sec_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (m : ℕ)
    (u : SecP P.L (pullback.fst P.A.hom y) m)
    (h : ∀ (x : Over.mk y ⟶ P.A) j, ⊤ ≤ x.left ⁻¹ᵁ P.L.U j → ArcPts.sval u (fib x) j = 0) (i) : u.f i = 0 := by
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (pullback P.A.hom y) :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral y _ _
      (IsPullback.of_hasPullback P.A.hom y)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine eq_zero_of_rational_points (pullback.snd P.A.hom y) _ _ fun x hx hU => ?_
  let a : Over.mk y ⟶ P.A := Over.homMk (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
    exact Category.id_comp _)
  have e : fib a = x := by
    apply pullback.hom_ext
    · exact fib_fst a
    · rw [hx]; exact pullback.lift_snd _ _ _
  have := h a j fun p hp => Set.mem_iInter.1 (hU hp) 0
  rw [e] at this
  exact this

theorem pow_mem_Theta {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {th : (Fin A.gB → ℂ) → ℂ}
    (h : th ∈ A.Theta 1 0) (n : ℕ) : th ^ (n + 1) ∈ A.Theta (n + 1) 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [pow_succ] using A.mul_mem_Theta ih h

theorem map_nsmul_eq_pow {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v')
    (n : ℕ) (v : V) : x (n • v) = x v ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, SpecGroup.map_zero_eq_one x h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem left_toUnit_comp {S : Scheme.{0}} {G T T' : Over S} (ξ : 𝟙_ (Over S) ⟶ G) (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom) : (toUnit T' ≫ ξ).left = r ≫ (toUnit T ≫ ξ).left := by
  rw [Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc, hr]

theorem exists_germ_shift {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (Γ : Germs) (k : ℕ) [NeZero k] :
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → ∀ la : A.La, (∀ α, (k : ℤ) ∣ A.be la.y α) → ∀ α, ∀ th ∈ A.Theta k α, ∀ z,
      ∃ F : Γ.R w, IsFShift A k α th la z F ∧ Γ.ev w F = A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun w hw la hla α th hth z => ?_⟩
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  obtain ⟨hm, hev⟩ := ((h₀ T₀ le_rfl k).1 _ _ (A.shift_mem_Theta hth la)).1 z
  refine ⟨Subalgebra.inclusion (Γ.le T₀ w hw)
    (⟨_, Conv.single_mem_halfRing T₀ (A.be la.y α / k) (Complex.exp (A.lin la z))⟩ * ⟨_, hm⟩),
    ⟨⟨NeZero.ne k, hla α⟩, fun n => ?_⟩, ?_⟩
  · rw [Subalgebra.coe_inclusion, MulMemClass.coe_mul,
      ← A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm, AnArc.coeff_FSumShift]
    refine (finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_).symm
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  · rw [Γ.ev_eq T₀ w hw, map_mul, hev w hw, Conv.ev_single hw, ← AnArc.e_mul_intCast]
    obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

theorem level_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (k : ℕ) [NeZero k], ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → Function.Surjective (Ψ.pi w) → (∀ la, Ψ.pi w (A.Pw w la) = 1) → ∀ (ξ : 𝟙_ (Over S) ⟶ o.t.G) (la : A.La), ξ ^ k = 1 → Φ.LevelPt k (toUnit _ ≫ ξ) la → toUnit _ ≫ ξ = Ψ.pi w ((k : ℂ)⁻¹ • A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR k _
  obtain ⟨T₁, hT₁, hsec⟩ := GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR k
  obtain ⟨T₂, hsh⟩ := exists_germ_shift A Γ k
  obtain ⟨T₃, hT₃⟩ := A.exists_isConvLine
  refine ⟨max T₁ (max T₂ T₃), hT₁.trans (le_max_left _ _), fun w hw' surj per ξ la hξ hlev => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ : T₁ < w.im ∧ T₂ < w.im ∧ T₃ < w.im := by simpa using hw'
  have hw : Ψ.T < w.im := lt_of_le_of_lt hT₁ h₁
  obtain ⟨σt, hσt, σ₀, hσ₀, hval, hspan⟩ := hsec w hw h₁
  have hk : k ≠ 0 := NeZero.ne k
  obtain ⟨θ, hθ, hθ0⟩ := hA.2
  have hθk : θ ^ k ∈ A.Theta k 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact pow_mem_Theta A hθ n
  have hθk0 : θ ^ k ≠ 0 := fun e => hθ0 (funext fun z => pow_eq_zero_iff hk |>.1 (congrFun e z))
  have hv : ∀ α, ∀ th ∈ A.Theta k α, ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v)) j = A.Sum k α th w v * Ψ.fr w j v ^ k := fun α th hth v j hj =>
    hval α th hth v j (by rw [fib_fst]; exact hj)
  refine LevelUnique.torsion_eq_of_same_ratios hL hL2 E H D l B bb S s o ℂ (Ψ.yw w) A.V (Ψ.pi w) k _ _
    (fun _ => True) (σ₀ 0 (θ ^ k)) (Nat.one_le_iff_ne_zero.2 hk) ?_ ?_ (fun m _ u hu => ?_) ?_
    (fun _ _ _ _ => trivial) fun v _ t₁ t₂ j j' hj hj' => ?_
  · rw [← MonObj.comp_pow, hξ, MonObj.comp_one]
  · rw [← map_nsmul_eq_pow _ (SpecGroup.pi_add Ψ hw), ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk), one_smul, per]
  · refine sec_eq_zero (objPolAV o) (Ψ.yw w) m u fun x j hj => ?_
    obtain ⟨v, rfl⟩ := surj x
    exact hu v j hj
  · obtain ⟨v, hv0⟩ := A.exists_Sum_ne_zero hk 0 hθk0 fun z => AnArc.summable_term hT₃ hk hθk h₃ (0, z)
    obtain ⟨j, hj⟩ := exists_chart o.t.PP.isLB ((Ψ.pi w v).left (default : PrimeSpectrum ℂ))
    have hj' := (HolHom.le_preimage_iff (Ψ.pi w v).left _).2 hj
    refine ⟨fun _ => j, fun e => ?_⟩
    have h0 : ArcPts.sval (σ₀ 0 (θ ^ k)) (fib (Ψ.pi w v)) j = 0 := by
      rw [ArcPts.sval, e]
      refine Points.valR_zero _ _ fun p hp => Set.mem_iInter.2 fun _ => ?_
      have := hj' hp
      rw [← fib_fst] at this
      exact this
    rw [hv 0 _ hθk v j hj'] at h0
    exact mul_ne_zero hv0 (pow_ne_zero _ ((SpecGroup.pi_frm Ψ hw v).1 j hj').ne_zero) h0
  · have e₀ : (Ψ.pi w v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.ev w).toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (SpecGroup.ev_base Ψ hw) (Ψ.pi_eq w hw v)
        (left_toUnit_comp ξ _ (SpecGroup.ev_base Ψ hw))
    have e₁ : (Φ.x v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.R w).val.toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk y) _ (SpecGroup.val_base Ψ hw) (Ψ.xt_gen w hw v).symm
        (left_toUnit_comp ξ _ (SpecGroup.val_base Ψ hw))
    have ht : ⊤ ≤ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j :=
      SpecGroup.le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ (e₀ ▸ hj)
    have hg : ⊤ ≤ (Φ.x v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j := by
      rw [e₁]
      exact fun p _ => ht (x := spMap (Γ.R w).val.toRingHom p) trivial
    have key : ∀ α α', ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α',
        ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α' th' w (v + (k : ℂ)⁻¹ • A.Pw w la) =
        ArcPts.sval (σ₀ α' th') (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) := by
      intro α α' th hth th' hth'
      obtain ⟨F, hF, hFe⟩ := hsh w h₂ la hlev.dvd α th hth v
      obtain ⟨F', hF', hFe'⟩ := hsh w h₂ la hlev.dvd α' th' hth' v
      have h := hlev.2.2 α α' th hth th' hth' v F F' j hF hF' hg
      rw [← hσt α th hth _ _ j e₁.symm ht, ← hσt α' th' hth' _ _ j e₁.symm ht, ← MulMemClass.coe_mul,
        ← MulMemClass.coe_mul, Subtype.val_inj] at h
      rw [hσ₀ α th _ _ j e₀ hj, hσ₀ α' th' _ _ j e₀ hj, ← hFe, ← hFe', ← map_mul, ← map_mul, h]
    obtain ⟨n₁, r₁, α₁, θ₁, m₁, s₁⟩ := hspan t₁
    obtain ⟨n₂, r₂, α₂, θ₂, m₂, s₂⟩ := hspan t₂
    rw [← SpecGroup.pi_add Ψ hw] at hj' ⊢
    rw [s₁ _ j hj, s₂ _ j hj, s₁ _ j' hj', s₂ _ j' hj', Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hv _ _ (m₁ b) _ j' hj', hv _ _ (m₂ a) _ j' hj']
    linear_combination (r₁ b * r₂ a * Ψ.fr w j' (v + (k : ℂ)⁻¹ • A.Pw w la) ^ k) * key _ _ _ (m₁ b) _ (m₂ a)

end GlobalTheory.SpecLevel
