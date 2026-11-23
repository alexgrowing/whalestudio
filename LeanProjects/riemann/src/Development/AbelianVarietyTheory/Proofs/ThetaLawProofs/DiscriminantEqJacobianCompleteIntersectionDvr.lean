import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacEqUnitMulDetPderiv
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MulVecCongrDeg
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsCxOfFactor
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SpanModEquationsLift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPowSpanXLeOfDense
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDApplyMap
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCombSubMemSupPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDExactGeneric
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFactorAssociatedJacobian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.DiscrJacGlobal
open EtBaseChange

theorem top_le_of_closedPoint {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) {U : X.Opens}
    (h : w (IsLocalRing.closedPoint T) ∈ U) : ⊤ ≤ w ⁻¹ᵁ U :=
  fun p _ => ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open U.isOpen h

theorem exists_unit_chart {R T : Type} [CommRing R] [CommRing T] (x : KeyIn R) (w : Sp T ⟶ x.P.A.left)
    (c c' : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c') :
    ∃ ω : Tˣ, ∀ (l : ℕ) (s : RR x l), valT w (x.P.L.U c) (s.f c) = (ω : T) ^ l * valT w (x.P.L.U c') (s.f c') := by
  have hp : ⊤ ≤ w ⁻¹ᵁ (x.P.L.U c ⊓ x.P.L.U c') := fun p hp => ⟨h hp, h' hp⟩
  refine ⟨Units.map (valH w _ hp).toMonoidHom (x.P.L.g c c'), fun l s => ?_⟩
  have hs : rs x.P.A.left (inf_le_left : x.P.L.U c ⊓ x.P.L.U c' ≤ x.P.L.U c) (s.f c) =
      ((x.P.L.g c c' ^ (l : ℤ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')ˣ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')) *
        rs x.P.A.left inf_le_right (s.f c') := s.compat c c'
  refine (valT_res w inf_le_left hp _).symm.trans ((congrArg (valT w _) hs).trans ?_)
  refine (valT_eq w _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]; rfl
  · exact (valT_eq w _ hp _).symm.trans (valT_res w _ hp _)

theorem notMem_nonzeroLocus {R T : Type} [CommRing R] [CommRing T] [IsLocalRing T] (x : KeyIn R)
    (w : Sp T ⟶ x.P.A.left) (c : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) {l : ℕ} (s : RR x l)
    (hs : valT w (x.P.L.U c) (s.f c) = 0) : w (IsLocalRing.closedPoint T) ∉ Out.nonzeroLocus s := by
  intro hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have h₁ := top_le_of_closedPoint w hk
  have hle := x.P.A.left.basicOpen_le (s.f k)
  obtain ⟨ω, hω⟩ := exists_unit_chart x w k c (fun p hp => hle (h₁ hp)) h
  have e := valT_res w hle h₁ (s.f k)
  rw [valT_eq w _ h₁] at e
  have hu : IsUnit (valT w (x.P.L.U k) (s.f k)) :=
    e ▸ (x.P.A.left.toRingedSpace.isUnit_res_basicOpen (s.f k)).map (valH w _ h₁)
  rw [hω, hs, mul_zero] at hu
  exact not_isUnit_zero hu

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (π : X ⟶ Sp R) (f : R →+* T)
    (w : Sp T ⟶ X) (hw : w ≫ π = spMap f) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (c : R) :
    valT w U (cst π U c) = f c := by
  have h0 : valT w U (cst π U c) =
      valT w U ((π.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE w π (U := ⊤) le_top h _).trans ?_)
  rw [hw, ← Category.comp_id (spMap f), valT_spMap f (𝟙 (Sp R)) (U := ⊤) le_top, valT_eq (𝟙 (Sp R)) ⊤ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  simp

theorem eval_det_pderiv_mul {O : Type} [CommRing O] {g : ℕ} (e : MvPowerSeries (Fin g) O →ₐ[O] O)
    (ω : MvPowerSeries (Fin g) O) (F : Fin g → MvPowerSeries (Fin g) O) (hF : ∀ i, e (F i) = 0) :
    e (Matrix.of fun i j => MvPowerSeries.pderiv O j (ω * F i)).det =
      e ω ^ g * e (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det := by
  rw [AlgHom.map_det, AlgHom.map_det]
  refine Eq.trans ?_ ((Matrix.det_smul _ (e ω)).trans (by rw [Fintype.card_fin]))
  congr 1
  ext i j
  simp [hF]

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, jac x s (z a) (ch a)) := by
  intro laws O _ _ _ _ x n l d s b m z ch hn hl hb hm hfin hz hs hj hinj hex
  classical
  let p₀ : Fin d → x.P.A.left := fun a => (z a).left (IsLocalRing.closedPoint O)
  let Y : Type := Set.range p₀
  let p : Fin d → Y := fun a => ⟨p₀ a, a, rfl⟩
  have hY : Finite Y := (Set.finite_range p₀).to_subtype
  choose r hr using fun y : Y => y.2
  choose θ hθ₀ hθ₁ hθ₂ hθ₃ using fun y : Y =>
    GlobalTheory.FormalChart.exists_formal_chart O x.P.A.left x.P.A.hom x.P.g (z (r y)).left x.P.smoothDim (Over.w (z (r y)))
  have hθ : ∀ y : Y, θ y (IsLocalRing.closedPoint _) = y.1 := fun y => (hθ₀ y).trans (hr y)
  choose e he₁ he₂ using fun a => hθ₃ (p a) O (z a).left
    ((Over.w (z a)).trans (Spec.map_id _).symm) (hθ (p a)).symm
  have hc : ∀ y, ⊤ ≤ θ y ⁻¹ᵁ x.P.L.U (ch (r y)) := fun y => top_le_of_closedPoint _ (by
    rw [hθ₀]; exact hz (r y) (x := IsLocalRing.closedPoint O) trivial)
  have hc' : ∀ a, ⊤ ≤ θ (p a) ⁻¹ᵁ x.P.L.U (ch a) := fun a => top_le_of_closedPoint _ (by
    rw [hθ]; exact hz a (x := IsLocalRing.closedPoint O) trivial)
  choose ω hω using fun a => exists_unit_chart x (θ (p a)) (ch a) (ch (r (p a))) (hc' a) (hc (p a))
  let F : Y → Fin x.P.g → MvPowerSeries (Fin x.P.g) O := fun y i =>
    valT (θ y) (x.P.L.U (ch (r y))) ((s i).f (ch (r y)))
  let ρ : ∀ j, Y → Fin ((l - j * n) ^ x.P.g) → MvPowerSeries (Fin x.P.g) O := fun j y k =>
    valT (θ y) (x.P.L.U (ch (r y))) ((b j k).f (ch (r y)))
  let u : Fin d → Oˣ := fun a => Units.map (e a).toMonoidHom (ω a)
  have hval : ∀ a (k : ℕ) (sg : RR x k), valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a)) =
      (u a : O) ^ k * e a (valT (θ (p a)) (x.P.L.U (ch (r (p a)))) (sg.f (ch (r (p a))))) := fun a k sg => by
    have h := valT_spMap (e a).toRingHom (θ (p a)) (hc' a) (sg.f (ch a))
    rw [he₂, hω, map_mul, map_pow] at h
    exact h
  have hF : ∀ a i, e a (F (p a) i) = 0 := fun a i =>
    ((u a).isUnit.pow n).mul_right_eq_zero.1 ((hval a n (s i)).symm.trans (hs a i))
  have hZ : FinZ x s := by
    have : Finite (Sp O) := by
      refine Set.finite_univ_iff.1 ((Set.toFinite {(⊥ : PrimeSpectrum O), IsLocalRing.closedPoint O}).subset
        fun q _ => ?_)
      by_cases hq : PrimeSpectrum.asIdeal q = ⊥
      · exact Or.inl (PrimeSpectrum.ext hq)
      · exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime q).isMaximal hq)))
    refine (hfin.union (Set.finite_range fun q : Fin d × Sp O => (z q.1).left q.2)).subset fun y hy => ?_
    by_cases h : x.P.A.hom y = IsLocalRing.closedPoint O
    · exact Or.inl ⟨h, hy⟩
    · obtain ⟨a, q, hq⟩ := hex y h hy
      exact Or.inr ⟨(a, q), hq⟩
  have hcx := (KoszulCx.koszul_isCx O x n l d s b z ch hl hb).2 m hm hz hs
  have hcl := GlobalTheory.KosResidueExact.main laws O _ (IsLocalRing.residue O) x n l s b m hn hl hb hm hZ
  have hgen := GlobalTheory.KeyKa.KoszulGenExact.kosD_exact_generic laws O _ (algebraMap O (FractionRing O)) x n l s b m d z ch
    (IsFractionRing.injective O _) hn hl hb hm hz hs hj hinj (fun y ⟨q, hq⟩ => hex y fun h => by
      have h₁ := congrArg PrimeSpectrum.asIdeal (hq.trans h)
      have h₂ : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right q.isPrime.ne_top
      change Ideal.comap (algebraMap O (FractionRing O)) q.asIdeal = IsLocalRing.maximalIdeal O at h₁
      rw [h₂, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O _)] at h₁
      exact IsDiscreteValuationRing.not_a_field O h₁.symm)
  obtain ⟨hK₁, hK₂⟩ := GlobalTheory.KeyKa.KosKer.ker_and_image O x.P.g d _ m _ hcx hgen hcl
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let f : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have hf : RingHom.ker f = IsLocalRing.maximalIdeal O := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (IsLocalRing.ResidueField O) K).injective]
    exact IsLocalRing.ker_residue
  have hsurj := GlobalTheory.SeriesNakayama.span_mod_equations_lift O K f x.P.g _ Y F (ρ 0) hf (GlobalTheory.KeyKa.exists_sub_mem_of_dense K x.P.g _ Y _ _
    (GlobalTheory.KeyKa.exists_comb_sub_mem_sup_pow laws O K f x n l s b m Y θ (fun y => ch (r y)) hf hn hl hb hm hZ hθ₁ hθ₂ hc
      (fun y y' h => Subtype.ext ((hθ y).symm.trans (h.trans (hθ y'))))
      (fun y i => by
        rw [hθ₀]
        exact notMem_nonzeroLocus (T := O) x _ _ (hz (r y)) _ (hs (r y) i))))
  have hmul : ∀ y i k, F y i * ρ 1 y k = ∑ k', m i 0 1 k' k • ρ 0 y k' := fun y i k => by
    have h := congrArg (valH (θ y) _ (hc y)) (hm i 0 i.pos k (ch (r y)))
    rw [map_mul, map_sum] at h
    refine (congrArg₂ (· * ·) (valT_eq _ _ (hc y) _) (valT_eq _ _ (hc y) _)).trans
      (h.trans (Finset.sum_congr rfl fun k' _ => (map_mul _ _ _).trans ?_))
    rw [Algebra.smul_def]
    exact congrArg₂ (· * ·) ((valT_eq _ _ (hc y) _).symm.trans (valT_cst x.P.A.hom _ (θ y) (hθ₁ y) _ (hc y) _))
      (valT_eq _ _ (hc y) _).symm
  obtain ⟨E, Pm, h₁, h₂, h₃, h₄⟩ := GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian O x.P.g d _ Y p F (ρ 0) e (fun a => u a ^ (l - 0 * n))
    (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) hF he₁
    (fun a k => hval a _ (b 0 k)) hsurj (fun v hv y => by
      obtain ⟨w, rfl⟩ := hK₁ v hv
      have : ∑ k, (∑ i, (m i 0 1).mulVec (w i)) k • ρ 0 y k = ∑ i, ∑ k', w i k' • (F y i * ρ 1 y k') := by
        simp only [hmul, Finset.sum_apply, Finset.sum_smul, Finset.smul_sum, Matrix.mulVec, dotProduct, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [_root_.mul_comm]
      rw [this]
      exact Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun k' _ => Submodule.smul_of_tower_mem _ _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))) hK₂
  let ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O := fun j => Nat.casesOn j E fun _ => 0
  obtain ⟨h₅, t₀, h₆⟩ := GlobalTheory.KeyKa.KoszulTors.koszul_tors O x.P.g d _ m _ ev₀ Pm hcx h₁ h₂ h₃ hK₁ hcl
  refine ⟨ev₀, Pm, t₀, h₁, h₅, h₆, h₄.trans (Associated.prod _ _ _ fun a _ => ?_)⟩
  obtain ⟨v, hv⟩ := GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv O x (θ (p a)) (z a) (e a) (hθ₁ _) (hθ₂ _) (hθ₃ _) (he₁ a) (he₂ a)
  rw [hv n s (ch a) (hz a)]
  simp only [hω]
  rw [eval_det_pderiv_mul (e a) _ (F (p a)) (hF a), ← _root_.mul_assoc]
  exact (associated_unit_mul_right _ _ (v.isUnit.mul ((((ω a).isUnit.pow n).map (e a)).pow _)))

end GlobalTheory.DiscrJacGlobal
end
