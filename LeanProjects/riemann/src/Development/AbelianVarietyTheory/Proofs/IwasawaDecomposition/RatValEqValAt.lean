import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEquationsHeightSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCardStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointsEquivFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSectionExtensionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HtModel

theorem ratVal_eq_valAt {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (f : Z.functionField) (y : CxPts q σ) : ratVal f y = valAt y.1 f := by
  by_cases h : RegAt (under y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hy : y ∈ CxPts.ptsIn q σ U := CxPts.mem_ptsIn.2 hU
    rw [ratVal_fnOf hy, OfModel.valAt_fnOf y.1 hU hy, CxPts.ev_eq hy]
    rfl
  · rw [ratVal, dif_neg h, valAt, dif_neg h]

theorem bijective_comp (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => ?_, fun σ => ?_⟩
  · exact IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun h a
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (I := RingHom.ker σ) (eq_bot_iff.2 fun n hn => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    exact Int.cast_eq_zero.1 hn
  refine ⟨IsFractionRing.lift (A := 𝓞 F) (K := F) hσ, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

open Classical in

theorem ht_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+), A.Induced M L k 0 → ∀ (x : Y.X) (a : ℝ), IsClosed ({x} : Set Y.X) → ArInt.IsPtHt L (M.j x) a → A.ht x = a / (((k : ℕ) : ℝ) * (A.n : ℕ)) := by
  intro F _ _ C Y A M L k ⟨_, r, hr, hinf, hfin⟩ x a hx ⟨h, H, ha⟩
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (M.j x)
  have := M.ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := GlobalTheory.T.closed_point_algebraic F Y M x hx
  have hri : Set.range i = closure {M.j x} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ M.p) 0 := M.ar.of_isClosedImmersion i hcΓ hd
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  have he : A.D.IsEqn x (eqn A.D x) := (A.D.exists_isEqn x).choose_spec
  have hu (c) (hc : x ∈ (L.B.pull M.j).U c) :
      UnitAt x (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) := by
    have := (he.nsmul k).iff_unitAt.1 (hr.isEqn c x hc)
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  obtain ⟨s, hs, hval⟩ := GlobalTheory.T.rational_section_extension M.X Y.X Z M.j i x hi L.B L.isLB r hr.isRatSec _ hu
  have hdeg := H.point Z i hcΓ hd s hs
  have hne := (ExtConj.main F).1

  obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have h₁ := GlobalTheory.T.local_equations_height_sum F Z (i ≫ M.p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => (k : ℕ) * A.lg v (hne v).some (E y).1) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ M.j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : M.j x ∈ L.B.U c := by
        have := Set.mem_iInter.1 (OfModel.le_chart M L.B _ (E y).1 (yt ≫ i) e₁ (i := fun _ => c) hU
          (x := IsLocalRing.closedPoint _) trivial) PUnit.unit
        rw [← (E y).2]
        exact this
      rw [hfin v _ (E y).1 (yt ≫ i) (fun _ => c) e₁ hU, hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc, (E y).2]
      simp)
  have h₂ (v) : ∑ᶠ y, ((k : ℕ) : ℝ) * A.lg v (hne v).some (E y).1 =
      (k : ℕ) * if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]
    exact congrArg _ (finsum_comp_equiv E (f := fun y => A.lg v (hne v).some y.1))
  replace h₁ := h₁.trans (congrArg (- ·) (finsum_congr h₂))

  have h₃ (σ : F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ M.p) (σ.comp (algebraMap (𝓞 F) F)), logNorm ((L.restr i).φ _) s y =
      (k : ℕ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi ℂ σ
    rw [← finsum_subtype_eq_finsum_cond, mul_finsum]
    refine finsum_eq_of_bijective E E.bijective fun y => ?_
    have hp := CxPts.mem_ptsIn.1 (CxPts.mem_pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y)
    unfold logNorm
    generalize CxPts.pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = c at hp ⊢
    have hxc : M.j x ∈ L.B.U (c PUnit.unit) := by
      have := Set.mem_iInter.1 hp PUnit.unit
      rw [← hi, ← (hE y).2]
      exact this
    have hx' : under (E y).1 = x := (E y).2
    have hxc' : x ∈ (L.B.pull M.j).U c := Set.mem_iInter.2 fun _ => hxc
    have hg : A.D.GeneratesAt (under (E y).1) ((eqn A.D x)⁻¹ : Y.Fnˣ) := by
      rw [hx', Units.val_inv_eq_inv_val]
      exact CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hreg : ((k : ℕ) • A.D).RegularAt (under (E y).1) ((((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) ^ (k : ℕ)) := by
      rw [hx', ← Units.val_pow_eq_pow_val, inv_pow, Units.val_inv_eq_inv_val]
      exact (CartierDiv.isEqn_iff_generatesAt_inv.1 (he.nsmul k)).regularAt
    have e₁ := hinf σ (E y).1 (Points.PtsOver.map i rfl _ y) c _ (hE y).1.symm (hx'.symm ▸ hxc') hreg
    rw [C.pn_mPow _ _ _ _ _ _ _ hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at e₁
    have h0 : ‖ratVal (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) (E y).1‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (by rw [hx']; exact hu c hxc'))
    have e₂ := congrArg Real.log e₁
    have h0' : C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) (E y).1 ^ (k : ℕ) ≠ 0 :=
      right_ne_zero_of_mul (e₁.trans_ne (mul_ne_zero (pow_ne_zero _ h0) (Real.exp_ne_zero _)))
    rw [Real.log_mul (Real.exp_ne_zero _) h0', Real.log_mul (pow_ne_zero _ h0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow, ratVal_eq_valAt] at e₂
    have e₃ := hval ℂ _ _ (c PUnit.unit) (hE y).1 (E y).2 (hE y).2 hxc
    have e₄ := (L.φ _).pull_φ i rfl c y
    rw [ratVal_eq_valAt]
    refine (congrArg₂ (fun a b => Real.log ‖a‖ - b / 2) e₃ e₄).trans ?_
    push_cast at e₂
    change Real.log ‖valAt (E y).1.1 (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn)‖ - _ = _
    push_cast
    linarith
  unfold HermLB.curveDeg at hdeg
  rw [h₁, ← finsum_eq_of_bijective _ (bijective_comp F) fun σ => (h₃ σ).symm, hi, ha,
    GlobalTheory.T.residue_embeddings_card F Y M x hx, ← mul_finsum, ← mul_finsum, finsum_eq_sum_of_fintype (α := F →+* ℂ)] at hdeg
  obtain ⟨_, _⟩ := ExtConj.pts Y x hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hk : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  rw [Adl.ht, div_eq_div_iff (by positivity) (by positivity)]
  rw [Nat.cast_mul] at hdeg
  linear_combination (-((A.n : ℕ) : ℝ)) * hdeg

end GlobalTheory.TrueGeo.HtModel
