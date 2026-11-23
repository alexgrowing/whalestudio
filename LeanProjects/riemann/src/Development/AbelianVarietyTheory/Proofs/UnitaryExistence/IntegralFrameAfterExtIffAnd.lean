import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AlgebraicPointWeights
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.AlgLawsCompare

open NumberField IsDedekindDomain IsLocalRing AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights GlobalTheory.Frames

section Valuations

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one_iff_isUnit (v : V) : valV V (algebraMap V K' v) = 1 ↔ IsUnit v := by
  rw [← notMem_maximalIdeal, ← valV_lt_one_iff (K' := K'), not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (valV_le_one v) h⟩

theorem vV_nonneg (v : V) : 0 ≤ vV V (algebraMap V K' v) := by
  by_cases h : algebraMap V K' v = 0
  · simp [h, vV]
  · have := (WithZero.log_le_log (valV_ne_zero (V := V) h) one_ne_zero).2 (valV_le_one v)
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

end Valuations

theorem exists_overLa {K : Type} [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr) (hT : T.FinRes) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la T.V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := T.V) (K := T.Fr)
      (IsIntegral.map_of_comp_eq (Int.castRingHom T.V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective T.V T.Fr
  let g : 𝓞 K →+* T.V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap T.V T.Fr (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal T.V).comap g ≠ ⊥ := by
    have : Finite (ResidueField T.V) := hT
    have hc : Nat.card (ResidueField T.V) ≠ 0 := Nat.card_pos.ne'
    intro h
    have h1 : ((Nat.card (ResidueField T.V) : ℕ) : 𝓞 K) ∈ (maximalIdeal T.V).comap g := by
      rw [Ideal.mem_comap, map_natCast, ← residue_eq_zero_iff, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    rw [h, Ideal.mem_bot] at h1
    exact hc (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal T.V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV T.V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg, valV_eq_one_iff_isUnit]
    exact notMem_maximalIdeal.1 ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV T.V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hpos : 0 < vV T.V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV T.V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

theorem finite_of_finite_residueField {V K W L : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) : i.Finite := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    Formalism.L2.PjFree.mem_range_of_vV_nonneg (by rw [hi]; exact mul_nonneg (by positivity) (vV_nonneg a))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := ((algebraMap W L).comp g).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun a => hg a
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_cases h0 : a = 0
    · simp [h0]
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    have h1 : valV W (algebraMap W L (g a)) = 1 := (valV_eq_one_iff_isUnit _).2 hu
    have h2 := hi (algebraMap V K a)
    have h3 : (0 : ℤ) < r * vV V (algebraMap V K a) := mul_pos (by exact_mod_cast hr) (vV_pos h0 ha)
    rw [← h2, ← hg, vV, h1] at h3
    simp at h3
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  have : IsHausdorff ((maximalIdeal V).map (algebraMap V W)) W := IsHausdorff.of_isDomain _ htop
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have : Finite (W ⧸ (maximalIdeal V).map (algebraMap V W)) := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    have : Finite (W ⧸ maximalIdeal W) := h'
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have : Module.Finite V (W ⧸ (maximalIdeal V).map (algebraMap V W)) := Module.Finite.of_finite
  have : Module.Finite V W := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal V)
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_testRing_factor {K : Type} [Field K] (p : TRing K) {S : Type} [Field S] [Algebra K S]
    (φ : p.R →ₐ[K] S) {J : Type} [Fintype J] (g : J → S) :
    ∃ (r : TRing K) (α : p.R →ₐ[K] r.R) (χ : r.R →ₐ[K] S) (gr : J → r.R),
      Function.Injective χ ∧ χ.comp α = φ ∧ ∀ j, χ (gr j) = g j := by
  classical
  let e := Fintype.equivFin J
  let v : Fin (p.n + Fintype.card J) → S :=
    Fin.append (fun i => φ (Ideal.Quotient.mk p.I (MvPolynomial.X i))) (fun k => g (e.symm k))
  let Φ : MvPolynomial (Fin (p.n + Fintype.card J)) K →ₐ[K] S := MvPolynomial.aeval v
  let r : TRing K := ⟨p.n + Fintype.card J, RingHom.ker Φ, (RingHom.ker_isPrime Φ).isRadical⟩
  have hΦ : Φ.comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J))) =
      φ.comp (Ideal.Quotient.mkₐ K p.I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, v, Fin.append_left]
  let α₀ : MvPolynomial (Fin p.n) K →ₐ[K] r.R :=
    (Ideal.Quotient.mkₐ K (RingHom.ker Φ)).comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J)))
  have hα₀ : ∀ a ∈ p.I, α₀ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
    have h1 : Φ (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) a) = φ (Ideal.Quotient.mk p.I a) :=
      congrArg (fun F => F a) hΦ
    exact h1.trans (by rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
  let α : p.R →ₐ[K] r.R := Ideal.Quotient.liftₐ p.I α₀ hα₀
  let χ : r.R →ₐ[K] S := Ideal.kerLiftAlg Φ
  refine ⟨r, α, χ, fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Fin.natAdd p.n (e j))),
    Ideal.kerLiftAlg_injective Φ, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    rw [← hΦ]
    apply MvPolynomial.algHom_ext
    intro i
    rfl
  · intro j
    show Φ _ = g j
    simp [Φ, v, Fin.append_right]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z : FrPt Xo c T, FrMap φ y z :=
  FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem exists_frame {L : Type} [Field L] [Algebra c.F L] (x : Sp L ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c L) :
    ∃ y : FrPt Xo c L, y.x = x := by
  classical
  obtain ⟨y, -, h, -⟩ := gfp_frPt_gen (L' := L) GlobalTheory.abelianSchemeLaws_all.2.secTwist (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  exact ⟨y, h⟩

theorem fromTest_of_same_point {S : Type} [Field S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' := by
  classical
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
  obtain ⟨r, α, χ, gr, hχ, hα, hgr⟩ := exists_testRing_factor p φ
    (J := (Σ τ : E →+* ℂ, Option (Fin (Dw.mult τ) × Fin (Dw.mult τ))) ⊕ Bool)
    (Sum.elim (fun q => q.2.elim (g q.1).det⁻¹ fun ij => g q.1 ij.1 ij.2) fun b => cond b (a : S) (a⁻¹ : Sˣ))
  let g₀ : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) r.R :=
    fun τ => Matrix.of fun i j => gr (.inl ⟨τ, some (i, j)⟩)
  have hg₀ : ∀ τ, (g₀ τ).map χ = g τ := fun τ => Matrix.ext fun i j => hgr (.inl ⟨τ, some (i, j)⟩)
  have hd : ∀ τ, IsUnit (g₀ τ).det := fun τ => by
    refine IsUnit.of_mul_eq_one (gr (.inl ⟨τ, none⟩)) (hχ ?_)
    rw [map_mul, map_one, hgr, AlgHom.map_det, AlgHom.mapMatrix_apply, hg₀]
    exact mul_inv_cancel₀ (hg τ).ne_zero
  have h1 : gr (.inr true) * gr (.inr false) = 1 := hχ (by rw [map_mul, map_one, hgr, hgr]; simp)
  let a₀ : r.Rˣ := ⟨gr (.inr true), gr (.inr false), h1, (mul_comm _ _).trans h1⟩
  obtain ⟨z, hz⟩ := exists_baseChange α y₀
  have hzy : FrMap χ z y := frMap_cancel (Xo := Xo) (c := c) _ _ _ α χ y₀ z y hz (hα ▸ h₀)
  obtain ⟨z', hz', -⟩ := existsUnique_frChg E H Dw l Xo c r.R z g₀ a₀ hd
  refine ⟨r, χ, z', (ChgBC.frChg_baseChange E H Dw l Xo c r.R S χ z z' y y' g₀ a₀ hz' hzy).2 ?_⟩
  have ha : χ (a₀ : r.R) = (a : S) := hgr (.inr true)
  simp only [hg₀, ha]
  exact hc

theorem reFrame : Formalism.L2.PjFree.ReFrame Xo c := by
  refine Formalism.L2.PjFree.reFrame_of
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw') ?_
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx k hk
  have hK : ∀ τ, IsUnit ((k τ).map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk τ).map _
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  simp only at hx
  subst hx
  obtain ⟨u0, hu0⟩ := IntRebase.gen_unit' (x := y0.1.x) zs y0.1.s zg y0.1.gen
  refine ⟨⟨IntRebase.rebase₂ y0.1 _ hK, fromTest_of_same_point (y := y0.1) rfl y0.2.1,
    IntRebase.integral_reb T io y0.1 y0.2.2 k hk hK⟩, u0, rfl, fun τ i => ?_,
    𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · exact (IntRebase.isCombAtG_iff Xo.univ.t y0.1.x
      (fun j => IntRebase.ovT (t := Xo.univ.t) (y0.1.tan τ j)) _ _).2 rfl
  · intro i h
    show ((𝟙 _ : Gx y0.1.x ⟶ Gx y0.1.x).appLE _ _ h).hom (scal y0.1.x (u0 : T.Fr) i * zs.f i) = y0.1.s.f i
    rw [← hu0 i]
    exact IntRebase.id_appLE_apply _ _ h _

variable (Xo c)

def FramesExtendAt (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  letI := io.toAlgebra
  ∀ y : FrPt Xo c T.Fr, ∃ (T' : CDVR) (io' : c.F →+* T'.Fr),
    letI := io'.toAlgebra
    ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (r : ℕ), 0 < r ∧ (∀ x : T.Fr, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧
      φ.toRingHom.Finite ∧ (T.FinRes → T'.FinRes) ∧
      ∃ (z : FrPt Xo c T'.Fr) (y' : IntFr Xo c T' io') (t : Ix Dw → T'.Frˣ), FrMap φ y z ∧ FrBor t z y'.1

def IntegralFrameAfterExtFinRes : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    FramesExtendAt Xo c T io

end GlobalTheory.AlgLawsCompare
