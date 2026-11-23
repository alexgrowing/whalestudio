import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSectionsGoodThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTy

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ImageGenReg

section Alg

open scoped TensorProduct
open Filter Topology

open GlobalTheory.AffinePoints in

theorem exists_approx {k A : Type} [CommRing k] [IsDedekindDomain k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (σ : k →+* ℂ) (hσ : Function.Injective σ) (P : Ideal A) [P.IsPrime]
    (hP : ∀ a : k, algebraMap k A a ∈ P → a = 0) {b : A} (hb : b ∈ P) (hb0 : b ≠ 0) :
    ∃ (ι : Type) (l : Filter ι) (_ : l.NeBot) (φ : ι → A →+* ℂ) (φ₀ : A →+* ℂ),
      (∀ i a, φ i (algebraMap k A a) = σ a) ∧ (∀ a, φ₀ (algebraMap k A a) = σ a) ∧ φ₀ b = 0 ∧
      (∀ᶠ i in l, φ i b ≠ 0) ∧ ∀ a, Tendsto (fun i => φ i a) l (𝓝 (φ₀ a)) := by
  letI : Algebra k ℂ := σ.toAlgebra
  haveI : FaithfulSMul k ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hσ
  haveI : Module.Flat k ℂ := inferInstance
  have hinj : Function.Injective (algebraMap k (A ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hP a (Ideal.Quotient.eq_zero_iff_mem.1 ha)
  haveI : Nontrivial (ℂ ⊗[k] (A ⧸ P)) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) (Algebra.linearMap k (A ⧸ P)) hinj
    haveI : Nontrivial (ℂ ⊗[k] k) := (TensorProduct.rid k ℂ).toEquiv.nontrivial
    exact h.nontrivial
  obtain ⟨ψ₀⟩ := GlobalTheory.GeomPointLift.nonempty_algHom_of_isAlgClosed ℂ (ℂ ⊗[k] (A ⧸ P))
  let ψ : ℂ ⊗[k] A →ₐ[ℂ] ℂ := ψ₀.comp (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ k P))
  have hψb : ψ (1 ⊗ₜ b) = 0 := by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem.2 hb]
  have hnz : (1 ⊗ₜ b : ℂ ⊗[k] A) ∈ nonZeroDivisors (ℂ ⊗[k] A) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) (LinearMap.mulLeft k b)
      (mul_right_injective₀ hb0)
    have e : ∀ x : ℂ ⊗[k] A, LinearMap.lTensor ℂ (LinearMap.mulLeft k b) x = (1 ⊗ₜ b) * x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add x y hx hy => rw [map_add, hx, hy, mul_add]
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    exact h (by rw [e, hx, map_zero])
  haveI := RingHom.ker_isPrime ψ
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (ℂ ⊗[k] A))) (J := RingHom.ker ψ) bot_le
  haveI : q.IsPrime := hq.1.1
  have hbq : (1 ⊗ₜ b : ℂ ⊗[k] A) ∉ q := fun h =>
    Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h hnz
  let B := (ℂ ⊗[k] A) ⧸ q
  let m : A →+* B := (Ideal.Quotient.mk q).comp Algebra.TensorProduct.includeRight.toRingHom
  let p₀ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ q ψ fun a ha => hqle ha
  have hm : ∀ (r : B →ₐ[ℂ] ℂ) a, r (m (algebraMap k A a)) = σ a := fun r a => by
    have : m (algebraMap k A a) = algebraMap ℂ B (σ a) := by
      change Ideal.Quotient.mk q (Algebra.TensorProduct.includeRight (algebraMap k A a)) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k ℂ (ℂ ⊗[k] A)]
      rfl
    rw [this, AlgHom.commutes]
    rfl
  have hd := dense_nonvanishing (A := B) (f := m b) fun h => hbq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine ⟨B →ₐ[ℂ] ℂ, 𝓝[{r | r (m b) ≠ 0}] p₀, mem_closure_iff_nhdsWithin_neBot.1 (hd p₀),
    fun r => r.toRingHom.comp m, p₀.toRingHom.comp m, hm, hm p₀, hψb, self_mem_nhdsWithin, fun a => ?_⟩
  exact ((continuous_eval (m a)).tendsto p₀).mono_left nhdsWithin_le_nhds

end Alg

section Geo

open Filter Topology CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem regAt_of_bounded {k : Type} [CommRing k] [IsDedekindDomain k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (p : X ⟶ Sp k) [LocallyOfFiniteType p]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (σ : k →+* ℂ) (hσ : Function.Injective σ) (W : X.Opens)
    (g : X.functionField) (Φ : CxPts p σ → ℝ) (hΦ : ∀ y ∈ ptsIn p σ W, ContinuousAt Φ y)
    (hb : ∀ y ∈ ptsIn p σ W, RegAt (under y) g → ‖ratVal g y‖ ^ 2 ≤ Φ y) (x : X) (hx : x ∈ W)
    (hpx : (p x).asIdeal = ⊥) : RegAt x g := by
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.NormalPole.exists_zeroAt_inv X hN x g hreg
  have hg0 : g ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hpz : (p z).asIdeal = ⊥ :=
    le_bot_iff.1 (hpx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 (hz.map p.continuous))
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset (memInf hzW (hz.mem_open W.isOpen hx))
  have hle : U ≤ W₀ ⊓ W := hUW
  obtain ⟨b, hb'⟩ : ∃ b : Γ(X, U), ∀ h, fnOf _ h b = g⁻¹ :=
    ⟨resG X (hle.trans inf_le_left) g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hb0 : b ≠ 0 := fun h => inv_ne_zero hg0 (by rw [← hb' (gen_mem hzU), h, map_zero])
  have hzb : z ∉ X.basicOpen b := fun h =>
    (zeroAt_iff.1 hzero).2 (hb' (gen_mem hzU) ▸ (unitAt_fnOf_iff hzU _ b).2 h)
  have hmem (a : Γ(X, U)) : z ∈ X.basicOpen a ↔ a ∉ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    conv_lhs => rw [← show hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) = z from hU.fromSpec_primeIdealOf ⟨z, hzU⟩]
    change hU.primeIdealOf ⟨z, hzU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
  letI : Algebra k Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType k Γ(X, U) :=
    RingHom.FiniteType.comp (p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  obtain ⟨ι, l, _, φ, φ₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_approx σ hσ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
    (fun a ha => by
      by_contra h0
      have e := Scheme.basicOpen_appLE p U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
      rw [basicOpen_eq_of_affine] at e
      have h : z ∈ X.basicOpen (algX p U a) := (SetLike.ext_iff.1 e z).2 ⟨hzU, by
        change a ∉ (p z).asIdeal
        rw [hpz]
        exact h0⟩
      exact (hmem _).1 h ha)
    (not_not.1 fun h => hzb ((hmem b).2 h)) hb0
  let y (i : ι) : CxPts p σ := ofHom hU (φ i) (h₁ i)
  let y₀ : CxPts p σ := ofHom hU φ₀ h₂
  have hy (i) : y i ∈ ptsIn p σ U := ofHom_mem hU _ _
  have hy₀ : y₀ ∈ ptsIn p σ U := ofHom_mem hU _ _
  have hlim : Tendsto y l (𝓝 y₀) := tendsto_subtype_rng.2
    (tendsto_of_isAffineOpen hU hy₀ (.of_forall hy) fun a => by
      have e₀ : valR y₀.1 U a = φ₀ a := ev_ofHom hU _ _ a
      rw [e₀]
      exact (h₅ a).congr fun i => (ev_ofHom hU (φ i) (h₁ i) a).symm)
  have hT : Tendsto (fun i => Φ (y i) * ‖φ i b‖ ^ 2) l (𝓝 (Φ y₀ * ‖φ₀ b‖ ^ 2)) :=
    ((hΦ y₀ (ptsIn_mono (hle.trans inf_le_right) hy₀)).tendsto.comp hlim).mul ((h₅ b).norm.pow 2)
  rw [h₃, norm_zero, zero_pow two_ne_zero, mul_zero] at hT
  refine absurd (ge_of_tendsto hT (h₄.mono fun i hi => ?_)) (not_le.2 one_pos)
  have hev : ev p σ U b (y i) = φ i b := ev_ofHom hU _ _ b
  have hu : UnitAt (under (y i)) g⁻¹ := hb' (gen_mem hzU) ▸ (unitAt_fnOf_iff (mem_ptsIn.1 (hy i)) _ b).2
    (mem_ptsIn.1 ((mem_ptsIn_basicOpen (hy i) b).2 (hev ▸ hi)))
  have hgu : UnitAt (under (y i)) g := inv_inv g ▸ hu.inv
  have hmul := ratVal_mul hgu.regAt hu.regAt
  have hone : ratVal (1 : X.functionField) (y i) = 1 := by
    have := ratVal_fnOf (hy i) (gen_mem hzU) 1
    rwa [map_one, ev_eq (hy i), map_one] at this
  rw [mul_inv_cancel₀ hg0, hone, ← hb' (gen_mem hzU), ratVal_fnOf (hy i), hev] at hmul
  have h := hb (y i) (ptsIn_mono (hle.trans inf_le_right) (hy i)) hgu.regAt
  calc (1 : ℝ) = ‖ratVal g (y i)‖ ^ 2 * ‖φ i b‖ ^ 2 := by rw [← mul_pow, ← norm_mul, ← hmul, norm_one, one_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (sq_nonneg _)

end Geo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option maxHeartbeats 1000000 in

theorem main : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), (p x).asIdeal = ⊥ → GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i)) := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw k x hx hpx
  have : IsProper p := by
    obtain ⟨n, c, hc, h⟩ := hM.arith.isProjOver
    have := isProper_str (𝓞 Y.d.c₂.F) n
    rw [← h]
    infer_instance
  have := hM.arith.isLocallyNoetherian
  obtain ⟨τ⟩ : Nonempty (Y.d.c₂.F →+* ℂ) := inferInstance
  let σ := τ.comp (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F)
  refine regAt_of_bounded p hM.normal σ (τ.injective.comp (IsFractionRing.injective _ _)) (L.B.U k) _
    (fun y => Real.exp (2 * ((8 * i : ℕ) : ℝ) * t) * Real.exp (((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y))
    (fun y hy => continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (L.cInf σ k y hy).continuousAt)))
    (fun y hy hr => ?_) x hx hpx
  have h := GlobalTheory.T.hermitian_lattice_sections_good_three hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw σ y k hy hr
  rwa [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)] at h

end GlobalTheory.ImageGenReg

end
