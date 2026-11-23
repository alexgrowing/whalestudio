import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

def dualHom {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) : A →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_mul' f f' := by ext <;> simp [hm, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f f' := by ext <;> simp

@[simp] theorem dualHom_fst {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).fst = e f := by
  simp [dualHom]

@[simp] theorem dualHom_snd {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).snd = D f := by
  simp [dualHom]

theorem derivation_eq_zero_of_etale {k A : Type} [CommRing k] [CommRing A] {g : ℕ}
    (φ : MvPolynomial (Fin g) k →+* A) (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ)
    (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have hP : ∀ q, D (φ q) = 0 := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add q r hq hr => rw [map_add, map_add, hq, hr, add_zero]
    | mul_X q i hq => rw [map_mul, hm, hq, hX]; simp
  let F : A →+* DualNumber ℂ := dualHom e D hm
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ q, F (φ q) = F₀ (φ q) := fun q => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) k) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) k) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F₀ with commutes' := fun q => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.PointDer

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_eq_fderiv : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  intro k _ Y p n σ c x₀ hx₀ U hU δ hδ0 hδm
  have hxc : x₀ ∈ ptsIn p σ c.U := c.source_subset hx₀
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 c.affine _
    ⟨mem_ptsIn.1 hU, mem_ptsIn.1 hxc⟩
  have hWc : Y.basicOpen g ≤ c.U := Y.basicOpen_le g
  have hWU : Y.basicOpen g ≤ U.1 := hfg ▸ Y.basicOpen_le f
  have hxW : x₀ ∈ ptsIn p σ (Y.basicOpen g) := mem_ptsIn.2 (hfg ▸ hxf)

  have hmU : ∀ a b, δ (a * b) = evHom hU a * δ b + evHom hU b * δ a := fun a b => by
    rw [hδm, ev_eq hU, ev_eq hU]
  let ψU := dualHom (evHom hU) δ hmU
  letI : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen g) := (resG Y hWU).toAlgebra
  haveI : IsLocalization.Away f Γ(Y, Y.basicOpen g) :=
    U.2.isLocalization_of_eq_basicOpen f (homOfLE hWU) hfg.symm
  have hfu : IsUnit (ψU f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst, isUnit_iff_ne_zero, ← ev_eq hU]
    exact (mem_ptsIn_basicOpen hU f).1 (mem_ptsIn.2 hxf)
  let ψW : Γ(Y, Y.basicOpen g) →+* DualNumber ℂ := IsLocalization.Away.lift f hfu
  have hψW (a : Γ(Y, U.1)) : ψW (resG Y hWU a) = ψU a := IsLocalization.Away.lift_eq f hfu a
  have hψW1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ψW = evHom hxW := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    change (ψW (resG Y hWU a)).fst = evHom hxW (resG Y hWU a)
    rw [hψW, dualHom_fst, ← ev_eq, ← ev_eq, ev_res _ hxW]
  have hfst (a : Γ(Y, Y.basicOpen g)) : (ψW a).fst = evHom hxW a := RingHom.congr_fun hψW1 a

  let v : ReciprocityTheory.L2DbarEstimates.V n := WithLp.toLp 2 (fun b => (ψW (resG Y hWc (c.x b))).snd)

  have hdW := fun a : Γ(Y, Y.basicOpen g) => c.differentiableAt_ev a hx₀ hxW
  let dW : Γ(Y, Y.basicOpen g) → ℂ := fun a => fderiv ℂ (ev p σ _ a ∘ c.e.symm) (c.e x₀) v
  have hdadd (a b) : dW (a + b) = dW a + dW b := by
    have e : ev p σ _ (a + b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) + (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_add _ _ _
    simp only [dW, e, fderiv_add (hdW a) (hdW b), ContinuousLinearMap.add_apply]
  have hdmul (a b) : dW (a * b) = evHom hxW a * dW b + evHom hxW b * dW a := by
    have e : ev p σ _ (a * b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) * (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_mul _ _ _
    simp only [dW, e, fderiv_mul (hdW a) (hdW b), Function.comp_apply, c.e.left_inv hx₀,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← ev_eq hxW]
  have hn : ∀ᶠ w in 𝓝 (c.e x₀), c.e.symm w ∈ ptsIn p σ (Y.basicOpen g) :=
    Filter.eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds
      (ChartGlue.mem_over c.e hx₀ hxW)) fun _ h => h.2

  let Dd : Γ(Y, Y.basicOpen g) →+ ℂ := AddMonoidHom.mk' (fun a => (ψW a).snd - dW a) fun a b => by
    simp only [map_add, TrivSqZeroExt.snd_add, hdadd]
    ring
  have hD : Dd = 0 := by
    refine derivation_eq_zero_of_etale ((resG Y hWc).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x))
      ?_ (evHom hxW) Dd ?_ ?_ ?_
    · have hR : (resG Y hWc).Etale := by
        letI : Algebra Γ(Y, c.U) Γ(Y, Y.basicOpen g) := (resG Y hWc).toAlgebra
        haveI : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
          c.affine.isLocalization_of_eq_basicOpen g (homOfLE hWc) rfl
        exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway g)
      exact RingHom.Etale.stableUnderComposition _ _ c.etale hR
    · intro a
      have e1 : (resG Y hWc) (MvPolynomial.eval₂Hom (algX p c.U) c.x (MvPolynomial.C a)) =
          resG Y hWU (algX p U.1 a) := by
        rw [MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX,
          ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
      have e2 : dW (resG Y hWU (algX p U.1 a)) = 0 := by
        have e : ev p σ _ (resG Y hWU (algX p U.1 a)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] fun _ => σ a := by
          filter_upwards [hn] with w hw
          rw [Function.comp_apply, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
          exact ev_algX hw a
        show fderiv ℂ _ _ v = 0
        rw [e.fderiv_eq]
        simp
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, e1, hψW, ψU, dualHom_snd, hδ0, e2, sub_zero]
    · intro a b
      simp only [Dd, AddMonoidHom.mk'_apply, map_mul, TrivSqZeroExt.snd_mul, hfst, hdmul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    · intro i
      have e2 : dW (resG Y hWc (c.x i)) = v i := by
        have e : ev p σ _ (resG Y hWc (c.x i)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)]
            EuclideanSpace.proj (𝕜 := ℂ) i := by
          filter_upwards [hn, c.e.open_target.mem_nhds (c.e.map_source hx₀)] with w hw hwt
          rw [Function.comp_apply, ev_res hWc hw, ← c.apply_eq _ (c.e.map_target hwt) i,
            c.e.right_inv hwt]
          rfl
        simp only [dW, e.fderiv_eq, ContinuousLinearMap.fderiv]
        rfl
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', e2]
      simp [v]
  refine ⟨v, fun a => ?_⟩
  have h1 := congrArg (fun D : Γ(Y, Y.basicOpen g) →+ ℂ => D (resG Y hWU a)) hD
  simp only [Dd, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply, hψW, dualHom_snd, sub_eq_zero] at h1
  rw [show δ a = (ψU a).snd from (dualHom_snd _ _ _ a).symm, h1]
  have e : ev p σ _ (resG Y hWU a) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] ev p σ U.1 a ∘ c.e.symm := by
    filter_upwards [hn] with w hw
    exact ev_res hWU hw a
  simp only [dW, e.fderiv_eq]

end GlobalTheory.PointDer
