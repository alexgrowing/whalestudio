import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.IsoActFree
import Development.WeilBound.ThetaLifts.SmallCones.ConeAB
import Development.WeilBound.ThetaLifts.SmallCones.GenAnisoOf
import Development.WeilBound.ThetaLifts.SmallCones.SoDefs

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genSmall_of (hK : CTKernel) (hF : CTFub) (hCB : ConeB) (h2 : TwoExp) (hM : MixAB) (hMW : MixW) (hC : EvCone) (hWi : Witt)
    (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hSD : SoDecay) (hV : FinVolU) (hSF : SoFin)
    (hSt : SoStab) (hZ : SoZeroA') (hSe : SoEv) : GenSmall := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eB hM₁ hM₀ he₀ heB z hz K μK μ hI hμK hμ
  by_cases hex : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ hp => absurd ⟨χX, χW, om, hp⟩ hex⟩
  obtain ⟨χ0, χ0', o, hq⟩ := hex
  obtain ⟨⟨eA, heA⟩, -⟩ := hC F E σ B n d X W M χ0 χ0' o _ _ _ _ hq _ _ X₁ W₁ H H' i₀ i₁ j₀ j₁ M₀ hH hH' hM₀
  obtain ⟨C₀, hC₀, -, hK1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀
  obtain ⟨C₁, hC₁, hK2⟩ := hK1 n₁ X₁ H j₀ j₁ M₀ hH hM₀ eA heA
  obtain ⟨c, hc, h2'⟩ := h2 F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hq.base hq.herm hq.skew hq.good hM₀
    eA eB heA heB
  obtain ⟨κ, hκ, hB⟩ := hCB F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' eB heB z hz K μK μ hI hμK hμ
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ hq.base hq.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  obtain ⟨κ₁, hκ₁, hch⟩ := dom_change hG hE hq.base hq.herm hq.good.haar hM₁.haar hq.good.dom hM₁.dom
  refine ⟨C₀ * κ₁, C₁ * c * κ, mul_ne_zero hC₀ hκ₁, mul_ne_zero (mul_ne_zero hC₁ hc) hκ,
    fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hs := hle Φ hΦ
  have hst := hSt F E σ B n d X W M χX χW om _ _ _ _ hp
  obtain ⟨hmA, hmB⟩ := hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  replace hmA := hmA eA heA
  have hu := (hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1
  have lB := lawsB hp heB (hmB eB heB) hz.1 hH.rank hH'.xx fun m hm => (hu m hm).2
  obtain ⟨b1, b2, b3⟩ := hB χX χW om om₀ hp hp₀ Φ hΦ hfin
  replace b1 := b1 γ hγ
  have k1 := hK2 γ hγ χX χW om _ _ _ _ hp Φ hs
  have hsch : ∀ {I e}, IsEv B M M₀ H.ι H'.ι I e → ∀ w, ∀ Ψ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ w Ψ) ∈ schA F (Fin n₁ × Fin d₁) := fun he w Ψ h => he.maps _ (rho_mem M hp.base.std w h)
  set L : UA σ X.J → UA σ W.J → ℂ := fun g h =>
    ∑' q : MulAction.orbitRel.Quotient Eˣ (IsoV σ X), -thetaSum F (eA (om (γ q.out * g, h) Φ)) with hL
  have hlines : ∀ g h, (Summable fun x => thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g)) →
      ∑' x, thv B M om eA (shiftA H H' 1) Φ h (γ x * g) - c * ∑' x, thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g) = L g h := by
    intro g h hsB
    have hsA : Summable fun x => thv B M om eA (shiftA H H' 1) Φ h (γ x * g) := (k1 g).1 h
    rw [← tsum_mul_left, ← hsA.tsum_sub (hsB.mul_left c), orbit_sum isoAct_free (hsA.sub (hsB.mul_left c))]
    refine tsum_congr fun q => ?_
    have hΨ := pair_pres hp (γ q.out * g, h) hs
    obtain ⟨sA, sB, e2⟩ := h2' _ hΨ
    have vA : ∀ ξ : Eˣ, thv B M om eA (shiftA H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [(lawsTA hp hmA fun m hm => (hu m hm).1).mult hD hU hTB hp hp₀ hH (hsch heA _) hs hγ h g q.out ξ ξ (map_inv _ _).symm
        (by simp only [MonoidHom.inv_apply, hp.hW.2 ξ, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec]
      rfl
    let φ : Eˣ ≃ Eˣ := (Equiv.inv Eˣ).trans (conjE hp.base.cm)
    have vB : ∀ ξ : Eˣ, thv B M om eB (shiftB σ H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [lB.toLawsT.mult hD hU hTB hp hp₀ hH (hsch heB _) hs hγ h g q.out ξ ξ⁻¹ rfl
        (by simp only [hp.hW.2 ξ⁻¹, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec, shiftB]
      congr 4
    simp only [vA, vB]
    have sA' : Summable fun ξ : Eˣ => thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y))
        (om (γ q.out * g, h) Φ))) := sA.comp_injective Units.val_injective
    have sB' : Summable fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x))
        (om (γ q.out * g, h) Φ))) := (sB.comp_injective Units.val_injective).comp_injective φ.injective
    rw [sA'.tsum_sub (sB'.mul_left c), tsum_mul_left,
      φ.tsum_eq fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))),
      units_sum sA, units_sum sB, e2]
    have z0 : ∀ v : Matrix (Fin n) (Fin d) E, incM F ((0 : E) • v) = 0 := fun v => by rw [incM_smul, map_zero, zero_smul]
    have zB := (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ eB heB _
      (hst (γ q.out * g, h) Φ hΦ)).1
    simp only [z0, rho_zero, zB]
    simp [thetaSum]
  obtain ⟨Cd, kd, hdec⟩ := hSD F E σ B n d X W M χX χW om _ _ _ _ hp Φ hΦ 0
  have hvol := hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hs
    ⟨Cd * (M.μ M.dom).toReal, kd, fun h => by
      calc _ ≤ ∫⁻ _ in M.dom, ENNReal.ofReal (Cd * (ht h : ℝ) ^ kd) ∂M.μ := lintegral_mono fun g => by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (by simpa using hdec g h)
        _ = _ := by
            rw [setLIntegral_const, mul_right_comm, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol.ne]⟩
    _ fun g => (k1 g).2
  refine ⟨fun h => ∫ g in M.dom, (C₀ * thetaSum F (e₀ (om (g, h) Φ)) + C₁ * L g h) ∂M.μ,
    fun h => C₁ * c * κ * coneI B M om M₀ om₀ eB K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1, ?_, fun t m hm h => ?_,
    fun t m hm h => by dsimp only; rw [b2 t 1 m hm h]; ring, fun h₁ p hl h => ⟨?_, fun hso => ?_⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨a1, a2, a3⟩ := b1 h
    rw [Pi.add_apply, mul_assoc (C₁ * c), ← a3, ← integral_const_mul, ← eq_sub_iff_add_eq, ← integral_sub (f1 h) (a2.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [a1] with g hg
    rw [← hlines g h hg]
    simp only [thv]
    ring
  · dsimp only
    rw [← integral_const_mul]
    congr 1
    funext g
    have m1 : ∀ g', om (g', m * h) Φ = om (1, m) (om (g', h) Φ) := fun g' => by simp [om_mul]
    have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ 1 t 1 m hm 1 (one_mem _) _
      (pair_pres hp (g, h) hs)
    rw [one_mul] at m2
    simp only [hL, m1, m2, hmA.levi (levi_one H) hm (pair_pres hp _ hs), thetaSum_smul', ← Prod.one_eq_mk, map_one,
      Module.End.one_apply, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, one_mul, ← mul_neg, tsum_mul_left]
    ring
  · dsimp only
    rw [b2 1 h₁ p hl h, b3]
    simp
  · have hz0 : ∀ g, L g (p * h) = 0 := fun g => by
      have : ∀ g', eA (om (g', p * h) Φ) = 0 := fun g' => by
        refine hZ F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ M₁ hM₁
          ⟨χX, χW, om₁, om₀, _, _, _, _, _, _, hp₁, hp₀⟩ e₀ eA he₀ heA _ (pair_pres hp _ hs) ?_
        have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ g' 1 h₁ p hl 1 (one_mem _) _
          (pair_pres hp (1, h) hs)
        rw [one_mul, om_mul, Prod.mk_mul_mk, mul_one] at m2
        rw [m2]
        exact Submodule.smul_mem _ _ (hSt F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ _ _ hso)
      simp [hL, this, thetaSum]
    simp only [hz0, mul_zero, add_zero]
    exact (zero_term hMW hTB hp hp₁ hH' he₀ hch C₀ hs).2 h₁ p hl h

end PositivityTheory.ThKCT

end
