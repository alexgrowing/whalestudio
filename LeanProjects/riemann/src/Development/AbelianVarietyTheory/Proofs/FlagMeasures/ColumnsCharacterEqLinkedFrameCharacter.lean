import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem mem_mL_of_coprime_smul (I : AutInst) (g c : ℕ) (hc : Nat.Coprime c g) {v : VA I} (hv : v ∈ I.Lf)
    (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ mL I g) : v ∈ mL I g := by
  have hb : ((c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have hR1 : ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * (c : I.E ⊗[I.F] Af I.F) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
    have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hb
    push_cast at this
    linear_combination this
  have e : v = ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((c : I.E ⊗[I.F] Af I.F) • v) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hR1, one_smul]
  have hint : ∀ n : ℤ, ∀ w ∈ mL I g, ((n : I.E ⊗[I.F] Af I.F)) • w ∈ mL I g := fun n w hw =>
    (mL I g).smul_mem (⟨(n : I.E ⊗[I.F] Af I.F), intCast_mem _ n⟩ : IntAf I.F I.E) hw
  rw [e]
  exact add_mem (hint _ _ hcv) (hint _ _ (smul_mem_mL I hv))

theorem iota_symm_inv_g {D : D7} (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) =
      algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹) := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  have hG : D.host.g 0 * D.host.g 1 = X.B.g := X.g_eq.symm
  have h1 : algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹) * ((X.B.g : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) = 1 := by
    rw [← hG, ← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hG ▸ hg)), map_one]
  have ha : ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ιA.symm, ← map_mul, h1, map_one]
  have hb := inv_g X.B.I X.B.g hg
  set a := ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹))
  set b := algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹)
  calc a = a * (b * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by rw [hb, mul_one]
    _ = (a * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * b := by ring
    _ = b := by rw [ha, one_mul]

theorem hA_pair_cong (I : AutInst) (g : ℕ) (H : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hH : ∀ z ∈ mL I g, H *ᵥ z ∈ mL I g) (P P' Q Q' : VA I) (hPP : P - P' ∈ mL I g) (hQQ : Q - Q' ∈ mL I g)
    (hP' : P' ∈ I.Lf) (hHQ : H *ᵥ Q ∈ I.Lf) :
    ZMod' I g (hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q')) := by
  have e : hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q') = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ (Q - Q')) := by
    have e1 : hA I P (H *ᵥ Q) = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ Q) := by
      rw [← hA_add_left, sub_add_cancel]
    rw [e1, Matrix.mulVec_sub, hA_sub_right]; ring
  rw [e]
  refine Z_add I g ?_ ?_
  · rw [hA_symm I (H *ᵥ Q)]
    exact Z_sig I g (mL_Qs I g hHQ hPP)
  · exact mL_Qs I g hP' (hH _ hQQ)

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem chi_link (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (Fr : FrQ D wt)
    (hL : FrLink X u wt ιA Fr)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) :
    X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) = Fr.chi y.1 := by
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  unfold AdFrame.chi
  rw [hpsi, map_mul, iota_symm_inv_g X ιA]
  rfl

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem psiK_eq_chi : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  intro D X u wt ιA hW hI hK Fr hL h y hRep hk
  obtain ⟨hlat, hform, -, -, -, hrep⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  obtain ⟨κ, hκdef⟩ : ∃ κ : X.B.I.Gf, κ = (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u := ⟨_, rfl⟩
  have hκ : κ ∈ X.K2 := by rw [hκdef]; exact hk
  have hκK : κ ∈ X.B.I.Kset := hκ.1
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hxκ : X.xu u * κ = (h : X.B.I.Gf) * X.xu u := by rw [hκdef]; group
  have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    have e : (h : X.B.I.Gf) = X.xu u * κ * (X.xu u)⁻¹ := by rw [hκdef]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hκK) (K_inv _ hxK)

  have hpres : ∀ x : X.B.I.Gf, x ∈ X.B.I.Kset → ∀ z ∈ mL X.B.I X.B.g, X.B.I.fmat x *ᵥ z ∈ mL X.B.I X.B.g :=
    fun x hx z hz => pres X.B.I hx X.B.g ∅ (mL X.B.I X.B.g) (by simp) (by simp) le_rfl z (mL_Mo X.B.I hz)
  have hpres1 : ∀ z ∈ mL X.B.I X.B.g, (X.B.I.fmat κ - 1) *ᵥ z ∈ mL X.B.I X.B.g :=
    fun z hz => pres1 X.B.I hκK X.B.g ∅ (mL X.B.I X.B.g) (by simp) le_rfl z (mL_Mo X.B.I hz)

  have hxinv : ∀ v : VA X.B.I, X.B.I.fmat (X.xu u) *ᵥ v = v → X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
    intro v hv
    calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
  have hfixE : ∀ b, X.B.I.fmat κ *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := by
    intro b
    have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := (X.xu_fix u b).1
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u b)
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, hxinv _ h1]
  have hfixZ : X.B.I.fmat κ *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) := by
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u)
    have hxx : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = incl X.B.I (X.zR u) := by
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul_inv, Matrix.one_mulVec]
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxx, h2]

  have key : ∀ v w : VA X.B.I, v ∈ X.B.I.Lf → X.B.I.fmat κ *ᵥ w = w →
      InAt X.B.I X.B.g X.B.g (v - w) → (X.B.I.fmat κ - 1) *ᵥ v ∈ mL X.B.I X.B.g := by
    intro v w hv hw hvw
    obtain ⟨c, hc, hcv⟩ := hvw
    refine mem_mL_of_coprime_smul X.B.I X.B.g c hc (K_sub_mv X.B.I hκK hv) ?_
    have hw0 : (X.B.I.fmat κ - 1) *ᵥ w = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_self]
    have e : (X.B.I.fmat κ - 1) *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v - w)) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat κ - 1) *ᵥ v) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hw0, sub_zero]
    rw [← e]; exact hpres1 _ hcv
  have hnxt : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    intro a
    unfold nxt
    split_ifs with ha
    · exact key _ _ (he0 _) (hfixE _) (X.basisApprox _).1
    · refine key _ _ hz0 hfixZ ?_
      obtain ⟨c, hc, hcv⟩ := X.xu_z u
      refine ⟨c, hc, ?_⟩
      have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
          -((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0)) := by
        rw [← smul_neg, neg_sub]
      rw [e]; exact neg_mem hcv

  have hterm : ∀ (i : Fin D.R.k) (hi : i.1 + 1 < D.R.k),
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) -
        ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩))) := by
    intro i hi
    generalize hj : (⟨i.1 + 1, hi⟩ : Fin D.R.k) = j
    have hT : ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b j)) =
        hA X.B.I (embA X wt ιA (Fr.bd i)) (X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA (Fr.b j)) := by
      rw [← hform, RingEquiv.symm_apply_apply, hrep h y hRep]
    have hT2 : hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j) =
        hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)
          (X.B.I.fmat (h : X.B.I.Gf) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw j)) := by
      rw [← Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X (X.xu u) (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← fmat_mul, ← fmat_mul, hxκ]
    rw [hT, hT2]
    refine hA_pair_cong X.B.I X.B.g _ (hpres _ hhK) _ _ _ _ ?_ ?_ ((hlat (Fr.bd i)).1 (Fr.bd_mem i))
      (K_mv X.B.I hhK (K_mv X.B.I hxK (hbw j)))
    · have := neg_mem (hL.2.2.1 i); rwa [neg_sub] at this
    · have := neg_mem (hL.2.1 j); rwa [neg_sub] at this

  have hZ : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
      ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
        Fr.b Fr.bd y.1.1) - 0) := by
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
        ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
          Fr.b Fr.bd y.1.1) - 0 =
        (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) +
        ∑ i : Fin D.R.k, ((if hi : i.1 + 1 < D.R.k then
            hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) else 0) -
          ιA.symm (if hi : i.1 + 1 < D.R.k then
            hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
              (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩) else 0)) := by
      simp only [Afun, supSum, map_sum, Finset.sum_sub_distrib]; ring
    rw [e]
    refine Z_add X.B.I X.B.g (Z_sum X.B.I X.B.g _ _ fun a _ => ?_) (Z_sum X.B.I X.B.g _ _ fun i _ => ?_)
    · exact congruence_fixed_term X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
        (mL_Qs X.B.I X.B.g (hf0 a) (hnxt a))
    · by_cases hi : i.1 + 1 < D.R.k
      · simp only [dif_pos hi]; exact hterm i hi
      · simp only [dif_neg hi, map_zero, sub_self]; exact Z_zero X.B.I X.B.g
  have h0 : X.psiEf (divN X.B.I X.B.g 0) = 1 := by
    rw [divN, mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  calc ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ)
      = X.psiEf (divN X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ)) := by rw [hκdef]; rfl
    _ = X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
          (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) := by
      have hE := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
      rw [h0, mul_one] at hE
      exact hE
    _ = Fr.chi y.1 := by
      exact chi_link D X u wt ιA Fr hL y

end GlobalTheory.St.G.ColChar
