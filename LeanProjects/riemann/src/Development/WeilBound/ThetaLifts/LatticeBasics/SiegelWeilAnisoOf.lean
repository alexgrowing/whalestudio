import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {ψ : AddChar (AF F) ℂ}

theorem theta_inj (hψ : IsStd ψ) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) (h : ∀ w, thetaSum F (schr ψ w φ) = 0) : φ = 0 := by
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
  have r0 : rt (0 : κ → F) = 0 := funext fun _ => map_zero _
  funext x
  have key := GlobalTheory.SchrodingerUniq.coeff_zero_eq_zero (χ := fun (y : κ → AF F) (ξ : κ → F) => ψ (rt ξ ⬝ᵥ y))
    (c := fun ξ => φ (rt ξ + x)) (fun y ξ => hn _) (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [r0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      refine ⟨Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀), ?_⟩
      beta_reduce
      rwa [dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul])
    (by convert summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hφ) using 1) fun y => by
      have hb : ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) ≠ 0 := norm_ne_zero_iff.1 (by rw [hn]; exact one_ne_zero)
      refine (mul_eq_zero.1 (Eq.trans ?_ (h (x, y)))).resolve_left hb
      rw [← tsum_mul_left, thetaSum]
      refine tsum_congr fun ξ => ?_
      simp only [schr, AddChar.map_add_eq_mul]
      ring
  simpa [r0] using key

theorem schr_schr (w w' : (κ → AF F) × (κ → AF F)) : ∃ c : ℂ, ∀ φ, schr ψ w (schr ψ w' φ) = c • schr ψ (w + w') φ :=
  ⟨ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)), fun φ => funext fun x => by
    simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc,
      add_dotProduct, dotProduct_add]
    congr 2
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : AF F)⟩

variable {dd} {χ : Chr F E} {om S l}

theorem dbl_inj (hψ : IsStd ψ) (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {Φ} (hΦ : Φ ∈ schA F κ)
    (h0 : ∀ w, l (dd.rho ψ w Φ) = 0) : Φ = 0 := theta_inj hψ hΦ fun w => by
  obtain ⟨w, rfl⟩ := dd.e.surjective w
  refine (h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ)).unique (by
    convert hasSum_zero with y
    obtain ⟨c, e⟩ := schr_schr (ψ := ψ) (dd.e (incM F (Matrix.fromCols y (-y)))) (dd.e w)
    rw [Darboux.rho, e, map_smul, ← map_add, ← Darboux.rho, h0, smul_zero])

theorem dbl_comm (hψ : IsStd ψ) (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {p t} (hp : IsPar p t) (g)
    {Φ} (hΦ : Φ ∈ schA F κ) : om p (S g Φ) = S g (om p Φ) := by
  have hw := h.weil.2.1
  have mem : ∀ w, ∀ Φ ∈ schA F κ, dd.rho ψ w Φ ∈ schA F κ := fun w => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _
  refine sub_eq_zero.1 (dbl_inj hψ h (sub_mem (hw.pres _ _ (h.lin.pres g Φ hΦ)) (h.lin.pres _ _ (hw.pres p Φ hΦ))) fun w => ?_)
  obtain ⟨w, rfl⟩ : ∃ w', w = mat g * actB (cA σ) p w' := ⟨mat g⁻¹ * actB (cA σ) p⁻¹ w, by
    simp [actB, mat, Matrix.mul_assoc, ← Matrix.transpose_mul]⟩
  have law := h.weil.2.2 l h.adm h.kill p t hp
  rw [show ∀ w (a b : (κ → AF F) → ℂ), dd.rho ψ w (a - b) = dd.rho ψ w a - dd.rho ψ w b from
      fun w a b => funext fun x => mul_sub _ _ _, map_sub, ← h.lin.impl g _ _ (hw.pres p Φ hΦ), ← hw.impl p w Φ hΦ,
    h.fix g _ (hw.pres _ _ (mem w Φ hΦ)), law _ (mem w Φ hΦ),
    show mat g * actB (cA σ) p w = actB (cA σ) p (mat g * w) from (Matrix.mul_assoc _ _ _).symm,
    ← hw.impl p _ _ (h.lin.pres g Φ hΦ), ← h.lin.impl g w Φ hΦ, law _ (h.lin.pres g _ (mem w Φ hΦ)), h.fix g _ (mem w Φ hΦ),
    sub_self]

theorem sw_transl (h1 : SiegelWeilStd) (h2 : FrameConj) {r s r' s'} (hB : B.IsGood σ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h0 : min r s = 0)
    (hA : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') (hχ : IsHecke F E χ)
    (hc : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {dd om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l) {K a} (hK : IsStab2 B K) (ha : IsHgt K a)
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ A.J) D μ)
    {Φ} (hΦ : Φ ∈ kfin om K) : EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
      fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  obtain ⟨N, _, n0, n1, n2⟩ := hΦ
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r' s' hB (hA.symm.imp And.right And.right) K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have mul : ∀ x y Ψ, om x (om y Ψ) = om (x * y) Ψ := fun x y Ψ => by rw [map_mul, Module.End.mul_apply]
  intro x
  obtain ⟨e, e1, ⟨t₁, e2⟩, e3, e4⟩ := h1 F E σ B m n A Y r s r' s' hB hm hn h0 hA χ hχ hc _ dd om S l h b K₀ _ hb hK₀ ha₀ μ D hμ hD
    (om p⁻¹ Φ) (h.weil.2.1.pres _ _ (n0 n1)) (Submodule.finiteDimensional_of_le (S₂ := N.map (om p⁻¹)) (Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, n2 _ (hk' k k.2) Φ n1, by simp only [mul]; congr 2; group⟩))) (x * p)
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) :=
    (differentiable_id.const_sub _).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine ⟨fun z => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) * e z, fun z hz => (dc.analyticAt z).meromorphicAt.mul (e1 z hz),
    ⟨t₁, fun z hz => ?_⟩, (dc.analyticAt _).mul e3, ?_⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mpr ((e2 z hz).mul_left ((d : ℂ) ^ (((m : ℂ) - n) / 2 - z)))
    simp only [eisTerm, flat, mul, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · simp only [e4, sub_self, Complex.cpow_zero, one_mul, ← dbl_comm hB.std h hp.inv _ (n0 n1), mul, mul_inv_cancel_right]

theorem _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of (h1 : SiegelWeilStd) (h2 : FrameConj) (hL : FinLevel) (hC : Stab2Cpt) :
    SiegelWeilAniso := by
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hc dd om S l hd h K a hK ha Φ₁ p1 Φ₂ p2
    refine sw_transl h1 h2 hB hm hn h0 (.inl ⟨hA, hY⟩) hχ hc h hK ha hM.haar hM.dom
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
    · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf
  · intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd' hX hW h0 hM χ hχ hc dd om S l ⟨d', ht, hd⟩ h K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
    have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
      rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
    refine sw_transl h1 h2 hB hd' hn h0 (.inr ⟨hW, hX⟩) hχ hc h hK ha hμ hD
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
      refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
      rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    · rw [actsD_unique' M hB.std hu e]
      have := n2 uᵀ (tr hu) f hf
      rwa [ht] at this

end GlobalTheory.ThK.Dbl.Box

end
