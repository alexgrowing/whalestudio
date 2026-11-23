import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Kcompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt

noncomputable section

namespace PositivityTheory.ThKU.Vac

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}

variable (σ) in

def KSub (X : Spc F E n) (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := KAt σ X v
  one_mem' := GlobalTheory.InertSph.one_mem_KAt σ X v
  mul_mem' := fun {a b} ha hb => ⟨(USub' σ X v).mul_mem ha.1 hb.1, fun y hy => ⟨by
    rw [show mat (a * b) = mat a * mat b from rfl, ← Matrix.mulVec_mulVec]; exact (ha.2 _ (hb.2 y hy).1).1, by
    rw [mul_inv_rev, show mat (b⁻¹ * a⁻¹) = mat b⁻¹ * mat a⁻¹ from rfl, ← Matrix.mulVec_mulVec]
    exact (hb.2 _ (ha.2 y hy).2).2⟩⟩
  inv_mem' := fun {a} ha => ⟨(USub' σ X v).inv_mem ha.1, fun y hy => ⟨(ha.2 y hy).2, by rw [inv_inv]; exact (ha.2 y hy).1⟩⟩

section Alg

variable {R A α β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype α] [Fintype β]

theorem symp_dblW (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (x₁ x₂ y₁ y₂ : Matrix α β A) :
    symp c ξ JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = symp c ξ JA JB x₁ y₁ - symp c ξ JA JB x₂ y₂ := by
  rw [symp, hTens_dbl, mul_sub, map_sub]; rfl

end Alg

theorem dbl_eigenW {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} {φ} (hφ : M.IsVac B.ψ v φ)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))}
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd) {omd}
    (hsp : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd) (g : UG (cA σ) (dbl (incM F W.J)))
    (hg : At (evFin F v) (g.1.1 - 1)) (hg' : PresD v W (g⁻¹).1.1) :
    ∃ c : ℂ, Acts (evFin F v) (omd g) (boxFun φ (star φ)) (c • boxFun φ (star φ)) := by
  obtain ⟨hs, h0, θ, -, hθ⟩ := hφ
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have hv : ∀ γ ∈ latAtV X W v, schr (psiAt B.ψ v) (locCo M.co v γ) φ = _ := fun γ hγ =>
    (eq_of_acts v h₁ (h₀ φ hs) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)).trans
      (eq_of_acts v h₁ (h₀ φ hs) (hθ γ hγ)).symm
  set θ' := inclR (F := F) (AF F) (θ : E)
  refine eigen dd hB.std {z | ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, z = Matrix.fromCols γ₁ γ₂} ?_ ?_
    (fun z => B.ψ (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (dbl (incM F W.J)) z z)) (sb_box_loc hs (sb_star hs)) ?_ ?_
    (omd g) (hsp.pres g) (hsp.adm g) (actB (cA σ) g) (hsp.impl g) ?_ ?_
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩ u hu
    ext i (j | j)
    exacts [congrFun (congrFun (hAt _ h1 u hu) i) j, congrFun (congrFun (hAt _ h2 u hu) i) j]
  · intro z hz h
    have ez : z = Matrix.fromCols z.toCols₁ z.toCols₂ := (Matrix.fromCols_toCols z).symm
    refine ⟨_, mem_latAtV hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, _, mem_latAtV hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, ez⟩
    · ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inl j)
    · have := h _ ⟨γ, hγ, 0, zero_mem _, rfl⟩
      rwa [ez, symp_dblW, symp_zero, sub_zero] at this
    · ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inr j)
    · have := h _ ⟨0, zero_mem _, -γ, neg_mem hγ, rfl⟩
      rwa [ez, symp_dblW, symp_zero, zero_sub, ← neg_one_smul (AF F) γ, symp_smul, neg_one_mul, neg_neg] at this
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    exact fun e => mul_ne_zero hx (star_ne_zero.2 hx) (congrFun e (Sum.elim x x))
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    have e : locCo dd v (Matrix.fromCols γ₁ γ₂) = (Sum.elim (locCo M.co v γ₁).1 (locCo M.co v γ₂).1,
        Sum.elim (locCo M.co v γ₁).2 (-(locCo M.co v γ₂).2)) := by
      have := hdd γ₁ γ₂
      ext (i | i) <;> simp [locCo, this]
    have a2 : At (evFin F v) (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (incM F W.J) γ₂ γ₂) := fun u hu => by
      rw [smul_eq_mul, mul_left_comm, ← symp_smul, hAt _ h2 u hu, symp_zero, mul_zero]
    rw [e, schr_box hB.std, hv _ h1, hv _ h2, symp_dblW, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_psi hB.std a2]
    funext x
    simp only [boxFun, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  · intro u hu
    have : u * (g.1.1 - 1)ᵀ = 0 := by
      rw [← idem_smul hg, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul]
      change (sg v 1 • u) * _ = 0
      rw [hu, Matrix.zero_mul]
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, e, he, eg⟩ := hg'
    refine ⟨Matrix.fromCols γ₁ γ₂ * ((g⁻¹).1.1)ᵀ, ⟨γ₁ * aᵀ + γ₂ * bᵀ, add_mem (latAtV_mul ha h1) (latAtV_mul hb h2),
      γ₁ * cᵀ + γ₂ * eᵀ, add_mem (latAtV_mul hc h1) (latAtV_mul he h2), ?_⟩, ?_, ?_⟩
    · rw [eg, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
    · have : g.1.1 * (g⁻¹).1.1 = 1 := g.1.mul_inv
      rw [actB, Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, hTens_mul (cA σ) _ (g⁻¹).2]

theorem vacFixW {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ) {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil B.ψ χX χW om) (hv : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w)
    {k : UA σ W.J} (hk₀ : k ∈ GlobalTheory.InertSph.KAt σ W v) : Acts (evFin F v) (om (1, k)) (M.vac v) (M.vac v) := by
  set K := KSub σ W v
  have hk : k ∈ K := hk₀
  have hL := hW.lat
  have hs := IsUWeilPair.isUSplitting hw
  have hKc : IsCompact (K : Set (UA σ W.J)) := isCompact_KAt W hL v
  have hU : ∀ k ∈ K, k ∈ UAt σ W (evFin F v) := fun k hk => hk.1
  have hP : ∀ k ∈ K, mat k ∈ Pres v W := fun k hk z hz => (hk.2 z hz).1
  obtain ⟨hsb, h0, θ, hθ1, hθ⟩ := hM.vac v
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have eig : ∀ k ∈ K, ∃ c : ℂ, Acts (evFin F v) (om (1, k)) (M.vac v) (c • M.vac v) := fun k hk =>
    vacuum_eigenline_of_local locRepEx F E σ n d B X W M om ⟨hB, ⟨_, _, hX⟩, ⟨_, _, hW⟩, hM, _, _, hw⟩ v k hk
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y) = M.vac v y := by
    change M.vac v (evA _ v (putA v x₀ y)) * r₀ (putA v x₀ y) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have bd : ∀ k ∈ K, ∀ c : ℂ, om (1, k) Φ = c • Φ → ‖c‖ ≤ 1 := fun k hk c hc => by
    refine norm_eq_one hKc (f := fun g => (LinearMap.proj y ∘ₗ res v x₀) (om (1, g) Φ))
      ((hs.cont _ (res_adm v x₀ _) _ hΦs).comp (continuous_const.prodMk continuous_id)) hk (a := M.vac v y) hy fun j => ?_
    have : om (1, k ^ j) Φ = c ^ j • Φ := by
      induction j with
      | zero => rw [pow_zero, pow_zero, one_smul, Prod.mk_one_one, map_one]; rfl
      | succ j ih =>
        rw [show ((1, k ^ (j + 1)) : UA σ X.J × _) = (1, k ^ j) * (1, k) by simp [pow_succ], map_mul, Module.End.mul_apply, hc,
          map_smul, ih, smul_smul, pow_succ']
    rw [this, map_smul, smul_eq_mul, ← hΦy]; rfl
  obtain ⟨c, hc⟩ := eig k hk
  have hcΦ : om (1, k) Φ = c • Φ := by rw [hΦ, hc r₀ (h₀ _ hsb), tens_smul]
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨⟨-, dd, omd, hdd, ⟨-, hsp, hrule⟩, hres⟩, -, -⟩ := hw
  obtain ⟨b, b', f', b1, b2, hb, pb, pf, hf⟩ := exists_beta hB hL k (hU k hk) (hP k hk) (hP _ (inv_mem hk))
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin d) (incM F W.J) k
  have hm : At (evFin F v) (1 - mat k) := by simpa using at_sub at_zero (hU k hk)
  have pm : 1 - mat k ∈ Pres v W := sub_mem (one_mem _) (hP k hk)
  have hJ : incM F W.J * incM F W.J⁻¹ = 1 := by
    change W.J.map (inclR (F := F) (AF F)) * W.J⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AE F E)), Matrix.mul_nonsing_inv _ (skew_det hW)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨s₀, n₀, p, t, ss, eg, es, en, en', hn, hp, et, et'⟩ :=
    exists_decomp hJ k b1 b2 hb hf (ε := Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm) gd hgd
  have o1 := one_mem (Pres v W)
  have z0 := zero_mem (Pres v W)
  have pC : PresD v W (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v W (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (Vf.eps v : AE F E) = 1 := by rw [Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v W := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v W :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have vd : M.IsVac B.ψ v (M.vac v) := ⟨hsb, h0, θ, hθ1, hθ⟩
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F W.J)), At (evFin F v) (g.1.1 - 1) → PresD v W (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := dbl_eigenW hB hX hW vd hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (Vf.eps v : AE F E) = 0 := at_eps u hu
      ext (i | i) (j | j) <;> simp [SS, Matrix.one_apply, smul_ite, this, apply_ite (u • ·)] <;> split_ifs <;> simp [this])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have := at_mul_right f' hm u hu
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [show u • (f' * (1 - k.1.1)) = 0 from this, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pf pm, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    have := congrArg (GlobalTheory.DiagForm.lDiag F _) e
    rw [map_smul, smul_eq_mul] at this
    exact (mul_right_cancel₀ (lDiag_ne hΦs hΦ0) (this.symm.trans (one_mul _).symm))
  have e1 : omd gd (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    rw [hres k gd hgd Φ hΦs _ (star_mem_schA hΦs)]
    change boxFun (om (1, k) Φ) _ = _
    rw [hcΦ]; funext x; simp [boxFun, mul_assoc]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * gd := by rw [eg]; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χX hv t
    (by rw [et]; exact add_mem o1 (mul_mem pb pm)) (by rw [et']; exact sub_mem o1 (mul_mem pb (mul_mem pf pm)))
    (by rw [et, add_sub_cancel_left]; exact at_mul_right _ hm)) hΦs hΦ0 e2
  obtain ⟨c', hc'⟩ := eig k⁻¹ (inv_mem hk)
  have hc'Φ : om (1, k⁻¹) Φ = c' • Φ := by rw [hΦ, hc' r₀ (h₀ _ hsb), tens_smul]
  have cc : c * c' = 1 := by
    have e : om ((1, k⁻¹) * (1, k)) Φ = (c * c') • Φ := by rw [map_mul, Module.End.mul_apply, hcΦ, map_smul, hc'Φ, smul_smul]
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at e
    have := congrFun e (putA v x₀ y)
    rw [Pi.smul_apply, hΦy, smul_eq_mul] at this
    exact mul_right_cancel₀ hy (this.symm.trans (one_mul _).symm)
  have n1 := bd k hk c hcΦ
  have n2 := bd _ (inv_mem hk) c' hc'Φ
  have n3 : ‖c‖ * ‖c'‖ = 1 := by rw [← norm_mul, cc, norm_one]
  have n4 : ‖c‖ = 1 := le_antisymm n1 (by nlinarith [norm_nonneg c, norm_nonneg c'])
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]

theorem vacFixX {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ) {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil B.ψ χX χW om) (hv : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χW w)
    {k : UA σ X.J} (hk₀ : k ∈ GlobalTheory.InertSph.KAt σ X v) : Acts (evFin F v) (om (k, 1)) (M.vac v) (M.vac v) := by
  set K := KSub σ X v
  have hk : k ∈ K := hk₀
  have hL := hX.lat
  have hs := IsUWeilPair.isUSplitting hw
  have hKc : IsCompact (K : Set (UA σ X.J)) := isCompact_KAt X hL v
  have hU : ∀ k ∈ K, k ∈ UAt σ X (evFin F v) := fun k hk => hk.1
  have hP : ∀ k ∈ K, mat k ∈ Pres v X := fun k hk z hz => (hk.2 z hz).1
  obtain ⟨hsb, h0, θ, hθ1, hθ⟩ := hM.vac v
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have eig : ∀ k ∈ K, ∃ c : ℂ, Acts (evFin F v) (om (k, 1)) (M.vac v) (c • M.vac v) := fun k hk => by
    refine eigen M.co hB.std (latAtV X W v) hAt (fun z hz h => mem_latAtV hB hX hW v hz h) _ hsb h0
      (fun γ hγ => (eq_of_acts v h₁ (h₀ _ hsb) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) _)).trans
        (eq_of_acts v h₁ (h₀ _ hsb) (hθ γ hγ)).symm) (om (k, 1)) (hs.pres _) (hs.adm _) (actAB (cA σ) (k, 1)) (hs.impl _)
      (fun u hu => act_away (hU k hk) (PositivityTheory.ThKH.Locrep.one_mem_UAt W v) hu) fun γ hγ => ⟨mat k⁻¹ * γ, mul_latAtV (hP _ (inv_mem hk)) hγ, ?_, ?_⟩
    · have : mat k * mat k⁻¹ = 1 := k.1.mul_inv
      change mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ
      rw [← Matrix.mul_assoc, this, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, ← hTens_tr, ← hTens_tr _ _ _ γ, Matrix.transpose_mul, hTens_mul (cA σ) _ (k := mat k⁻¹) (k⁻¹).2]
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y) = M.vac v y := by
    change M.vac v (evA _ v (putA v x₀ y)) * r₀ (putA v x₀ y) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have bd : ∀ k ∈ K, ∀ c : ℂ, om (k, 1) Φ = c • Φ → ‖c‖ ≤ 1 := fun k hk c hc => by
    refine norm_eq_one hKc (f := fun g => (LinearMap.proj y ∘ₗ res v x₀) (om (g, 1) Φ))
      ((hs.cont _ (res_adm v x₀ _) _ hΦs).comp (continuous_id.prodMk continuous_const)) hk (a := M.vac v y) hy fun j => ?_
    have : om (k ^ j, 1) Φ = c ^ j • Φ := by
      induction j with
      | zero => rw [pow_zero, pow_zero, one_smul, Prod.mk_one_one, map_one]; rfl
      | succ j ih =>
        rw [show ((k ^ (j + 1), 1) : _ × UA σ W.J) = (k ^ j, 1) * (k, 1) by simp [pow_succ], map_mul, Module.End.mul_apply, hc,
          map_smul, ih, smul_smul, pow_succ']
    rw [this, map_smul, smul_eq_mul, ← hΦy]; rfl
  obtain ⟨c, hc⟩ := eig k hk
  have hcΦ : om (k, 1) Φ = c • Φ := by rw [hΦ, hc r₀ (h₀ _ hsb), tens_smul]
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨-, ⟨d', hd', -, dd, omd, hdd, ⟨-, hsp, hrule⟩, hres⟩, -⟩ := hw
  obtain ⟨b, b', f', b1, b2, hb, pb, pf, hf⟩ := exists_beta hB hL k (hU k hk) (hP k hk) (hP _ (inv_mem hk))
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin n) (incM F X.J) k
  have hm : At (evFin F v) (1 - mat k) := by simpa using at_sub at_zero (hU k hk)
  have pm : 1 - mat k ∈ Pres v X := sub_mem (one_mem _) (hP k hk)
  have hJ : incM F X.J * incM F X.J⁻¹ = 1 := by
    change X.J.map (inclR (F := F) (AF F)) * X.J⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AE F E)), Matrix.mul_nonsing_inv _ (herm_det hX)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨s₀, n₀, p, t, ss, eg, es, en, en', hn, hp, et, et'⟩ :=
    exists_decomp hJ k b1 b2 hb hf (ε := Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm) gd hgd
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (Vf.eps v : AE F E) = 1 := by rw [Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have vd : M.IsVac B.ψ v (M.vac v) := ⟨hsb, h0, θ, hθ1, hθ⟩
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := dbl_eigen hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (Vf.eps v : AE F E) = 0 := at_eps u hu
      ext (i | i) (j | j) <;> simp [SS, Matrix.one_apply, smul_ite, this, apply_ite (u • ·)] <;> split_ifs <;> simp [this])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have := at_mul_right f' hm u hu
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [show u • (f' * (1 - k.1.1)) = 0 from this, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pf pm, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    have := congrArg (GlobalTheory.DiagForm.lDiag F _) e
    rw [map_smul, smul_eq_mul] at this
    exact (mul_right_cancel₀ (lDiag_ne hΦs hΦ0) (this.symm.trans (one_mul _).symm))
  have e1 : omd gd (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    rw [hres k gd hgd Φ hΦs _ (star_mem_schA hΦs)]
    change boxFun (om (k, 1) Φ) _ = _
    rw [hcΦ]; funext x; simp [boxFun, mul_assoc]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * gd := by rw [eg]; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χW hv t
    (by rw [et]; exact add_mem o1 (mul_mem pb pm)) (by rw [et']; exact sub_mem o1 (mul_mem pb (mul_mem pf pm)))
    (by rw [et, add_sub_cancel_left]; exact at_mul_right _ hm)) hΦs hΦ0 e2
  obtain ⟨c', hc'⟩ := eig k⁻¹ (inv_mem hk)
  have hc'Φ : om (k⁻¹, 1) Φ = c' • Φ := by rw [hΦ, hc' r₀ (h₀ _ hsb), tens_smul]
  have cc : c * c' = 1 := by
    have e : om ((k⁻¹, 1) * (k, 1)) Φ = (c * c') • Φ := by rw [map_mul, Module.End.mul_apply, hcΦ, map_smul, hc'Φ, smul_smul]
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at e
    have := congrFun e (putA v x₀ y)
    rw [Pi.smul_apply, hΦy, smul_eq_mul] at this
    exact mul_right_cancel₀ hy (this.symm.trans (one_mul _).symm)
  have n1 := bd k hk c hcΦ
  have n2 := bd _ (inv_mem hk) c' hc'Φ
  have n3 : ‖c‖ * ‖c'‖ = 1 := by rw [← norm_mul, cc, norm_one]
  have n4 : ‖c‖ = 1 := le_antisymm n1 (by nlinarith [norm_nonneg c, norm_nonneg c'])
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]

end PositivityTheory.ThKU.Vac

end
