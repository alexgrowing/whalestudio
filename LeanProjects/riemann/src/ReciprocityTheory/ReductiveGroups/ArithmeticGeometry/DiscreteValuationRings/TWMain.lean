import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation QForm

set_option maxHeartbeats 800000 in

theorem tw_of (hG : GlobalFnsSt) (hTW : TwistBCSpanStatement) (hVR : VRatioGtStatement) : TWStatement := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk p w hw ζ hζ
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have alg : ∀ {Rg : Type} [CommRing Rg] (X Y : Rgˣ) (g g' e : Rg), X.val = g * Y.val → g * g' = e →
      e * g = g → (X⁻¹).val = g' * (Y⁻¹).val := by
    intro Rg _ X Y g g' e h3 h4 h5
    linear_combination (g' * (Y⁻¹).val - (X⁻¹).val * (1 - e)) * Units.inv_mul X -
      (g' * (X⁻¹).val * g) * Units.mul_inv Y +
      (-(g' * (Y⁻¹).val * (X⁻¹).val) - (X⁻¹).val * (X⁻¹).val * e + (X⁻¹).val * (X⁻¹).val) * h3 -
      (X⁻¹).val * h4 - ((X⁻¹).val * (X⁻¹).val * Y.val) * h5
  have prodF : ∀ {T : Type} (U : Type) [CommGroup U] (h : T → U) (a b c d : T) (kk : ℕ),
      ∏ i, h (Sum.elim ![a, b, c, d] ![d, c] i) ^ (Sum.elim ![(-1 : ℤ), 1, 1, -1] ![(kk : ℤ), -(kk : ℤ)] i) =
        (h a)⁻¹ * h b * h c * (h d)⁻¹ * (h c ^ kk)⁻¹ * h d ^ kk := by
    intro T U _ h a b c d kk
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two]
    show (h a ^ (-1 : ℤ) * h b ^ (1 : ℤ) * h c ^ (1 : ℤ) * h d ^ (-1 : ℤ)) *
      (h d ^ (kk : ℤ) * h c ^ (-(kk : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    simp only [_root_.mul_assoc, _root_.mul_comm, _root_.mul_left_comm]
  have fwdF : ∀ {T : Type} (U : Type) [CommGroup U] (h : T → U) (P Bv : Fin 4 → T) (ε : Fin 4 → ℤ),
      ∏ x, h (Sum.elim P (Sum.elim Bv P) x) ^ (Sum.elim ε (Sum.elim ε (fun i => -ε i)) x) =
        ∏ i, h (Bv i) ^ ε i := by
    intro T U _ h P Bv ε
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [_root_.mul_left_comm, _root_.mul_inv_cancel, _root_.mul_one]
  have backF : ∀ {T : Type} (U : Type) [CommGroup U] (h : T → U) (P Bv : Fin 4 → T) (Ψ : Fin 4 ⊕ Fin 4 → T)
      (ε : Fin 4 → ℤ) (δ : Fin 4 ⊕ Fin 4 → ℤ), (∀ i, Ψ (Sum.inl i) = P i) → (∀ i, Ψ (Sum.inr i) = Bv i) →
      (∀ i, δ (Sum.inl i) = -ε i) → (∀ i, δ (Sum.inr i) = ε i) →
      ∏ x, h (Sum.elim P Ψ x) ^ (Sum.elim ε δ x) = ∏ i, h (Bv i) ^ ε i := by
    intro T U _ h P Bv Ψ ε δ h1 h2 h3 h4
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h1, h2, h3, h4, zpow_neg, Finset.prod_inv_distrib]
    exact _root_.mul_inv_cancel_left _ _
  obtain ⟨m, hm⟩ := exists_liftO (hϖ := hϖ) (hv := hv) (D := D) p.g.b
  have hmul : ∀ x y : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ (x * y) = (ιS hϖ hv ≫ x) * (ιS hϖ hv ≫ y) := by
    intro x y
    first
      | exact (preHom (G := D.toPre.P.A) (ιS hϖ hv)).map_mul x y
      | exact MonObj.comp_mul _ _ _
  have hone : ιS hϖ hv ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A) = 1 := by
    first
      | exact (preHom (G := D.toPre.P.A) (ιS hϖ hv)).map_one
      | exact MonObj.comp_one _
      | simp
  have hinv : ∀ x : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ x⁻¹ = (ιS hϖ hv ≫ x)⁻¹ := by
    intro x
    first
      | exact map_inv (preHom (G := D.toPre.P.A) (ιS hϖ hv)) x
      | simp
  have hpow : ∀ (x : TO hϖ hv ⟶ D.toPre.P.A) (n : ℕ), ιS hϖ hv ≫ x ^ n = (ιS hϖ hv ≫ x) ^ n := by
    intro x n
    first
      | exact map_pow (preHom (G := D.toPre.P.A) (ιS hϖ hv)) x n
      | exact (preHom (G := D.toPre.P.A) (ιS hϖ hv)).map_pow x n
  have hjf : jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A = fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    first | exact whiskerRight_fst _ _ | simp [jO]
  have hjs : jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A = snd (TF (R := V) F) D.toPre.P.A := by
    first | exact whiskerRight_snd _ _ | simp [jO]
  have hgsF : ∀ {Z : Scheme.{0}} (f : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (c : F),
      gs f z ⊤ (gF D.toPre F c) =
        gs (f ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := by
    intro Z f z c
    exact gs_pull f _ z ⊤ (by first | trivial | simp) _
  have hgsm : ∀ {Z : Scheme.{0}} (f : Z ⟶ (TF (R := V) F).left) (z : Z) (a b : F),
      gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a * b)) =
        gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) *
          gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom b) := by
    intro Z f z a b
    rw [map_mul]
    exact gs_mul f z ⊤ (by first | trivial | simp) _ _
  obtain ⟨e, he⟩ := exists_gen_of_local D.toPre.P.L hL (lineφO hϖ hv (D := D) m) (DegPre.lineε k)
  have hφw : (fun i => (ιS hϖ hv).left ≫ lineφO hϖ hv (D := D) m i) = DegPre.lineφ D.toPre F p.g.b := by
    funext i
    fin_cases i
    · show (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, hone] <;> rfl
    · show (ιS hϖ hv).left ≫ m.left = p.g.b.left
      rw [← Over.comp_left, hm] <;> rfl
  have hfw : FormEq (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)
      (fun i => (ιS hϖ hv).left ≫ lineφO hϖ hv (D := D) m i) (DegPre.lineε k) := by
    rw [hφw]
    intro U _ h
    rfl
  obtain ⟨cw, hcw0, hcw⟩ := ReciprocityTheory.ChartRestriction.G.DVR.TWM.exists_ratio hL w hw
    (LB.pullGen D.toPre.P.L _ _ e (ιS hϖ hv).left) (pullGen_isGen D.toPre.P.L _ _ e he _) hfw
  obtain ⟨qw, hqw⟩ := wt_coe_of_ne (v := v) hcw0
  obtain ⟨qζ, hqζ⟩ := wt_coe_of_ne (v := v) hζ
  refine ⟨qw + qζ - (Q p.y : ℚ) / k, ?_⟩
  intro s t s' hPhi hsm r
  have step : ∀ α : D.toPre.X, ∃ qα : ℚ, (k : ℚ) * qα = (bOf D.toPre Q p.y α : ℚ) ∧ ∀ R : ℚ,
      (VGe D F v k α (s.s α) R → VGe D F v k (α + p.y) (t.s (α + p.y)) (R + (qα + qw))) ∧
      (VGe D F v k (α + p.y) (t.s (α + p.y)) R → VGe D F v k α (s.s α) (R + -(qα + qw))) := by
    intro α
    obtain ⟨G₀, hG₀⟩ := exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv (D := D) m α) DegPre.gtε
    have hφα : (fun i => (ιS hϖ hv).left ≫ gtφO hϖ hv (D := D) m α i) = DegPre.gtφ D.toPre F p.g.b α := by
      funext i
      fin_cases i
      · show (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left = (cP D.toPre _ α * p.g.b).left
        rw [← Over.comp_left, hmul, comp_cP, hm] <;> rfl
      · show (ιS hϖ hv).left ≫ (cP D.toPre _ α).left = (cP D.toPre _ α).left
        rw [← Over.comp_left, comp_cP] <;> rfl
      · show (ιS hϖ hv).left ≫ m.left = p.g.b.left
        rw [← Over.comp_left, hm] <;> rfl
      · show (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left
        rw [← Over.comp_left, hone] <;> rfl
    have hfα : FormEq (DegPre.gtφ D.toPre F p.g.b α) DegPre.gtε
        (fun i => (ιS hϖ hv).left ≫ gtφO hϖ hv (D := D) m α i) DegPre.gtε := by
      rw [hφα]
      intro U _ h
      rfl
    obtain ⟨cα, hcα0, hcα⟩ := ReciprocityTheory.ChartRestriction.G.DVR.TWM.exists_ratio hL (p.g.s α) (p.g.isGen α)
      (LB.pullGen D.toPre.P.L _ _ G₀ (ιS hϖ hv).left) (pullGen_isGen D.toPre.P.L _ _ G₀ hG₀ _) hfα
    obtain ⟨qα, hvα, hkα⟩ := hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α G₀ hG₀ cα
      (fun Z r z J hJ => by rw [hcα Z r z J hJ, val_pull] <;> first | exact hJ | rfl)
    have hα : cP D.toPre (TO hϖ hv) (α + p.y) = cP D.toPre (TO hϖ hv) α * m ^ k := by
      rw [cPoint_add]
      congr 1
      apply liftO_unique (hϖ := hϖ) (hv := hv) (D := D)
      rw [comp_cP, cPoint_y, hpow, hm] <;> rfl
    obtain ⟨eO, heO, heOv⟩ := gen_uO (hϖ := hϖ) (hv := hv) (D := D) k α (α + p.y) m hα
      (LB.mulGen D.toPre.P.L _ _ _ _ G₀ e) (mulGen_isGen D.toPre.P.L _ _ _ _ G₀ e hG₀ he) (fun U _ h => prodF U h (cP D.toPre (TO hϖ hv) α * m).left (cP D.toPre (TO hϖ hv) α).left m.left
        (1 : TO hϖ hv ⟶ D.toPre.P.A).left k)
    obtain ⟨⟨u, hu, hcorr⟩, huv⟩ := gen_phi (D := D.toPre) hG p w hw α
    have hc0 : cα * cw ≠ 0 := mul_ne_zero hcα0 hcw0
    have hvc : v (cα * cw) = ((qα + qw : ℚ) : WithTop ℚ) := by
      rw [AddValuation.map_mul, hvα, hqw, WithTop.coe_add]
    have hcgen : ∀ ρ : DegPre.BF D.toPre F ⟶ DegPre.BF D.toPre F,
        ∀ (y : (DegPre.BF D.toPre F).left) (J), Good D.toPre.P.L y J →
        (val u ρ.left y J).val = gs ρ.left y ⊤ (gF D.toPre F (cα * cw)) *
          (val eO (ρ ≫ jO hϖ hv (D := D)).left y J).val := by
      intro ρ y J hJ
      have h1 := huv u hu hcorr _ ρ y J hJ
      have h2 := heOv _ (ρ ≫ jO hϖ hv (D := D)) y J hJ
      have hA : (ρ ≫ jO hϖ hv (D := D)) ≫ fst _ _ ≫ m = ρ ≫ fst _ _ ≫ p.g.b := by
        rw [Category.assoc, reassoc_of% hjf, hm]
      have hB : (ρ ≫ jO hϖ hv (D := D)) ≫ snd _ _ = ρ ≫ DegPre.prB D.toPre F := by
        rw [Category.assoc, hjs]
      have hC : ((ρ ≫ jO hϖ hv (D := D)) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (ιS hϖ hv).left := by
        first
          | rw [Category.assoc, hjf, ← Category.assoc, Over.comp_left]
          | simp only [Category.assoc, hjf, Over.comp_left]
      rw [hA, hB, hC] at h2
      rw [h1, h2, hgsF, val_mul, val_mul]
      simp only [uVal, Units.val_mul, Over.comp_left]
      rw [hcα _ _ _ _ hJ, hcw _ _ _ _ hJ, val_pull, val_pull, hgsm]
      all_goals first | exact hJ | ring
    refine ⟨qα, hkα, fun R => ⟨fun hs0 => ?_, fun ht0 => ?_⟩⟩
    · have hfst : (DegPre.trPt D.toPre F p.g.b).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left =
          (fst (TF (R := V) F) D.toPre.P.A).left := by
        rw [← Over.comp_left, tr_fst]
      have hh : (DegPre.trPt D.toPre F p.g.b).left ≫ (jO hϖ hv (D := D)).left =
          (jO hϖ hv (D := D)).left ≫ (trO hϖ hv m).left := by
        rw [← Over.comp_left, ← Over.comp_left, jO_trO (hϖ := hϖ) (hv := hv) (D := D) p.g.b m hm]
      exact vge_moveO (hϖ := hϖ) (hv := hv) hTW hk (s := s.s α) (s' := t.s (α + p.y))
        (h := (DegPre.trPt D.toPre F p.g.b).left) hfst (H := (trO hϖ hv m).left) hh u (hPhi α u hu hcorr)
        eO heO (fun U _ h => fwdF U h (fun i => ((trO hϖ hv m).left ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫
          D.toPre.famφB α i) (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB (α + p.y) i)
          (DegPre.famε k))
        (cα * cw) (by
          intro y J hJ
          have := hcgen (𝟙 _) y J hJ
          rw [Category.id_comp] at this
          simpa only [Over.id_left] using this)
        (le_of_eq hvc.symm) hs0
    · have hm' : ιS hϖ hv ≫ m⁻¹ = p.g.b⁻¹ := by rw [hinv, hm]
      have hbb : (DegPre.trPt D.toPre F p.g.b⁻¹).left ≫ (DegPre.trPt D.toPre F p.g.b).left = 𝟙 _ := by
        rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.H1.trPt_mul, _root_.inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.H1.trPt_one,
          Over.id_left]
      have hmm : ∀ {W : Scheme.{0}} (g : (TO hϖ hv ⊗ D.toPre.P.A).left ⟶ W),
          (trO hϖ hv (D := D) m⁻¹).left ≫ (trO hϖ hv m).left ≫ g = g := by
        intro W g
        rw [← Category.assoc, ← Over.comp_left, trO_mul, _root_.inv_mul_cancel, trO_one, Over.id_left,
          Category.id_comp]
      have hfst' : (DegPre.trPt D.toPre F p.g.b⁻¹).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left =
          (fst (TF (R := V) F) D.toPre.P.A).left := by
        rw [← Over.comp_left, tr_fst]
      have hh' : (DegPre.trPt D.toPre F p.g.b⁻¹).left ≫ (jO hϖ hv (D := D)).left =
          (jO hϖ hv (D := D)).left ≫ (trO hϖ hv m⁻¹).left := by
        rw [← Over.comp_left, ← Over.comp_left, jO_trO (hϖ := hϖ) (hv := hv) (D := D) p.g.b⁻¹ m⁻¹ hm']
      have hu'v : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
          val (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.trPt D.toPre F p.g.b⁻¹).left))
            (𝟙 _) y J = (val u (DegPre.trPt D.toPre F p.g.b⁻¹).left y J)⁻¹ := by
        intro y J hJ
        rw [val_inv, val_pull, Category.id_comp]
        all_goals first | exact hJ | rfl
      have hrel' : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
          (DegPre.famφ D.toPre F (α + p.y)) (DegPre.famε k) (t.s (α + p.y))
          (DegPre.trPt D.toPre F p.g.b⁻¹).left _ _
          (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.trPt D.toPre F p.g.b⁻¹).left)) := by
        apply (secRel_iff hL ..).2
        intro y J hJ
        have h1 := (secRel_iff hL ..).1 (hPhi α u hu hcorr) _ (DegPre.trPt D.toPre F p.g.b⁻¹).left y J hJ
        rw [hbb] at h1
        rw [Category.id_comp, hu'v y J hJ, h1, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      exact vge_moveO (hϖ := hϖ) (hv := hv) hTW hk (s := t.s (α + p.y)) (s' := s.s α)
        (h := (DegPre.trPt D.toPre F p.g.b⁻¹).left) hfst' (H := (trO hϖ hv m⁻¹).left) hh'
        _ hrel' (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eO (trO hϖ hv m⁻¹).left))
        (invGen_isGen D.toPre.P.L _ _ _ (pullGen_isGen D.toPre.P.L _ _ eO heO _)) (fun U _ h => backF U h
          (fun i => ((trO hϖ hv m⁻¹).left ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫ D.toPre.famφB (α + p.y) i)
          (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) _ (DegPre.famε k) _
          (fun i => (Category.assoc _ _ _).symm)
          (fun i => by simp only [Sum.elim_inr, Over.comp_left]; rw [Category.assoc, hmm])
          (fun i => rfl) (fun i => neg_neg _))
        (cα * cw)⁻¹ (by
          intro y J hJ
          have hX := hcgen (DegPre.trPt D.toPre F p.g.b⁻¹) y J hJ
          have hgg : gs (DegPre.trPt D.toPre F p.g.b⁻¹).left y ⊤ (gF D.toPre F (cα * cw)) *
              gs (𝟙 _) y ⊤ (gF D.toPre F (cα * cw)⁻¹) =
                gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 1) := by
            rw [hgsF, hgsF, hfst', Category.id_comp, ← hgsm, mul_inv_cancel₀ hc0]
          have he1 : gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 1) *
              gs (DegPre.trPt D.toPre F p.g.b⁻¹).left y ⊤ (gF D.toPre F (cα * cw)) =
                gs (DegPre.trPt D.toPre F p.g.b⁻¹).left y ⊤ (gF D.toPre F (cα * cw)) := by
            rw [hgsF, hfst', ← hgsm, _root_.one_mul]
          rw [hu'v y J hJ, val_inv, val_pull, ← hh', ← Over.comp_left]
          all_goals first | exact hJ | exact alg _ _ _ _ _ hX hgg he1)
        (le_of_eq (v_inv_coe (v := v) hc0 hvc).symm) ht0
  constructor
  · intro hN χ
    obtain ⟨α, rfl⟩ : ∃ α, χ = α + p.y := ⟨χ - p.y, (sub_add_cancel χ p.y).symm⟩
    obtain ⟨qα, hkα, hmove⟩ := step α
    have h1 := (hmove _).1 (hN α)
    have h2 := VGe.smul h1 (le_of_eq hqζ.symm) (fun j => hsm (α + p.y) j)
    refine VGe.mono h2 (le_of_eq ?_)
    have hq : qα = ((Q (α + p.y) : ℚ) - Q p.y - Q α) / k := by
      rw [eq_div_iff hk0, _root_.mul_comm, hkα]
      simp only [bOf, add_comm p.y α]
      push_cast
      ring
    rw [hq]
    ring
  · intro hN α
    obtain ⟨qα, hkα, hmove⟩ := step α
    have h0 := hN (α + p.y)
    have h1 := VGe.smul (s' := t.s (α + p.y)) h0 (le_of_eq (v_inv_coe (v := v) hζ hqζ).symm) (fun j => by
      rw [hsm (α + p.y) j, ← _root_.mul_assoc, ← constBF_mul, inv_mul_cancel₀ hζ, constBF_eq]
      first
        | simp only [resTop, map_one, _root_.one_mul]
        | simp [resTop])
    have h2 := (hmove _).2 h1
    refine VGe.mono h2 (le_of_eq ?_)
    have hq : qα = ((Q (α + p.y) : ℚ) - Q p.y - Q α) / k := by
      rw [eq_div_iff hk0, _root_.mul_comm, hkα]
      simp only [bOf, add_comm p.y α]
      push_cast
      ring
    rw [hq]
    ring

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
