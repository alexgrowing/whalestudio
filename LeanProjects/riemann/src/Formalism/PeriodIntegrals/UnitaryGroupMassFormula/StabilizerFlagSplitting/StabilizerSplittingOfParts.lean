import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.MulVecColOfMul

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

theorem stabilizer_splitting_of_parts (hFS : FixSub) (hSF : SubFlag) (hUN : UnipN) (hNP : NPerp) : C1ii := by
  intro k r z z' γ hs hp
  have hz : inWb k r z := hs.2.1.1
  have hz' : inWb k r z' := hs.2.2.1
  have hγ : γ ∈ B.GV k r := hp.1
  have hγu : IsUnit γ.det := GV_unit k r hγ
  have hγ1 : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hγu
  have hγ2 : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hγu
  have hG : IsUnit ((Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ).det := gram_unit k r z z' γ hs hp
  have hPY : Pm k r z z' γ * Ym k r z z' γ = Ym k r z z' γ := Proj.prj_Y _ _ hG
  have hPP : Pm k r z z' γ * Pm k r z z' γ = Pm k r z z' γ := Proj.prj_sq _ _ hG
  have hHh : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r
  have hPH : (Pm k r z z' γ)ᴴ * Hpk k r = Hpk k r * Pm k r z z' γ := Proj.prj_star _ _ hHh
  have hLQ : ((Ym k r z z' γ)ᴴ * Hpk k r) * (1 - Pm k r z z' γ) = 0 := Proj.L_one_sub _ _ hG
  set Y := Ym k r z z' γ with hY
  set P := Pm k r z z' γ with hP

  have UW1 : ∀ w, (1 : B.Mat k r) ∈ UWset k r w := fun w => ⟨GV_one k r, fun a => by simp, by simp⟩
  have NS : ∀ w, ∀ g ∈ Nset k r, g ∈ Sset k r w := fun w g hg => ⟨1, UW1 w, g, hg, by simp⟩
  have Hmul : ∀ g ∈ Hst k r z z' γ, ∀ h ∈ Hst k r z z' γ, g * h ∈ Hst k r z z' γ := by
    rintro g ⟨hgS, s, hs1, rfl⟩ h ⟨hhS, t, ht1, rfl⟩
    refine ⟨(sGroup k r z hz).2.1 _ hgS _ hhS, s * t, (sGroup k r z' hz').2.1 _ hs1 _ ht1, ?_⟩
    calc γ * s * γ⁻¹ * (γ * t * γ⁻¹) = γ * s * (γ⁻¹ * γ) * t * γ⁻¹ := by noncomm_ring
      _ = γ * (s * t) * γ⁻¹ := by rw [hγ1]; noncomm_ring
  have Hinv : ∀ g ∈ Hst k r z z' γ, g⁻¹ ∈ Hst k r z z' γ := by
    rintro g ⟨hgS, s, hs1, rfl⟩
    refine ⟨(sGroup k r z hz).2.2 _ hgS, s⁻¹, (sGroup k r z' hz').2.2 _ hs1, ?_⟩
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv γ hγu, Matrix.mul_assoc]
  have H_GV : ∀ g ∈ Hst k r z z' γ, g ∈ B.GV k r := fun g hg => (hSF k r z hz hg.1).1

  have spanF : ∀ a, flagSpan k r z a ≤ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := by
    intro a; rw [flagSpan, Submodule.span_le]; rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl b.1, rfl⟩
  have spanF' : ∀ b, flagSpan k r z' b ≤
      (Submodule.span ℂ (Set.range (gramVec k r z z' γ))).comap (Matrix.mulVecLin γ) := by
    intro b; rw [flagSpan, Submodule.span_le]; rintro _ ⟨c, rfl⟩
    exact Submodule.mem_comap.2 (Submodule.subset_span ⟨Sum.inr c.1, rfl⟩)
  have Hcol : ∀ g ∈ Hst k r z z' γ, ∀ j,
      g *ᵥ gramVec k r z z' γ j ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := by
    rintro g ⟨hgS, s, hs1, hgs⟩ j
    have hF := hSF k r z hz hgS
    have hF' := hSF k r z' hz' hs1
    rcases j with a | b
    · have h1 := spanF a (hF.2 a)
      have h2 : fvec k r z a ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have e : g *ᵥ gramVec k r z z' γ (Sum.inl a) = (g *ᵥ fvec k r z a - fvec k r z a) + fvec k r z a := by
        rw [sub_add_cancel]; rfl
      rw [e]; exact Submodule.add_mem _ h1 h2
    · have h1 : Matrix.mulVecLin γ (s *ᵥ fvec k r z' b - fvec k r z' b) ∈
          Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := spanF' b (hF'.2 b)
      have h2 : γ *ᵥ fvec k r z' b ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) :=
        Submodule.subset_span ⟨Sum.inr b, rfl⟩
      rw [Matrix.mulVecLin_apply] at h1
      have e : g *ᵥ gramVec k r z z' γ (Sum.inr b) =
          γ *ᵥ (s *ᵥ fvec k r z' b - fvec k r z' b) + γ *ᵥ fvec k r z' b := by
        rw [← mulVec_add, sub_add_cancel, hgs]
        show (γ * s * γ⁻¹) *ᵥ (γ *ᵥ fvec k r z' b) = γ *ᵥ (s *ᵥ fvec k r z' b)
        rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hγ1, Matrix.mul_one]
      rw [e]; exact Submodule.add_mem _ h1 h2
  have HC : ∀ g ∈ Hst k r z z' γ, ∃ C, g * Y = Y * C := by
    intro g hg
    refine Proj.exists_C Y (g * Y) (fun j => ?_)
    have e : (fun i => (g * Y) i j) = g *ᵥ gramVec k r z z' γ j := by
      ext i; simp [hY, Ym, mul_apply, mulVec, dotProduct]
    rw [e]; exact Hcol g hg j
  have HM : ∀ g ∈ Hst k r z z' γ, (1 - P) * g * P = 0 := fun g hg => by
    obtain ⟨C, hC⟩ := HC g hg; exact Proj.presM _ Y hG g C hC
  have HU : ∀ g ∈ Hst k r z z' γ, P * g * (1 - P) = 0 := fun g hg => by
    obtain ⟨C, hC⟩ := HC g⁻¹ (Hinv g hg)
    exact Proj.presU _ Y hG g (H_GV g hg) (GV_unit k r (H_GV g hg)) C hC

  have U_P : ∀ v ∈ Uperp k r z z' γ, P *ᵥ v = 0 := fun v hv =>
    Proj.prj_mulVec_of_L _ Y ((mem_U_iff k r z z' γ v).1 hv)
  have Q_U : ∀ j, (fun i => (1 - P) i j) ∈ Uperp k r z z' γ := by
    intro j; rw [mem_U_iff]; ext l
    have := congrFun (congrFun hLQ l) j
    simpa [mulVec, dotProduct, mul_apply] using this
  have fixU : ∀ g : B.Mat k r, (∀ v ∈ Uperp k r z z' γ, g *ᵥ v = v) → g * (1 - P) = 1 - P :=
    fun g hg => mul_eq_of_cols k r g (1 - P) (fun j => hg _ (Q_U j))
  have fixM : ∀ g : B.Mat k r, g * Y = Y → g * P = P := by
    intro g hg
    simp only [hP, Pm, Proj.prj, ← Matrix.mul_assoc]
    rw [hg]

  have hKH : KU k r z z' γ ⊆ Hst k r z z' γ := by
    rintro κ ⟨hκG, hκf⟩
    refine ⟨hFS k r z hz ⟨hκG, fun a => hκf (Sum.inl a)⟩, γ⁻¹ * κ * γ,
      hFS k r z' hz' ⟨GV_mul k r (GV_mul k r (GV_inv k r hγ) hκG) hγ, fun b => ?_⟩, ?_⟩
    · have h1 : κ *ᵥ (γ *ᵥ fvec k r z' b) = γ *ᵥ fvec k r z' b := hκf (Sum.inr b)
      rw [← mulVec_mulVec, ← mulVec_mulVec, h1, mulVec_mulVec, hγ1, one_mulVec]
    · calc κ = (γ * γ⁻¹) * κ * (γ * γ⁻¹) := by rw [hγ2]; simp
        _ = γ * (γ⁻¹ * κ * γ) * γ⁻¹ := by noncomm_ring

  have Rnil : ∀ g ∈ Rst k r z z' γ, (g - 1) ^ (r + 2) = 0 := by
    rintro g ⟨hgH, hgU⟩
    obtain ⟨hgS, s, hs1, hgs⟩ := hgH
    have hF := hSF k r z hz hgS
    have hF' := hSF k r z' hz' hs1
    have n1 : ∀ a, ((g - 1) ^ (r + 1)) *ᵥ fvec k r z a = 0 := flag_nilp_all g (fvec k r z) hF.2
    have n2 : ∀ b, ((g - 1) ^ (r + 1)) *ᵥ (γ *ᵥ fvec k r z' b) = 0 := by
      refine flag_nilp_all g (fun b => γ *ᵥ fvec k r z' b) (fun b => ?_)
      have e : g *ᵥ (γ *ᵥ fvec k r z' b) - γ *ᵥ fvec k r z' b =
          Matrix.mulVecLin γ (s *ᵥ fvec k r z' b - fvec k r z' b) := by
        rw [Matrix.mulVecLin_apply, mulVec_sub, hgs, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
          hγ1, Matrix.mul_one]
      rw [e]
      have hle : flagSpan k r z' b ≤ (Submodule.span ℂ (Set.range fun c : {c : Fin (r + 1) // c < b} =>
          γ *ᵥ fvec k r z' c.1)).comap (Matrix.mulVecLin γ) := by
        rw [flagSpan, Submodule.span_le]; rintro _ ⟨c, rfl⟩
        exact Submodule.mem_comap.2 (Submodule.subset_span ⟨c, rfl⟩)
      exact hle (hF'.2 b)
    have hY0 : (g - 1) ^ (r + 1) * Y = 0 := by
      ext i j
      rcases j with a | b
      · have := congrFun (n1 a) i
        simpa [hY, Ym, mul_apply, mulVec, dotProduct, gramVec] using this
      · have := congrFun (n2 b) i
        simpa [hY, Ym, mul_apply, mulVec, dotProduct, gramVec] using this
    have hP0 : (g - 1) ^ (r + 1) * P = 0 := by
      simp only [hP, Pm, Proj.prj, ← Matrix.mul_assoc]
      rw [← hY, hY0]; simp
    have hQ : (g - 1) * (1 - P) = 0 := by
      rw [Matrix.sub_mul, fixU g hgU, Matrix.one_mul, sub_self]
    exact Alg.nilp P g (r + 1) hPP hQ (HM g ⟨hgS, s, hs1, hgs⟩) hP0

  have hli : LinearIndependent ℂ (gramVec k r z z' γ) := by
    rw [Fintype.linearIndependent_iff]; intro c hc
    have h0 : c = 0 := Proj.Y_inj _ Y hG c (by rw [hY, Ym_mulVec]; exact hc)
    intro i; rw [h0]; rfl
  have hdis := hli.disjoint_span_image Set.isCompl_range_inl_range_inr.disjoint
  have hXl : Xsp k r ≤ Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inl) := by
    rw [Xsp, Submodule.span_le]; rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl ⟨a.val, by omega⟩, ⟨_, rfl⟩, fvec_lt k r z a⟩
  have hXr : Xsp k r ≤ (Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inr)).comap
      (Matrix.mulVecLin γ) := by
    rw [Xsp, Submodule.span_le]; rintro _ ⟨a, rfl⟩
    refine Submodule.mem_comap.2 (Submodule.subset_span ⟨Sum.inr ⟨a.val, by omega⟩, ⟨_, rfl⟩, ?_⟩)
    show γ *ᵥ fvec k r z' ⟨a.val, _⟩ = _
    rw [fvec_lt k r z' a]; rfl
  have hR : Rst k r z z' γ = {g | g ∈ Nset k r ∧ ∃ n ∈ Nset k r, g = γ * n * γ⁻¹} := by
    ext g; constructor
    · intro hg
      have hn := Rnil g hg
      obtain ⟨⟨hgS, s, hs1, hgs⟩, -⟩ := hg
      refine ⟨hUN k r z hs.2.1 g hgS (r + 2) hn, s, hUN k r z' hs.2.2 s hs1 (r + 2) ?_, hgs⟩
      have hsg : s = γ⁻¹ * g * γ := by
        rw [hgs]
        calc s = (γ⁻¹ * γ) * s * (γ⁻¹ * γ) := by rw [hγ1]; simp
          _ = γ⁻¹ * (γ * s * γ⁻¹) * γ := by noncomm_ring
      have e : s - 1 = γ⁻¹ * (g - 1) * γ := by
        calc s - 1 = γ⁻¹ * g * γ - γ⁻¹ * γ := by rw [hγ1, ← hsg]
          _ = γ⁻¹ * (g - 1) * γ := by noncomm_ring
      rw [e, conj_pow (g - 1) γ γ⁻¹ hγ1 hγ2, hn]; simp
    · rintro ⟨hgN, n, hnN, hgn⟩
      refine ⟨⟨NS z g hgN, n, NS z' n hnN, hgn⟩, fun v hv => ?_⟩
      have hL : ∀ j, herm (Hpk k r) v (gramVec k r z z' γ j) = 0 := fun j => by
        rw [← L_mulVec, (mem_U_iff k r z z' γ v).1 hv]; rfl
      have h1 : (g - 1) *ᵥ v ∈ Xsp k r := hNP k r g hgN v (fun a => by
        have := hL (Sum.inl ⟨a.val, by omega⟩)
        rw [← fvec_lt k r z a]; exact this)
      have h2 : (n - 1) *ᵥ (γ⁻¹ *ᵥ v) ∈ Xsp k r := hNP k r n hnN _ (fun a => by
        have := hL (Sum.inr ⟨a.val, by omega⟩)
        rw [← herm_unit k r hγ, mulVec_mulVec, hγ2, one_mulVec, ← fvec_lt k r z' a]
        exact this)
      have e : (g - 1) *ᵥ v = Matrix.mulVecLin γ ((n - 1) *ᵥ (γ⁻¹ *ᵥ v)) := by
        rw [Matrix.mulVecLin_apply, mulVec_mulVec, mulVec_mulVec, hgn]
        congr 1
        calc γ * n * γ⁻¹ - 1 = γ * n * γ⁻¹ - γ * γ⁻¹ := by rw [hγ2]
          _ = γ * (n - 1) * γ⁻¹ := by noncomm_ring
      have m1 := hXl h1
      have m2 : (g - 1) *ᵥ v ∈ Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inr) := by
        rw [e]; exact hXr h2
      have h0 := Submodule.disjoint_def.1 hdis _ m1 m2
      have : g *ᵥ v - v = 0 := by rw [← h0, sub_mulVec, one_mulVec]
      exact sub_eq_zero.1 this

  have hc : ∀ h ∈ Hst k r z z' γ, ∃! p : B.Mat k r × B.Mat k r,
      p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ KU k r z z' γ ∧ h = p.1 * p.2 := by
    intro h hh
    have hhG := H_GV h hh
    have hU := HU h hh
    have hκG : h * (1 - P) + P ∈ B.GV k r := Alg.unitK (Hpk k r) P h hHh hPH hPP hhG hU
    have hκY : (h * (1 - P) + P) * Y = Y := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPY, sub_self,
        Matrix.mul_zero, zero_add]
    have hκK : h * (1 - P) + P ∈ KU k r z z' γ := ⟨hκG, fun i => mulVec_col_of_mul k r _ Y hκY i⟩
    have hdec : (h * P + (1 - P)) * (h * (1 - P) + P) = h := Alg.decomp h P hPP hU
    have hκu : IsUnit (h * (1 - P) + P).det := GV_unit k r hκG
    have hρeq : h * P + (1 - P) = h * (h * (1 - P) + P)⁻¹ := by
      calc h * P + (1 - P) = (h * P + (1 - P)) * ((h * (1 - P) + P) * (h * (1 - P) + P)⁻¹) := by
            rw [mul_nonsing_inv _ hκu, Matrix.mul_one]
        _ = h * (h * (1 - P) + P)⁻¹ := by rw [← Matrix.mul_assoc, hdec]
    have hρH : h * P + (1 - P) ∈ Hst k r z z' γ := by
      rw [hρeq]; exact Hmul h hh _ (Hinv _ (hKH hκK))
    have hρR : h * P + (1 - P) ∈ Rst k r z z' γ := ⟨hρH, fun v hv => by
      rw [add_mulVec, ← mulVec_mulVec, U_P v hv, mulVec_zero, zero_add, sub_mulVec, one_mulVec,
        U_P v hv, sub_zero]⟩
    refine ⟨(h * P + (1 - P), h * (1 - P) + P), ⟨hρR, hκK, hdec.symm⟩, ?_⟩
    rintro ⟨ρ₁, κ₁⟩ ⟨hρ₁, hκ₁, h₁⟩
    have u := Alg.uniq h P ρ₁ κ₁ h₁.symm (fixU ρ₁ hρ₁.2)
      (fixM κ₁ (mul_eq_of_cols k r κ₁ Y hκ₁.2)) (HU κ₁ (hKH hκ₁))
    exact Prod.ext u.1 u.2

  have hd : ∀ ρ ∈ Rst k r z z' γ, ∀ κ ∈ KU k r z z' γ, ρ * κ = κ * ρ := fun ρ hρ κ hκ =>
    Alg.comm P ρ κ (fixU ρ hρ.2) (fixM κ (mul_eq_of_cols k r κ Y hκ.2)) (HM ρ hρ.1) (HU κ (hKH hκ))

  have he : ∀ ρ ∈ Rst k r z z' γ, (ρ - 1) ^ (2 * r + k + 1) = 0 := fun ρ hρ => by
    have e : r + 2 ≤ 2 * r + k + 1 := by have := hs.1; omega
    exact pow_eq_zero_of_le e (Rnil ρ hρ)
  exact ⟨hKH, hR, hc, hd, he⟩

end PI.StabSplit
