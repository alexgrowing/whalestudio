import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActInt
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActAlg
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DblCoordUnique
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrderStatement

noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory PositivityTheory.ThKH.Evl

namespace PositivityTheory.ThK

namespace LinAct

variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {K : Type} [CommRing K] [Nontrivial K] [Algebra k K] {c : K →ₐ[k] K} {ψ : AddChar k ℂ} {ξ₀ ξ : K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  {JA : Matrix α α K} {JB : Matrix β β K} {Cy : Matrix β ν K}

theorem dbl_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (dd : Darboux (symp (R := k) c ξ JB (dbl JA)) κ) (om : UG c (dbl JA) →* Module.End ℂ ((κ → k) → ℂ))
    (hs : IsSplitting (sbClass k) ψ dd (actB c) om) (hr : SiegelRule c (sbClass k) ψ ξ JB (dbl JA) dd 1 (diagCols α) om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY dd Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  have hiso := lagY_iso dd hL.1
  have hdim := lagY_dim hq dd hL
  have hcard := card_lagr hL
  have hn := norm_char hc
  have key : ∀ g, ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l (om g φ) = a * l φ := fun g =>
    line hc hn h1 _ hiso hdim l (l ∘ₗ om g) hl (by
      rintro _ ⟨z, rfl⟩ φ hφ
      refine (congrArg l (hs.impl g (Cy * z) φ hφ)).trans (hl _ ?_ _ (hs.pres g φ hφ))
      exact mem_lagY.2 ⟨_, by rw [actB, Matrix.mul_assoc]⟩) hne
  choose a ha using key
  obtain ⟨φ₀, hφ₀, hl₀⟩ := hne
  let A : UG c (dbl JA) →* ℂ :=
    { toFun := a
      map_one' := by
        have := ha 1 φ₀ hφ₀
        rw [map_one, Module.End.one_apply] at this
        exact (mul_eq_right₀ hl₀).1 this.symm
      map_mul' := fun g h => by
        have := ha (g * h) φ₀ hφ₀
        rw [map_mul, Module.End.mul_apply, ha g _ (hs.pres h _ hφ₀), ha h _ hφ₀, ← mul_assoc] at this
        exact (mul_right_cancel₀ hl₀ this).symm }
  obtain ⟨-, Cx, M, -, hM1, hM2⟩ := id hL
  obtain ⟨r, e, he⟩ := exists_coord hq ν α
  have hD := isLagr_diagCols (R := k) c JA
  have hisoD : ∀ z z' : Matrix β α K, (dd.e (z * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z' * (diagCols (E := K) α)ᵀ)).2 =
      (dd.e (z' * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z * (diagCols (E := K) α)ᵀ)).2 := fun z z' => by
    have h := dd.form (z * (diagCols (E := K) α)ᵀ) (z' * (diagCols (E := K) α)ᵀ)
    rw [symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JB hD.1, mul_zero, map_zero] at h
    exact sub_eq_zero.mp h.symm
  let X₀ : Matrix ν α K →ₗ[k] Matrix β (α ⊕ α) K :=
    { toFun := fun z => Cx * z * (diagCols (E := K) α)ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun t z => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let X : (Fin r → k) →ₗ[k] (κ → k) × (κ → k) := dd.e.toLinearMap ∘ₗ X₀ ∘ₗ e.toLinearMap
  have hX : ∀ x, X x = dd.e (Cx * e x * (diagCols (E := K) α)ᵀ) := fun _ => rfl
  obtain ⟨L, ⟨φ₁, hφ₁, hL₁⟩, hLX, hLY, hLT⟩ := exists_avg hc h1 _ hiso hdim l hl ⟨φ₀, hφ₀, hl₀⟩ X
    (fun x x' => hisoD _ _) (fun x hx => by
      obtain ⟨z, hz⟩ := mem_lagY.1 hx
      have h2 := dd.e.injective (hz.trans (hX x))
      have h3 := (indep hM2 (z := -z) (z' := e x * (diagCols (E := K) α)ᵀ) (by
        rw [Matrix.mul_neg, h2, Matrix.mul_assoc, neg_add_cancel])).2
      rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, ← fromCols_zero] at h3
      exact e.map_eq_zero_iff.1 (fromCols_ext_iff .. |>.1 h3).1)
  have hinv : ∀ z : Matrix β α K, ∀ φ ∈ SB (κ → k), L (dd.rho ψ (z * (diagCols (E := K) α)ᵀ) φ) = L φ := fun z φ hφ => by
    obtain ⟨x, hx⟩ := e.surjective (M * z).toRows₂
    have hz : z = Cy * (M * z).toRows₁ + Cx * e x := by
      rw [hx, ← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hM1, Matrix.one_mul]
    rw [Darboux.rho, hz, Matrix.add_mul, map_add, ← schr_add (hisoD _ _), hLY _ (mem_lagY.2 ⟨_, by rw [Matrix.mul_assoc]⟩)
      (fun x => hisoD _ _) _ (schr_mem hc _ hφ), ← hX, hLX _ _ hφ]
  have hA1 := GlobalTheory.T.lagrangian_stabilizer_character_trivial k K c ξ₀ _ _ _ _ hq (GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl hA) hD A.toHomUnits fun p t hp => by
    obtain ⟨g, hg, hdet⟩ := he t
    have e1 := hr L trivial hinv p t hp φ₁ hφ₁
    have e2 := hLT (om p) g (a p) (hs.pres p) (fun x φ hφ => by
      refine (hs.impl p (Cx * e x * (diagCols (E := K) α)ᵀ) φ hφ).trans ?_
      rw [hX, hg, actB, Darboux.rho, Matrix.mul_assoc _ (diagCols (E := K) α)ᵀ, ← transpose_mul, hp, transpose_mul]
      simp only [Matrix.mul_assoc]) (ha p) φ₁ hφ₁
    have e3 := mul_right_cancel₀ hL₁ (e1.symm.trans e2)
    have e4 : (Fintype.card β : ℝ) / 2 = (Fintype.card ν : ℕ) := by rw [hcard]; push_cast; ring
    rw [hdet, map_pow, e4, Real.rpow_natCast, MonoidHom.one_apply, Circle.coe_one, one_mul, NNReal.coe_pow] at e3
    refine Units.ext ((mul_eq_left₀ ?_).1 e3.symm)
    exact_mod_cast pow_ne_zero _ distribHaarChar_pos.ne'
  intro g φ hφ
  have : a g = 1 := congrArg Units.val (DFunLike.congr_fun hA1 g)
  rw [ha g φ hφ, this, one_mul]

theorem weilB_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (d : Darboux (symp (R := k) c ξ JB JA) κ) (om : UG c JA →* Module.End ℂ ((κ → k) → ℂ))
    (hW : IsWeilB c (sbClass k) ψ ξ JB JA d 1 om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY d Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  obtain ⟨hs₀, dd, omd, hdd, hs, hr, hb⟩ := hW
  have hn := norm_char hc
  obtain ⟨l₂, hne₂, hl₂⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form k _ ψ hc h1 _ (lagY_iso dd hL.1)
  have hfix := dbl_fix hc h1 hq hA hL dd omd hs hr l₂ hl₂ hne₂
  obtain ⟨φ₁, h₁, φ₂, h₂, h₁₂⟩ : ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), l₂ (boxFun φ₁ φ₂) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ₀, h₀, hl₀⟩ := hne
    obtain ⟨φ, hφ, hφ0⟩ := hne₂
    obtain ⟨y, hy⟩ := Function.ne_iff.mp fun h : φ₀ = 0 => hl₀ (by rw [h, map_zero])
    refine hφ0 (cyc hc hn h1 (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem h₀ h₀) (fun h => ?_) l₂ (fun w => ?_) φ hφ)
    · exact mul_ne_zero hy hy (congrFun h (Sum.elim y y))
    · rw [schr_box]
      exact hcon _ (schr_mem hc _ h₀) _ (schr_mem hc _ h₀)
  let Bx : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    { toFun := fun φ => boxFun φ φ₂
      map_add' := fun a b => funext fun x => add_mul _ _ _
      map_smul' := fun t a => funext fun x => mul_assoc _ _ _ }
  obtain ⟨a, ha⟩ := line hc hn h1 _ (lagY_iso d hL.1) (lagY_dim hq d hL) l (l₂ ∘ₗ Bx) hl (by
    rintro _ ⟨z, rfl⟩ φ hφ
    have e := hl₂ _ (mem_lagY.2 ⟨fromCols z 0, rfl⟩) _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
    have e0 : schr ψ (0, 0) φ₂ = φ₂ := by funext x; simp [schr]
    rw [mul_fromCols, hdd, Matrix.mul_zero, map_zero, schr_box] at e
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.fst_zero, Prod.snd_zero, neg_zero, e0] at e
    exact e) hne
  have ha0 : a ≠ 0 := fun h => h₁₂ ((ha φ₁ h₁).trans (by rw [h, zero_mul]))
  intro g φ hφ
  obtain ⟨gd, hgd⟩ := GlobalTheory.CompanionTheory.WeilOneMember.exists_embed g
  have e := hfix gd _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
  rw [hb g gd hgd φ hφ φ₂ h₂] at e
  exact mul_left_cancel₀ ha0 ((ha _ (hs₀.pres g φ hφ)).symm.trans (e.trans (ha φ hφ)))

end LinAct

theorem split_character_fixes_evaluation : LinearAct := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ hK ⟨ξ₀, hq⟩ hc h1 m n N κ _ JA JB d χ Cy om l hA _ hL ⟨_, d', hd', hW⟩ hev g φ hφ
  have := hK.nontrivial
  refine LinAct.weilB_fix hc h1 hq hA hL d' _ hW l ?_ hev.1 g φ hφ
  rintro _ ⟨z, rfl⟩ φ hφ
  have e := hev.2 zᵀ φ hφ
  rw [Darboux.rho, ← hd', transpose_mul, transpose_transpose, transpose_transpose] at e
  exact e

end PositivityTheory.ThK
