import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.HtLawCongr

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Joint

theorem admissibleHeckeAlgebra_of_generated (h : AdmTop2) : AdmTop := by
  intro Ω _ _ _ ε X A N l _ e S W ψ ι gN j a1 a2 a3 a4 a5 a6 a7 a8 ev ρ F b1 b2 b3 b4 b5 χ b6 m π σ P c1 c2 c3 c4 c5 c6 c7 c8 c9 c lam d1 d2 d3
  obtain ⟨pr, a, cf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    h ε X A N l e S W ψ ι gN j a1 a2 a3 a4 a5 a6 a7 a8 ev ρ F b1 b2 b3 b4 b5 χ b6 m π σ P c1 c2 c3 c4 c5 c6 c7 c8 c9 c lam d1 d2 d3
  exact ⟨pr, a, cf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.2⟩

theorem glue2 : Glue2 := by
  classical
  intro hK4 hK5 hAdm hTow hCh hMeas hJ hCoef hMono hPsi hFrob hDet hHat hPin hSmNz hGm hES hAvgEq hAvgMF hRhs hSm hChi
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc
  obtain ⟨hgM, hgl, χg, hkill, hatt, hine⟩ := hSrc
  obtain ⟨ψ, hψ⟩ := hPsi l Ω ι χg hkill
  obtain ⟨hlA, j, hj⟩ := hJ l Ω A hNf.atL
  have hl2 : l ≠ 2 := hNf.l_odd
  have he : 1 ≤ e := hNf.e_pos
  obtain ⟨N, χ, θ, α, v, B, cc, c₁, d₁, hN5, hgN, -, hlN, hχg, hα, hαq, hEig, hχm1, hθm1, hMeasMu, hv, hc1, hd1, hc1cop, hd1cop, hc1e, hd1e⟩ :=
    hCh l hl2 ι e he g hgM hgl ψ 1 one_pos (by simpa using (Fact.out : Nat.Prime l).one_lt.ne')
  haveI : NeZero N := ⟨by omega⟩
  let ε : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := ℂ)).toRingHom
  obtain ⟨X⟩ := hTow Ω ε
  let ψ₀ : ZMod l → Qbar l := fun x => ι.symm (ψ x)
  let cw : ZMod N → Qbar l := fun x => ι.symm (GlobalTheory.EisM.hat (⇑θ) (x.val : ℤ) / 2)
  obtain ⟨hθne, hθb, hθper⟩ := hHat l ι N θ hl2
  obtain ⟨c0, hc0⟩ := hNf.int
  obtain ⟨c00, hc00, -, hc00F⟩ := hCoef l c0 c0 (Finset.univ.image cw) (by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact hθb _)
  obtain ⟨pr, cf, χd, lam, κA, hcf, hκA, hpadd, hpsmul, hpO, hpgal, hpT, hpU, hχd, hpdiam, hlamFR, hlamEq⟩ :=
    hAdm l Ω ι e S A W g hNf χg ψ₀ hgM hgl hkill hatt hine (fun s => hψ s) j hj ε X N χ α B cc c00 hN5 hgN hlN hχg hα hαq hEig.toEigF
  have hlp : Nat.Prime l := Fact.out
  have hlcopN : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨gm, hgm⟩ := hGm l N hlcopN
  have hψ₀n : ∀ x, ‖ψ₀ x‖ ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have : ψ 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero
      simp [ψ₀, this]
    · have h1 : ψ x ^ (l - 1) = 1 := by
        rw [← map_pow, ZMod.pow_card_sub_one_eq_one hx, map_one]
      have hpow : (ψ₀ x) ^ (l - 1) = 1 := by
        show (ι.symm (ψ x)) ^ (l - 1) = 1
        rw [← map_pow, h1, map_one]
      exact (isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, by have := hlp.two_le; omega, hpow⟩).norm_eq_one.le
  have hcwO : ∀ x, cw x ∈ cf.O := fun x => hcf (hc00F _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hWn : GlobalTheory.K4.AdmWn ι e g A W X pr N cw c₁ d₁ gm ψ₀ cf := by
    refine ⟨fun x _ => ?_, hcwO⟩
    refine ⟨hc1, hd1, ?_, ?_, hpadd, hpsmul, hpO, hpgal, hpT, fun r₀ => (hgm r₀).2.2.2, fun r₀ => (hgm r₀).2.1, χg, hkill, hine, fun s => hψ s⟩
    · simpa [mul_right_comm] using hc1cop
    · simpa [mul_right_comm] using hd1cop
  have hcwne : ∃ x, cw x ≠ 0 := by
    obtain ⟨x, hx⟩ := hθne
    exact ⟨x, by simpa [cw] using hx⟩
  have hmatO : ∀ (s : G ℚ Ω) (i k : Fin 2), mat W s i k ∈ cf.O := fun s i k => hcf (hc00 (hc0 s i k))
  obtain ⟨c₀', m, cf', S', Y, y, hZW, hSh, -, -, hYE, hYO, hcf', -, hSys, hIw, hSp⟩ :=
    hK4 l Ω ι e S A W g hNf ⟨hgM, hgl, χg, hkill, hatt, hine⟩ ε X pr N cw c₁ d₁ gm ψ₀ cf
      (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩)
      (fun r₀ => (hgm r₀).1) hlcopN hl2 he hcwne hWn hNf.cont hmatO
  obtain ⟨χ', hχ'eq, hχ'u, hχ'm, hχ'p⟩ := hChi l ι N χ χd hχd
  have hFR' : GlobalTheory.KummerEisensteinGalois.IsLamFR X A N (2 * e - 1) χ' j pr cf lam := by
    obtain ⟨h1, h2, cL, per, h3, h4⟩ := hlamFR
    exact ⟨h1, h2, cL, per, h3, fun n hn b hb φ hφ => h4 n hn b ⟨hb.1, fun d hd => by rw [hb.2 d hd, hχ'eq d hd]⟩ φ hφ⟩
  have hFR2 : GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χ' j pr cf lam := by
    refine ⟨fun d hd b hb => ?_, hFR'⟩
    rw [hχ'eq d hd]
    exact hpdiam b hb d hd
  have hK5adm : GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm (ι.symm α) :=
    ⟨hN5, hlcopN, fun r₀ => ⟨(hgm r₀).1, (hgm r₀).2.2.1⟩, hα, hpU⟩
  have hd₀ : (l + 1).Coprime l := by simp
  have hd₀1 : ((l + 1 : ℕ) : ZMod l) = 1 := by simp
  obtain ⟨m₀, c₂, κ5, v5, hκ5, hv5, hHT⟩ :=
    hK5 l Ω ι e S A W g hNf ⟨hgM, hgl, χg, hkill, hatt, hine⟩ ε X pr N cw c₁ d₁ gm ψ₀ cf (ι.symm α)
      (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩)
      hl2 he hWn hK5adm j hj c₀' Y hZW hSh hYE (fun r s y => hYO r s y 1) χ' hχ'u hχ'm hχ'p lam hFR2 (l + 1) hd₀ (by have := hlp.two_le; omega)
  set d₀ : ℕ := l + 1 with hd₀def
  let b4 : Fin 4 → Qbar l := smB (2 * e + 1) c₁ d₁ (ι.symm (θ c₁)) (ι.symm ((θ * χ)⁻¹ d₁))
  let β : Fin (4 + 4) → Qbar l := Fin.append b4 (fun i => -(d₀ : Qbar l) * b4 i)
  let t : Fin (4 + 4) → ℕ := Fin.append (smT N c₁ d₁) (fun i => d₀ * smT N c₁ d₁ i)
  let δ : ℕ → Qbar l := fun n => algebraMap ℚ_[l] (Qbar l) (χ' n)
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  have hc1N : c₁.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hc1cop
  have hd1N : d₁.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hd1cop
  have hδ : ∀ u, u.Coprime N → ι (δ u) = χ u := by
    intro u hu
    simp only [δ]
    rw [hχ'eq u hu]
    exact hχd u hu
  have hExpl : Expl ι e A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j
      ((-1) ^ e * ψ (-1)) (GlobalTheory.EisM.hat ⇑θ) (GlobalTheory.EisM.tw2 N ((-1) ^ e * ψ (-1))) α B cc 8 β t := by
    refine ⟨κ5 * κA * (N.totient : Qbar l), v5, max m₀ 1, c₂, ?_, hv5, htLaw_congr hHT ?_⟩
    · exact mul_ne_zero (mul_ne_zero hκ5 hκA) (Nat.cast_ne_zero.2 (Nat.totient_pos.2 (by omega)).ne')
    · intro m' hm' ψ' z
      have hR := hRhs hAvgEq hAvgMF l ι e N θ χ (fun q => g.a q) α B cc c₁ d₁ δ lam κA κ5 v5 hl2 he hlN hχm1 hα0 hc1N hd1N hEig hδ hlamEq m' hm' ψ' z
      have hsum : ∑ i, β i * ψ'⁻¹ (t i) = (1 - (d₀ : Qbar l) * ψ'⁻¹ d₀) * ∑ i, b4 i * ψ'⁻¹ (smT N c₁ d₁ i) := by
        have h1 : ∑ i : Fin 4, β (Fin.castAdd 4 i) * ψ'⁻¹ (t (Fin.castAdd 4 i)) = ∑ i, b4 i * ψ'⁻¹ (smT N c₁ d₁ i) := by
          simp only [β, t, Fin.append_left]
        have h2 : ∑ i : Fin 4, β (Fin.natAdd 4 i) * ψ'⁻¹ (t (Fin.natAdd 4 i)) = ∑ i, -((d₀ : Qbar l) * ψ'⁻¹ d₀ * (b4 i * ψ'⁻¹ (smT N c₁ d₁ i))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [β, t, Fin.append_right, Nat.cast_mul, map_mul]
          ring
        rw [Fin.sum_univ_add, h1, h2, Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring
      rw [← hθm1, hsum]
      calc _ = (1 - (d₀ : Qbar l) * ψ'⁻¹ d₀) * rhs5 N (2 * e + 1) cw c₁ d₁ δ lam v5 κ5 m' ψ' z := by
              unfold rhs5
              ring
        _ = _ := by
              rw [hR]
              split_ifs <;> ring
  have hExplS := hES l Ω ι e A cf _ j _ _ _ α B cc 8 β t m hExpl
  have hle : cf.O ≤ cf'.O := fun z hz => hcf' z hz
  have hExpl2 : Expl ι e A cf' (smZ d₀ hd₀ (fun r s u => (l : Qbar l) ^ m * Y r s u 1)) j
      ((-1) ^ e * ψ (-1)) (GlobalTheory.EisM.hat ⇑θ) (GlobalTheory.EisM.tw2 N ((-1) ^ e * ψ (-1))) α B cc 8 β t := by
    obtain ⟨κ, v', m₁, c₃, h1, h2, h3⟩ := hExplS
    refine ⟨κ, v', m₁, c₃, h1, h2, ?_⟩
    have h4 := (hMono l Ω cf cf' hle).2.2 _ _ _ _ _ _ h3
    convert h4 using 2
    unfold smZ
    funext s y
    beta_reduce
    ring
  have hψ₀1 : ∀ x, x ≠ 0 → ‖ψ₀ x‖ = 1 := by
    intro x hx
    have h1 : ψ x ^ (l - 1) = 1 := by
      rw [← map_pow, ZMod.pow_card_sub_one_eq_one hx, map_one]
    have hpow : (ψ₀ x) ^ (l - 1) = 1 := by
      show (ι.symm (ψ x)) ^ (l - 1) = 1
      rw [← map_pow, h1, map_one]
    exact (isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, by have := hlp.two_le; omega, hpow⟩).norm_eq_one
  have hχn : ∀ s, ‖((χg s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    intro s
    rw [hψ s]
    refine hψ₀1 _ ?_
    intro h0
    have h2 : ((χg s : (Qbar l)ˣ) : Qbar l) = 0 := by
      rw [hψ s]
      show ι.symm (ψ (cyc1 l s)) = 0
      rw [h0, MulChar.map_nonunit _ not_isUnit_zero, map_zero]
    exact (χg s).ne_zero h2
  have hrho : ∀ s, GlobalTheory.K4.rhoK W e ψ₀ s 1 1 = eps l s ^ e * ((χg s : (Qbar l)ˣ) : Qbar l)⁻¹ * mat W s 1 1 := by
    intro s
    simp only [GlobalTheory.K4.rhoK, GlobalTheory.K4.thK, Matrix.smul_apply, smul_eq_mul, mul_inv, inv_inv]
    rw [hψ s]
    rfl
  have hνine : ∀ s ∈ Ine A, GlobalTheory.K4.nuD W e ψ₀ s = 1 := by
    intro s hs
    have hd := hDet l Ω ι e S A W g χg hNf hkill hgM hatt s hs
    have h1 := hine s hs
    rw [hd, Units.val_pow_eq_pow_val, zpow_natCast] at h1
    have hx : ((χg s : (Qbar l)ˣ) : Qbar l) ≠ 0 := (χg s).ne_zero
    have hr : GlobalTheory.K4.rhoK W e ψ₀ s 1 1 = 1 := by
      rw [hrho s]
      simp only [eps]
      field_simp
      field_simp at h1
      linear_combination h1
    unfold GlobalTheory.K4.nuD
    rw [dif_pos (by rw [hr]; exact one_ne_zero)]
    ext
    simp [hr]
  have hνfrob : ∃ σ ∈ Dec A, IsFrob A l σ ∧ ‖((GlobalTheory.K4.nuD W e ψ₀ σ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    obtain ⟨⟨σ, hσD, hσF⟩, hmatn, hepsn⟩ := hFrob l Ω e S A W hNf
    have hn : ‖GlobalTheory.K4.rhoK W e ψ₀ σ 1 1‖ = 1 := by
      rw [hrho σ, norm_mul, norm_mul, norm_pow, hepsn σ, norm_inv, hχn σ, hmatn σ hσD]
      simp
    have hne : GlobalTheory.K4.rhoK W e ψ₀ σ 1 1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    refine ⟨σ, hσD, hσF, ?_⟩
    unfold GlobalTheory.K4.nuD
    rw [dif_pos hne]
    simpa using hn
  have hθc : ‖θ c₁‖ = 1 := by
    simpa using θ.unit_norm_eq_one (ZMod.unitOfCoprime c₁ hc1N)
  have hlc : ¬ l ∣ c₁ := fun h => hlp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hc1cop) ⟨6 * N, by ring⟩)
  have hld : ¬ l ∣ d₁ := fun h => hlp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hd1cop) ⟨6 * N, by ring⟩)
  obtain ⟨hsmT, hS4⟩ := hSmNz l ι e N c₁ d₁ ψ (θ c₁) ((θ * χ)⁻¹ d₁) hlN (by omega) (by omega) (by omega) hlc hld hθc hc1e
    (by rw [MulChar.inv_apply_eq_inv', ← zpow_neg_one]; exact (hd1e (-1) (-1) (Or.inr rfl)).1)
  have hld₀ : ¬ l ∣ d₀ := by
    intro h
    have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).1 h
    exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
  have ht : ∀ i, ¬ l ∣ t i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [t, Fin.append_left]
      exact hsmT i
    · simp only [t, Fin.append_right]
      intro h
      rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
      · exact hld₀ h
      · exact hsmT i h
  have hsumne : ∑ i, ι (β i) * ψ⁻¹ (t i) * (t i : ℂ) ^ e ≠ 0 := by
    have h1 : ∑ i : Fin 4, ι (β (Fin.castAdd 4 i)) * ψ⁻¹ (t (Fin.castAdd 4 i)) * (t (Fin.castAdd 4 i) : ℂ) ^ e =
        ∑ i, ι (b4 i) * ψ⁻¹ (smT N c₁ d₁ i) * (smT N c₁ d₁ i : ℂ) ^ e := by
      simp only [β, t, Fin.append_left]
    have h2 : ∑ i : Fin 4, ι (β (Fin.natAdd 4 i)) * ψ⁻¹ (t (Fin.natAdd 4 i)) * (t (Fin.natAdd 4 i) : ℂ) ^ e =
        ∑ i, -((d₀ : ℂ) ^ (e + 1) * (ι (b4 i) * ψ⁻¹ (smT N c₁ d₁ i) * (smT N c₁ d₁ i : ℂ) ^ e)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [β, t, Fin.append_right, Nat.cast_mul, map_mul, map_neg, map_natCast, hd₀1, map_one]
      ring
    rw [Fin.sum_univ_add, h1, h2, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have hne : (1 : ℂ) - (d₀ : ℂ) ^ (e + 1) ≠ 0 := by
      rw [sub_ne_zero]
      norm_cast
      have h2 : 1 < d₀ := by rw [hd₀def]; have := hlp.two_le; omega
      have h3 : e + 1 ≠ 0 := by omega
      exact (Nat.one_lt_pow h3 h2).ne
    have := mul_ne_zero hne hS4
    convert this using 1
    ring
  obtain ⟨c', hc', hP⟩ := hPin hMeas hCoef hMono l Ω ι e A W cf' (GlobalTheory.K4.nuD W e ψ₀) _ j _ _ ψ α B cc v 8 β t hl2 he hα
    (fun x hx => (hj x).1 hx) hνine hνfrob hMeasMu hv ht hsumne hExpl2
  obtain ⟨hSys2, hIw2, hSp2⟩ := hSm l Ω W cf' _ S' A (GlobalTheory.K4.nuD W e ψ₀) _ e ψ₀ d₀ hd₀ hd₀1 hψ₀n hSys hIw hSp
  have hM := hMono l Ω cf' c' hc'
  exact ⟨c', _, S', GlobalTheory.K4.nuD W e ψ₀, GlobalTheory.K4.chiK l ψ₀, _, hM.1 _ _ _ hSys2, hM.2.1 _ _ _ hIw2, hSp2, hP⟩

end UpperTheory.V.Z.Kato.Joint

end
