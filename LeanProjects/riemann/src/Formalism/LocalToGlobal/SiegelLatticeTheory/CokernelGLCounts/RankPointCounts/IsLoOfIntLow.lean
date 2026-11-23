import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SignTransposeTwisted

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Free

def Free {n : ℕ} (σ : Fin n → Fin n) (i j : Fin n) : Prop := j < i ∧ σ i < σ j

theorem off_free {K : Type*} [CommRing K] {n : ℕ} {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpat : ∀ i j, σ j < σ i → T i j = 0) {i j : Fin n}
    (h : ¬ Free σ i j) : T i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hT.2 i j hij, Matrix.one_apply_ne hij.ne]
  · rw [hT.1 i, Matrix.one_apply_eq]
  · have hne : σ i ≠ σ j := fun e => hij.ne' (by rw [← hσ i, e, hσ])
    have : σ j < σ i := by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ⟨hij, h'⟩ h
      · exact h'
    rw [hpat i j this, Matrix.one_apply_ne hij.ne']

theorem ent_free {E K : Type*} [Field E] [CommRing K] (ψ : E →+* K) {n : ℕ} {σ : Fin n → Fin n}
    (hσ : ∀ a, σ (σ a) = a) {X' : Matrix (Fin n) (Fin n) E} (hX' : IsLo X') (hpX : ∀ i j, σ j < σ i → X' i j = 0)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpT : ∀ i j, σ j < σ i → T i j = 0) {J : AddSubgroup K}
    (h : ∀ i j, Free σ i j → ψ (X' i j) - T i j ∈ J) : EntIn J (X'.map ψ - T) := by
  intro i j
  rw [Matrix.sub_apply, Matrix.map_apply]
  by_cases hf : Free σ i j
  · exact h i j hf
  · rw [off_free hσ hX' hpX hf, off_free hσ hT hpT hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem bnd_mats {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K} (O : Subring Fp)
    (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) (hx : ∀ x : K, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * x ∈ I)
    {n k : ℕ} (Ms : Fin k → Matrix (Fin n) (Fin n) K) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ m i j, algebraMap Fp K s * Ms m i j ∈ I := by
  obtain ⟨s, hs0, hsO, hs⟩ := bnd_fin O hI (fun q : Fin k × Fin n × Fin n => Ms q.1 q.2.1 q.2.2) (fun q => hx _)
  exact ⟨s, hs0, hsO, fun m i j => hs (m, i, j)⟩

theorem int_of_close {K : Type*} [CommRing K] {I : Subring K} {n : ℕ} {a : Matrix (Fin n) (Fin n) K}
    (h : EntIn (lat I 1) (a - 1)) (i j : Fin n) : a i j ∈ I := by
  have e : a i j = (a - 1) i j + (1 : Matrix (Fin n) (Fin n) K) i j := by rw [Matrix.sub_apply]; ring
  rw [e]
  refine I.add_mem (lat_one (h i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact I.one_mem
  · exact I.zero_mem

end Free

section BadL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def GoodAt (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ X' : PairVal.MatR D) : Prop :=
  TieN.IntLow (Zd.M p) (locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) ∧
    TieN.IntUp (Zd.M p) (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀))

def LocTarget (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ : PairVal.MatR D) : Prop :=
  ∃ (T : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (c : (D.s.atP p).Fp), c ≠ 0 ∧
    ∀ X' : PairVal.MatR D, IsLo X' → (∀ i j, fσ w j < fσ w i → X' i j = 0) →
      (∀ i j, Free (fσ w) i j → ∃ y ∈ (D.s.atP p).O,
        (D.s.atP p).ιE (X' i j) - T i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y) →
      GoodAt Zd p w L₁ U₁ A₀ B₀ X'

theorem isLo_of_intLow {p : PlF D} {l : MatP D p} (h : TieN.IntLow (Zd.M p) l) : IsLo l := ⟨h.1, h.2.1⟩

theorem isUp_of_intUp {p : PlF D} {ρ : MatP D p} (h : TieN.IntUp (Zd.M p) ρ) : IsUp ρ :=
  ⟨h.1, fun a b hab => h.2.1 b a hab⟩

theorem target_L (u u' : D.what₂.Word) (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hcv : ∀ a, (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) a *
      (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) a = 1 :=
    fun a => by simp only [← map_mul, cf_cfi, map_one]
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hYp : CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p =
      (1 : (D.s.atP p).Ep) • (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))) -
      (0 : (D.s.atP p).Ep) • Ecorner D.R.rS := by
    rw [one_smul, zero_smul, sub_zero, zzp_sgn_ord Zd u u' p hM Z₁, hZ, ptMat_mono']
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  rw [hYp] at hk
  obtain ⟨hTlo, hTpat, -⟩ := comp_target (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats 𝒪[(D.s.atP p).Fp] (fun s hs => alg_mem_O hs) (fun x => bounded x)
    ![cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁,
      cQ (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) U₁,
      cQ' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) U₁,
      Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i), Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i)⁻¹,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁]
  refine ⟨(cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹,
    t * (t * (t * (t * (t * 1)))), by simp [ht0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  rw [hYp] at hab
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have haX : l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) = (l⁻¹ * locL Zd p A₀ B₀) *
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * X' * L₁⁻¹).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))) := by
    rw [locL_L Zd p hM, locL_L Zd p hM, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)))
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG : EntIn (lat (D.s.atP p).O (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * 1))))))
      (X'.map (D.s.atP p).ιE - (cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹) := by
    refine ent_free (D.s.atP p).ιE hσ hX' hpat hTlo hTpat fun i j hf => ?_
    obtain ⟨y, hy, e⟩ := hfree i j hf
    refine ⟨y, hy, ?_⟩
    rw [e]
    simp only [map_mul, map_one]
  have hcl := comp_main (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk ha hb' hab haX
    (alg_mem_O htO) (D.s.atP p).O.one_mem
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    refine ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, fun i j => ?_⟩
    rw [hR]
    exact int_of_close hcl.1 i j
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    refine ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, fun i j => ?_⟩ hρ
    rw [hR]
    exact int_of_close hcl.2 i j

end BadL

end Formalism.L2.SG.Pf.TupGlobApprox
