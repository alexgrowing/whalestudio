import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedLeadingTermSplitZMinor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EquivariantMapEqSmul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
open Formalism.MainNotions.PrimeDegreeVariant (embGL lastGL)

theorem isBlock_embGL (R : Type) [CommRing R] {N n : ℕ} (hN : N = n + 1) (g : GL (Fin n) R) :
    IsBlock hN (embGL R n N hN.symm g : Matrix (Fin N) (Fin N) R) (g : Matrix (Fin n) (Fin n) R) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> rw [GlobalTheory.Branching.embGL_apply]
  · simp [iC]
  · have := a.2
    simp [iC, iL, Fin.ext_iff]; omega
  · have := a.2
    simp [iC, iL, Fin.ext_iff]; omega
  · simp [iL]

theorem isBlock_mul_lastGL {R : Type} [CommRing R] {N n : ℕ} {hN : N = n + 1} {g' : GL (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} (h : IsBlock hN (g' : Matrix (Fin N) (Fin N) R) A 1) (t : Rˣ) :
    IsBlock hN ((g' * lastGL R N t : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) A (t : R) := by
  have e : ∀ a b, ((g' * lastGL R N t : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b =
      (g' : Matrix (Fin N) (Fin N) R) a b * ((if b.1 + 1 = N then t else 1 : Rˣ) : R) := by
    intro a b
    rw [Units.val_mul]
    exact Matrix.mul_diagonal _ _ _ _
  have hc : ∀ a : Fin n, ¬ ((iC hN a).1 + 1 = N) := fun a => by have := a.2; simp only [iC]; omega
  have hl : (iL hN).1 + 1 = N := hN.symm
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> rw [e]
  · rw [if_neg (hc b), h.1]; simp
  · rw [(h.2.1 a).1, zero_mul]
  · rw [(h.2.1 a).2, zero_mul]
  · rw [if_pos hl, h.2.2, one_mul]

theorem isBlock_lastGL (R : Type) [CommRing R] {N n : ℕ} (hN : N = n + 1) (t : Rˣ) :
    IsBlock hN ((lastGL R N t : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) ((1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
      (t : R) := by
  have h := isBlock_mul_lastGL (isBlock_embGL R hN 1) t
  rwa [map_one, one_mul] at h

theorem sum_bExp {N n : ℕ} (hN : N = n + 1) {lam : DomWeight N} {sg : DomWeight n} (hI : Interlace hN lam sg) :
    ((∑ s, (bBr hN lam sg s).toNat : ℕ) : ℤ) + lam.detShift = nBr lam sg := by
  have h1 : lam.detShift = lam.w (iL hN) := by
    unfold DomWeight.detShift
    rw [dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp only [iL]; omega)
  have h2 : ∑ s, (((bBr hN lam sg s).toNat : ℕ) : ℤ) = ∑ s, (lam.w (iC hN s) - sg.w s) :=
    Finset.sum_congr rfl fun s _ => Int.toNat_of_nonneg (hI s).2
  rw [h1, nBr, sum_split hN lam.w, Nat.cast_sum, h2, Finset.sum_sub_distrib]
  ring

theorem brStd_rhoK {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, SameShift (lam τ) (sg τ)) (g : ι → GL (Fin n) K) (g' : ι → GL (Fin N) K) (t : ι → K)
    (h : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) (t τ)) (G : VV K lam) :
    brStd hN lam sg (rhoK lam g' G) = (∏ τ, t τ ^ nBr (lam τ) (sg τ)) • rhoK sg g (brStd hN lam sg G) := by
  apply Subtype.ext
  have ht : ∀ τ, t τ ≠ 0 := fun τ h0 => by
    have h1 := (h τ).det
    rw [h0, mul_zero] at h1
    exact (Matrix.GeneralLinearGroup.det (g' τ)).ne_zero h1
  have hd : detTwK lam g' * ∏ τ, t τ ^ ∑ s, bExp hN lam sg τ s = (∏ τ, t τ ^ nBr (lam τ) (sg τ)) * detTwK sg g := by
    rw [detTwK, detTwK, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← sum_bExp hN (hI τ), zpow_add₀ (ht τ), zpow_natCast, detPow, detPow, hS τ, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      (h τ).det, mul_zpow]
    simp only [bExp]
    ring
  simp only [brStd, brStdP, LinearMap.comp_apply, Submodule.subtype_apply, rhoK_coe, LinearMap.smul_apply, actP, trAct,
    AlgHom.toLinearMap_apply, map_smul, Submodule.coe_smul]
  rw [coefLast_blockAct K ι hN _ _ _ t fun τ => (h τ).transpose, map_smul, Submodule.coe_smul, projVV_blockAct]
  simp only [smul_smul]
  congr 1
  linear_combination (brConst hN K lam sg) * hd

theorem equivariance : Equivariance := by
  intro K _ _ ι _ N n hN lam sg hI hS g g' h G
  rw [brStd_rhoK hN hI hS g g' (fun _ => 1) h G]
  simp

theorem brAt_eq_pullback {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, SameShift (lam τ) (sg τ)) (g : ι → GL (Fin n) K) (g' : ι → GL (Fin N) K) (t : ι → K) (ht : ∀ τ, t τ ≠ 0)
    (h : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) (t τ)) (G : VV K lam) :
    brStd hN lam sg (rhoK lam g'⁻¹ G) = rhoK sg g⁻¹ (brAt hN lam sg t G) := by
  have h1 := brStd_rhoK hN hI hS g g' t h (rhoK lam g'⁻¹ G)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
  rw [brAt, LinearMap.smul_apply, h1, smul_smul, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (ht τ), neg_add_cancel, zpow_zero], one_smul,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem homogeneity : Homogeneity := by
  intro K _ _ ι _ N n hN lam sg hI hS t
  refine ⟨?_, brAt_eq hN lam sg t⟩
  ext1 G
  have h := brAt_eq_pullback hN hI hS 1 (fun τ => lastGL K N (t τ)) (fun τ => (t τ : K)) (fun τ => (t τ).ne_zero)
    (fun τ => isBlock_lastGL K hN (t τ)) G
  rw [inv_one, map_one, Module.End.one_apply] at h
  exact h

section One

variable {K : Type} [Field K] {N n : ℕ}

theorem rename_snd_unit (f : MvPolynomial (Fin n × Fin n) K) :
    rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
      (rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) f) = f := by
  rw [rename_rename]
  exact rename_id_apply _

theorem ten_unit (f : MvPolynomial (Fin n × Fin n) K) :
    ten (fun _ : Unit => f) = rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) f := by
  simp [ten, Formalism.GradedWeylDivisibility.blockEmb]

theorem ten_unit_mem {sg : DomWeight n} {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ nablaSq K n sg) :
    ten (fun _ : Unit => f) ∈ VV K fun _ : Unit => sg :=
  Submodule.subset_span ⟨fun _ => f, fun _ => hf, rfl⟩

theorem exists_ten_unit {sg : DomWeight n} {F : Pol K Unit n} (hF : F ∈ VV K fun _ : Unit => sg) :
    ∃ f ∈ nablaSq K n sg, F = ten fun _ : Unit => f := by
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨f (), hf (), rfl⟩
  | zero => exact ⟨0, zero_mem _, by simp [ten_unit]⟩
  | add y z _ _ hy hz =>
    obtain ⟨f, hf, rfl⟩ := hy
    obtain ⟨g, hg, rfl⟩ := hz
    exact ⟨f + g, add_mem hf hg, by simp [ten_unit]⟩
  | smul a y _ hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨a • f, Submodule.smul_mem _ _ hf, by simp [ten_unit]⟩

theorem brOne_mem (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) :
    brOne K hN lam sg f ∈ nablaSq K n sg := by
  simp only [brOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply]
  obtain ⟨g, hg, e⟩ := exists_ten_unit (brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg)
    (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) f)).2
  rw [e, ten_unit, rename_snd_unit]
  exact hg

theorem brOne_sqAct [CharZero K] (hN : N = n + 1) {lam : DomWeight N} {sg : DomWeight n} (hI : Interlace hN lam sg)
    (hS : SameShift lam sg) (g : GL (Fin n) K) {f : MvPolynomial (Fin N × Fin N) K} (hf : f ∈ nablaSq K N lam) :
    brOne K hN lam sg (sqAct K N lam (embGL K n N hN.symm g) f) = sqAct K n sg g (brOne K hN lam sg f) := by
  have h := equivariance K Unit N n hN (fun _ => lam) (fun _ => sg) (fun _ => hI) (fun _ => hS) (fun _ => g)
    (fun _ => embGL K n N hN.symm g) (fun _ => isBlock_embGL K hN g) ⟨_, ten_unit_mem hf⟩
  have h1 := brOne_rename K hN lam sg (rhoK (fun _ => lam) (fun _ => embGL K n N hN.symm g) ⟨_, ten_unit_mem hf⟩)
  have h2 := brOne_rename K hN lam sg ⟨_, ten_unit_mem hf⟩
  obtain ⟨y, -, e⟩ := exists_ten_unit (brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) ⟨_, ten_unit_mem hf⟩).2
  rw [h, rhoK_coe, rhoK_coe, e, actTen, actTen, ten_unit, ten_unit, rename_snd_unit, rename_snd_unit] at h1
  rw [e] at h2
  simp only [ten_unit, rename_snd_unit] at h2
  rw [h1, h2]

theorem brOne_xi [CharZero K] (hN : N = n + 1) {lam : DomWeight N} {sg : DomWeight n} (hI : Interlace hN lam sg)
    (hS : SameShift lam sg) :
    brOne K hN lam sg (xiBr K hN lam sg) = (((cBr hN lam sg : ℤ) : K) * kapBr K hN lam sg) • extremal K n sg := by
  have h := projVV_coe (fun _ : Unit => sg) ⟨_, extVV_mem K fun _ : Unit => sg⟩
  simp only [extVV, ten_unit] at h
  simp only [brOne, brStdP, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply, LinearMap.smul_apply,
    GlobalTheory.XiTopCoef.coefLast_xi K N n hN lam sg hI hS, h, Submodule.coe_smul, map_smul, rename_snd_unit, brConst, Finset.univ_unique,
    Finset.prod_singleton]

end One

theorem cBr_eq {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    cBr hN lam sg = Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem xiBr_eq (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    xiBr K hN lam sg = Formalism.MainNotions.PrimeDegreeVariant.xi K hN.symm lam sg := by
  refine Finset.prod_congr rfl fun i _ => ?_
  have : zMinor K hN i = Formalism.GradedWeylDivisibility.initMinor K (Formalism.MainNotions.PrimeDegreeVariant.rowsZ hN.symm i) (by have := i.2; omega) := by
    unfold zMinor
    congr 1
    funext p
    have := p.2
    unfold Formalism.MainNotions.PrimeDegreeVariant.rowsZ
    split_ifs <;> first | rfl | omega | exact Fin.ext (by simp only [iL]; omega)
  rw [this]
  rfl

theorem map_xi {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N n : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (sg : DomWeight n) : map φ (Formalism.MainNotions.PrimeDegreeVariant.xi R h lam sg) = Formalism.MainNotions.PrimeDegreeVariant.xi S h lam sg := by
  simp only [Formalism.MainNotions.PrimeDegreeVariant.xi, map_prod, map_mul, map_pow, Formalism.GradedWeylDivisibility.lpMinor, Formalism.GradedWeylDivisibility.initMinor, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext1 a b <;> simp

theorem fockF_eq {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = fockB f (map (starRingEnd ℂ) g) := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map]
  rfl

theorem normFock_smul {N : ℕ} (lam : DomWeight N) (a b : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (a • f) (b • g) = a * starRingEnd ℂ b * normFock lam f g := by
  have : map (starRingEnd ℂ) (b • g) = starRingEnd ℂ b • map (starRingEnd ℂ) g := by
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  simp only [normFock, fockF_eq _ (b • g), fockF_eq f g, this, ← fockBL_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem fockF_self_ne {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) :
    Formalism.REAL.fockF f f ≠ 0 ∧ starRingEnd ℂ (Formalism.REAL.fockF f f) = Formalism.REAL.fockF f f := by
  have h := Formalism.GradedWeylDivisibility.fockPos σ f hf
  refine ⟨fun h0 => ?_, Complex.conj_eq_iff_im.2 h.2⟩
  rw [h0] at h
  simp at h

theorem map_mem_delSq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam : DomWeight n)
    {f : MvPolynomial (Fin n × Fin n) R} (hf : f ∈ delSq R n lam) : map φ f ∈ delSq S n lam := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem brOne_eq_transpose {N n : ℕ} (hN : N = n + 1) {lam : DomWeight N} {sg : DomWeight n} (hI : Interlace hN lam sg)
    (hS : SameShift lam sg) (hc : Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg ≠ 0) (hx : Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg ≠ 0)
    {io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    {br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ}
    (hio : Formalism.MainNotions.PrimeDegreeVariant.IsIota hN.symm lam sg io) (hbr : Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg br)
    (hT : Formalism.MainNotions.PrimeDegreeVariant.IsTranspose lam sg io br) : ∀ f ∈ delSq ℂ N lam, brOne ℂ hN lam sg f = br f := by
  have eN := nablaSq_eq_delSq ℂ lam
  have en := nablaSq_eq_delSq ℂ sg
  obtain ⟨a, ha⟩ := GlobalTheory.Branching.equivariant_map_eq_smul n N hN.symm lam sg ((interlace_iff hN lam sg).1 hI) (brOne ℂ hN lam sg) br
    (by
      rintro ψ (rfl | rfl)
      · exact ⟨fun f _ => brOne_mem hN lam sg f, fun g f hf => brOne_sqAct hN hI hS g hf⟩
      · rw [eN, en]
        exact ⟨hbr.2.1, hbr.2.2.2.1⟩)
    (by rw [eN]; exact hbr.2.2.1)
  have hc' : ((Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hc
  have he : extremal ℂ n sg ∈ nablaSq ℂ n sg := Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone sg)
  have hxi : Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg ∈ nablaSq ℂ N lam := by
    have h1 := hio.2.1 _ he
    rw [hio.2.2.2.1] at h1
    exact (Submodule.smul_mem_iff _ hc').1 h1
  obtain ⟨x1, x2⟩ := fockF_self_ne hx
  obtain ⟨e1, e2⟩ := fockF_self_ne (f := extremal ℂ N lam) (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW)
  obtain ⟨s1, -⟩ := fockF_self_ne (f := extremal ℂ n sg) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl sg.natW)
  have hk : kapBr ℂ hN lam sg = normFock lam (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg) (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg) := by
    rw [kapBr, normFock, fockF_eq, fockF_eq, map_xi, Formalism.L2.DIV.map_extremal, xiBr_eq]
  have hk0 : kapBr ℂ hN lam sg ≠ 0 := by rw [hk]; exact div_ne_zero x1 e1
  have hks : starRingEnd ℂ (kapBr ℂ hN lam sg) = kapBr ℂ hN lam sg := by rw [hk, normFock, map_div₀, x2, e2]
  have h1 := hT _ he _ (eN ▸ hxi)
  have h2 := brOne_xi (K := ℂ) hN hI hS
  rw [xiBr_eq, ha _ hxi, cBr_eq] at h2
  have h3 := congrArg (fun y => normFock sg ((1 : ℂ) • extremal ℂ n sg) y) h2
  have h4 := normFock_smul lam ((Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg : ℤ) : ℂ) 1 (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg)
    (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg)
  rw [one_smul, ← hio.2.2.2.1, h1, ← hk, map_one, mul_one] at h4
  have h5 : normFock sg (extremal ℂ n sg) (extremal ℂ n sg) = 1 := div_self s1
  simp only [normFock_smul, h4, h5, map_mul, hks, map_intCast, one_mul, mul_one] at h3
  have ha1 : a = 1 := by
    have := mul_right_cancel₀ (mul_ne_zero hc' hk0) (h3.trans (one_mul _).symm)
    simpa using congrArg (starRingEnd ℂ) this
  intro f hf
  rw [ha f (eN ▸ hf), ha1, one_smul]

theorem onePlace (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) : OnePlace := by
  intro N n hN lam sg hI hS
  obtain ⟨hc, -, hx, -, io, br, hio, hbr, hT⟩ := h6 n N hN.symm lam sg ((interlace_iff hN lam sg).1 hI)
  have e := brOne_eq_transpose hN hI hS hc hx hio hbr hT
  have st : ∀ g, ∀ f ∈ delSq ℂ N lam, sqAct ℂ N lam g f ∈ delSq ℂ N lam := fun g => (factSqStable ℂ N lam g).2
  obtain ⟨b1, b2, ⟨f0, hf0, b3⟩, b4, b5, b6⟩ := hbr
  refine ⟨fun f hf => ?_, fun f hf => ?_, ⟨f0, hf0, ?_⟩, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [e _ (map_mem_delSq _ lam hf)]
    exact b1 f hf
  · rw [e f hf]; exact b2 f hf
  · rw [e f0 hf0]; exact b3
  · rw [e _ (st _ f hf), e f hf]; exact b4 g f hf
  · rw [e _ (st _ f hf), e f hf]; exact b5 a f hf
  · rw [e f hf]; exact b6 f hf

theorem transposed (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) : Transposed := by
  intro N n hN lam sg hI hS
  obtain ⟨hc, -, hx, -, io, br, hio, hbr, hT⟩ := h6 n N hN.symm lam sg ((interlace_iff hN lam sg).1 hI)
  refine ⟨io, hio, fun s hs f hf => ?_⟩
  rw [brOne_eq_transpose hN hI hS hc hx hio hbr hT f hf]
  exact hT s hs f hf

theorem coeff_prod_rename {A ι : Type} [CommRing A] [Fintype ι] {n : ℕ} (b : ι → Fin n → ℕ)
    (P : ι → MvPolynomial (Unit × Fin n) A) :
    coeff (expOf b) (∏ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ)) =
      ∏ τ, coeff (expOf fun _ : Unit => b τ) (P τ) := by
  classical
  have hinj : ∀ τ : ι, Function.Injective (fun p : Unit × Fin n => (τ, p.2)) :=
    fun τ p q h => Prod.ext rfl (Prod.mk.inj h).2
  have h1 : ∀ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ) =
      ∑ m ∈ (P τ).support, monomial (m.mapDomain fun p : Unit × Fin n => (τ, p.2)) (coeff m (P τ)) := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, coeff (expOf fun _ : Unit => b τ) (P τ) =
      ∑ m ∈ (P τ).support, if m = expOf (fun _ : Unit => b τ) then coeff m (P τ) else 0 := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    simp only [coeff_sum, coeff_monomial]
  simp only [h1]
  rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_univ_sum, Finset.prod_univ_sum, coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← monomial_sum_prod, coeff_monomial, Finset.prod_ite_zero]
  have h3 : ∀ τ s, (∑ τ', (p τ').mapDomain fun q : Unit × Fin n => (τ', q.2)) (τ, s) = p τ ((), s) := by
    intro τ s
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply (hinj τ) (p τ) ((), s)
    · intro τ' _ h
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q, hq⟩
      exact h (Prod.mk.inj hq).1
    · simp
  congr 1
  apply propext
  constructor
  · intro h τ _
    ext q
    rw [← h3 τ q.2, h]
    rfl
  · intro h
    ext q
    rw [h3 q.1 q.2, h q.1 (Finset.mem_univ _)]
    rfl

theorem splitLast_blockEmb {K ι : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (τ : ι) (f : MvPolynomial (Fin N × Fin N) K) :
    splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) f))) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [Formalism.GradedWeylDivisibility.blockEmb, rename_C, splitLast_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have : splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ (X v)) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (X v)))) := by
      obtain ⟨a, s⟩ := v
      rw [fk_blockEmb_X, rename_X]
      rcases cases_idx hN s with rfl | ⟨s, rfl⟩
      · simp only [splitLast_X_lastCol, map_zero]
      · rcases cases_idx hN a with rfl | ⟨a, rfl⟩
        · simp only [splitLast_X_lastRow, map_X, rename_X]
        · simp only [splitLast_X_up, map_C, rename_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
    rw [map_mul, map_mul, hp, this, map_mul, map_mul, map_mul, map_mul]

theorem coefLast_ten {K ι : Type} [Field K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin N × Fin N) K) :
    coefLast hN b (ten f) = ten fun τ => rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
      (coefLast hN (fun _ : Unit => b τ) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (f τ))) := by
  rw [coefLast_eq_coeff, ten, ten, map_prod]
  simp only [splitLast_blockEmb]
  rw [coeff_prod_rename]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [coeff_map, coefLast_eq_coeff, Formalism.GradedWeylDivisibility.blockEmb, rename_rename]
  rfl

theorem fockB_ten {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockB (ten f) (ten g) = ∏ τ, fockB (f τ) (g τ) :=
  @fockSymTensor_holds K _ starRingOfComm ι _ n f g

theorem rename_unit_snd {K : Type} [Field K] {n : ℕ} (F : Pol K Unit n) :
    ten (fun _ : Unit => rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) F) = F := by
  rw [ten_unit, rename_rename]
  exact rename_id_apply _

theorem fockB_snd {K : Type} [Field K] {n : ℕ} (F : Pol K Unit n) (y : MvPolynomial (Fin n × Fin n) K) :
    fockB (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) F) y = fockB F (ten fun _ : Unit => y) := by
  conv_rhs => rw [← rename_unit_snd F, fockB_ten]
  simp

theorem tensor : Tensor := by
  intro K _ _ ι _ N n hN lam sg _ _ f G _ hG
  have hm : (ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)) ∈ VV K sg :=
    GlobalTheory.Proof.TensorMapDescent.ten_mem sg _ fun τ => brOne_mem hN _ _ _
  refine congrArg Subtype.val (eq_of_fockB sg (x' := ⟨_, hm⟩) fun y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    change fockB _ (ten y) = fockB (ten _) (ten y)
    rw [fockB_ten]
    simp only [brOne, brStd, brStdP, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply,
      LinearMap.smul_apply, Submodule.coe_smul, map_smul, ← fockBL_apply, smul_eq_mul]
    simp only [fockBL_apply]
    rw [fockB_projVV sg _ (GlobalTheory.Proof.TensorMapDescent.ten_mem sg y hy), hG, coefLast_ten, fockB_ten, brConst,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [fockB_snd, fockB_snd, fockB_projVV _ _ (ten_unit_mem (hy τ)), brConst]
    simp only [Finset.univ_unique, Finset.prod_singleton]
    rfl
  | zero => simp only [← fockBL_apply, map_zero]
  | add y z _ _ hy hz => simp only [← fockBL_apply, map_add] at *; rw [hy, hz]
  | smul a y _ hy => simp only [← fockBL_apply, map_smul] at *; rw [hy]

theorem brOne_mem_del (h1 : OnePlace) {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) {lam : DomWeight N}
    {sg : DomWeight n} (hI : Interlace hN lam sg) (hS : SameShift lam sg) {f : MvPolynomial (Fin N × Fin N) (𝓞 K)}
    (hf : f ∈ delSq (𝓞 K) N lam) : brOne K hN lam sg (toK K _ f) ∈ (delSq (𝓞 K) n sg).map (toK K _) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    let f0 := Formalism.GradedWeylDivisibility.applyWord ℤ v (Formalism.GradedWeylDivisibility.hw ℤ le_rfl lam.natW)
    obtain ⟨g, hg, e⟩ := (h1 N n hN lam sg hI hS).1 f0 (Submodule.subset_span ⟨v, rfl⟩)
    have hm : ∀ (L : Type) [Field L] [CharZero L] {σ : Type} (P : MvPolynomial σ ℤ),
        map (Int.castRingHom L) P = map (algebraMap ℚ L) (map (Int.castRingHom ℚ) P) := fun L _ _ _ P => by
      rw [map_map, Subsingleton.elim ((algebraMap ℚ L).comp (Int.castRingHom ℚ)) (Int.castRingHom L)]
    rw [hm ℂ f0, hm ℂ g, GlobalTheory.Proof.TensorMapDescent.brOne_map] at e
    have e' := MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective e
    have hk : ∀ {σ : Type} (P : MvPolynomial σ ℤ), toK K σ (map (Int.castRingHom (𝓞 K)) P) = map (Int.castRingHom K) P :=
      fun P => by
        change map (algebraMap (𝓞 K) K) _ = _
        rw [map_map, Subsingleton.elim ((algebraMap (𝓞 K) K).comp (Int.castRingHom (𝓞 K))) (Int.castRingHom K)]
    refine ⟨map (Int.castRingHom (𝓞 K)) g, map_mem_delSq _ sg hg, ?_⟩
    have hf0 : Formalism.GradedWeylDivisibility.applyWord (𝓞 K) v (Formalism.GradedWeylDivisibility.hw (𝓞 K) le_rfl lam.natW) = map (Int.castRingHom (𝓞 K)) f0 := by
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    simp only
    rw [hf0, hk, hk, hm K f0, hm K g, GlobalTheory.Proof.TensorMapDescent.brOne_map, e']
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [map_smul, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ hy

theorem brStd_mem_delStd (h1 : OnePlace) {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {N n : ℕ}
    (hN : N = n + 1) {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, SameShift (lam τ) (sg τ)) (G : VV K lam) (hG : (G : Pol K ι N) ∈ delStd K lam) :
    ((brStd hN lam sg G : VV K sg) : Pol K ι n) ∈ delStd K sg := by
  change ((brStdP hN lam sg (G : Pol K ι N) : VV K sg) : Pol K ι n) ∈ delStd K sg
  generalize (G : Pol K ι N) = F at hG
  induction hG using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    choose f0 hf0 e using hf
    have hn : ∀ τ, f τ ∈ nablaSq K N (lam τ) := fun τ => by
      rw [nablaSq_eq_delSq, ← e τ]
      exact map_mem_delSq (algebraMap (𝓞 K) K) _ (hf0 τ)
    have h := tensor K ι N n hN lam sg hI hS f ⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn⟩ hn rfl
    refine Submodule.subset_span ⟨_, fun τ => ?_, h⟩
    rw [← e τ]
    exact brOne_mem_del h1 hN (hI τ) (hS τ) (hf0 τ)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ hy

theorem integrality (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) : Integrality := by
  intro K _ _ ι _ N n hN lam sg hI hS M t ht G hG
  simp only [delK, delP, transLat, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.coe_restrictScalars,
    Submodule.subtype_apply] at hG ⊢
  intro w B hB
  have hb : ∀ τ, IsBlock hN ((embGL K n N hN.symm (B τ) * lastGL K N (Units.mk0 (t τ) (ht τ)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) (B τ : Matrix (Fin n) (Fin n) K) (t τ) :=
    fun τ => isBlock_mul_lastGL (isBlock_embGL K hN (B τ)) (Units.mk0 (t τ) (ht τ))
  obtain ⟨s, hs, h1⟩ := hG w _ fun τ => GlobalTheory.BranchBasis.isBasisAt_block K N n hN w (M τ) (t τ) (B τ) _ (hb τ) (hB τ)
  refine ⟨s, hs, ?_⟩
  rw [← rhoK_coe] at h1 ⊢
  rw [← brAt_eq_pullback hN hI hS B _ t ht hb G]
  have h2 := brStd_mem_delStd (onePlace h6) hN hI hS (s • _) h1
  rw [LinearMap.map_smul_of_tower] at h2
  exact h2

theorem statement_of_branching (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) : Statement :=
  ⟨onePlace h6, equivariance, integrality h6, homogeneity, GlobalTheory.BranchMembers.members⟩

end GlobalTheory.BranchFormula
