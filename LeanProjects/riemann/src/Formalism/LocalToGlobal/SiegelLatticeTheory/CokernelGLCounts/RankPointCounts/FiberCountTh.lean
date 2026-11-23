import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue

noncomputable section

namespace Formalism.L2.SG.Pf.FCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ClsInv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (Mp : Loc.Model F E) {m : ℕ}

def toR {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : ∀ i j, A i j ∈ Mp.R) : Matrix (Fin n) (Fin n) Mp.R :=
  Matrix.of fun i j => ⟨A i j, h i j⟩

theorem toR_map {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : ∀ i j, A i j ∈ Mp.R) :
    (toR Mp A h).map Mp.R.subtype = A := by
  ext i j
  rfl

theorem toR_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ i j, A i j ∈ Mp.R) (hB : ∀ i j, B i j ∈ Mp.R)
    (hAB : ∀ i j, (A * B) i j ∈ Mp.R) : toR Mp (A * B) hAB = toR Mp A hA * toR Mp B hB := by
  apply Matrix.map_injective (f := Mp.R.subtype) Subtype.val_injective
  dsimp only
  rw [Matrix.map_mul, toR_map, toR_map, toR_map]

theorem toR_one {n : ℕ} (h : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j ∈ Mp.R) :
    toR Mp (1 : Matrix (Fin n) (Fin n) E) h = 1 := by
  apply Matrix.map_injective (f := Mp.R.subtype) Subtype.val_injective
  dsimp only
  rw [toR_map, Matrix.map_one _ (map_zero _) (map_one _)]

theorem toR_eq_one {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : ∀ i j, A i j ∈ Mp.R) (hA : A = 1) :
    toR Mp A h = 1 := by
  subst hA
  exact toR_one Mp h

theorem int_mul' {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, A i j ∈ Mp.R) (hB : ∀ i j, B i j ∈ Mp.R) :
    ∀ i j, (A * B) i j ∈ Mp.R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem clsOf_mul (X A Ai B Bi : Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    (hA : ∀ i j, A i j ∈ Mp.R) (hAi : ∀ i j, Ai i j ∈ Mp.R) (hB : ∀ i j, B i j ∈ Mp.R)
    (hBi : ∀ i j, Bi i j ∈ Mp.R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (h3 : B * Bi = 1) (h4 : Bi * B = 1)
    (hAl : ∀ i, A i (Fin.last m) = if i = Fin.last m then 1 else 0)
    (hBl : ∀ j, Bi (Fin.last m) j = if j = Fin.last m then 1 else 0) :
    clsOf Mp (A * X * B) = clsOf Mp X := by
  have hint : (∀ a b, (A * X * B) a b ∈ Mp.R) ↔ ∀ a b, X a b ∈ Mp.R := by
    constructor
    · intro h
      have e : X = Ai * (A * X * B) * Bi := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h3, Matrix.mul_one]
      rw [e]
      exact int_mul' Mp (int_mul' Mp hAi h) hBi
    · intro h
      exact int_mul' Mp (int_mul' Mp hA h) hB
  have dA : IsUnit A.det := IsUnit.of_mul_eq_one Ai.det (by rw [← Matrix.det_mul, h1, Matrix.det_one])
  have dB : IsUnit B.det := IsUnit.of_mul_eq_one Bi.det (by rw [← Matrix.det_mul, h3, Matrix.det_one])
  have hdet : IsUnit (A * X * B).det ↔ IsUnit X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, IsUnit.mul_iff, IsUnit.mul_iff]
    tauto
  unfold clsOf
  by_cases hX : (∀ a b, X a b ∈ Mp.R) ∧ IsUnit X.det
  · have hY : (∀ a b, (A * X * B) a b ∈ Mp.R) ∧ IsUnit (A * X * B).det := ⟨hint.2 hX.1, hdet.2 hX.2⟩
    rw [dif_pos hY, dif_pos hX]
    congr 1
    apply Quotient.sound

    set AR := toR Mp A hA
    set AiR := toR Mp Ai hAi
    set BR := toR Mp B hB
    set BiR := toR Mp Bi hBi
    set XR : Matrix (Fin (m + 1)) (Fin (m + 1)) Mp.R := Matrix.of fun a b => ⟨X a b, hX.1 a b⟩
    set YR : Matrix (Fin (m + 1)) (Fin (m + 1)) Mp.R := Matrix.of fun a b => ⟨(A * X * B) a b, hY.1 a b⟩
    have hXR : XR = toR Mp X hX.1 := rfl
    have hYR : YR = AR * XR * BR := by
      rw [show YR = toR Mp (A * X * B) hY.1 from rfl, hXR,
        toR_mul Mp (A * X) B (int_mul' Mp hA hX.1) hB hY.1, toR_mul Mp A X hA hX.1 (int_mul' Mp hA hX.1)]
    have h1R : AR * AiR = 1 := by
      rw [← toR_mul Mp A Ai hA hAi (int_mul' Mp hA hAi)]
      exact toR_eq_one Mp _ _ h1
    have h2R : AiR * AR = 1 := by
      rw [← toR_mul Mp Ai A hAi hA (int_mul' Mp hAi hA)]
      exact toR_eq_one Mp _ _ h2
    have h3R : BR * BiR = 1 := by
      rw [← toR_mul Mp B Bi hB hBi (int_mul' Mp hB hBi)]
      exact toR_eq_one Mp _ _ h3
    let f : (Fin (m + 1) → Mp.R) ≃ₗ[Mp.R] (Fin (m + 1) → Mp.R) :=
      LinearEquiv.ofLinear AiR.mulVecLin AR.mulVecLin
        (by rw [← Matrix.mulVecLin_mul, h2R, Matrix.mulVecLin_one])
        (by rw [← Matrix.mulVecLin_mul, h1R, Matrix.mulVecLin_one])
    have hsurjB : LinearMap.range BR.mulVecLin = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      refine ⟨BiR.mulVecLin v, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, h3R, Matrix.mulVecLin_one, LinearMap.id_apply]
    have hmap : (LinearMap.range YR.mulVecLin).map (f : (Fin (m + 1) → Mp.R) →ₗ[Mp.R] (Fin (m + 1) → Mp.R)) =
        LinearMap.range XR.mulVecLin := by
      have hf : (f : (Fin (m + 1) → Mp.R) →ₗ[Mp.R] (Fin (m + 1) → Mp.R)) = AiR.mulVecLin := rfl
      rw [hf, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, hYR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2R,
        Matrix.one_mul, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hsurjB]
    have hAil : ∀ i, Ai i (Fin.last m) = if i = Fin.last m then 1 else 0 := by
      intro i
      have e := congrFun (congrFun h2 i) (Fin.last m)
      rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)] at e
      · rw [hAl, if_pos rfl, mul_one] at e
        rw [e, Matrix.one_apply]
      · intro k _ hk
        rw [hAl, if_neg hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hinv : (A * X * B)⁻¹ = Bi * X⁻¹ * Ai := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv h3, Matrix.inv_eq_right_inv h1,
        Matrix.mul_assoc]
    refine ⟨⟨Submodule.Quotient.equiv _ _ f hmap, ?_, ?_⟩⟩
    · show Submodule.Quotient.mk (f (Pi.single (Fin.last m) 1)) = Submodule.Quotient.mk (Pi.single (Fin.last m) 1)
      congr 1
      funext i
      apply Subtype.ext
      show ((AiR *ᵥ Pi.single (Fin.last m) 1) i : E) = ((Pi.single (Fin.last m) (1 : Mp.R) : Fin (m + 1) → Mp.R) i : E)
      rw [Matrix.mulVec_single_one]
      show Ai i (Fin.last m) = _
      rw [hAil]
      by_cases hi : i = Fin.last m
      · subst hi
        simp
      · rw [if_neg hi, Pi.single_eq_of_ne hi]
        rfl
    · intro v
      induction v using Submodule.Quotient.induction_on with
      | H x =>
        show Mp.lam _ (Submodule.Quotient.mk (f x)) = Mp.lam _ (Submodule.Quotient.mk x)
        simp only [Loc.Model.lam, Submodule.liftQ_apply, Loc.Model.lamRaw, LinearMap.coe_comp,
          Function.comp_apply, Submodule.mkQ_apply, LinearMap.proj_apply, LinearMap.restrictScalars_apply,
          Matrix.mulVecLin_apply]
        congr 1
        have hfx : ((Algebra.linearMap Mp.R E).compLeft (Fin (m + 1))) (f x) =
            Ai *ᵥ ((Algebra.linearMap Mp.R E).compLeft (Fin (m + 1))) x := by
          funext i
          show ((AiR *ᵥ x) i : E) = (Ai *ᵥ (fun j => (x j : E))) i
          rw [← toR_map Mp Ai hAi]
          exact RingHom.map_mulVec Mp.R.subtype AiR x i
        have hXm : (Matrix.of fun a b => (⟨X a b, hX.1 a b⟩ : Mp.R)).map Mp.R.subtype = X := rfl
        have hYm : (Matrix.of fun a b => (⟨(A * X * B) a b, hY.1 a b⟩ : Mp.R)).map Mp.R.subtype = A * X * B := rfl
        have hBv : ∀ y : Fin (m + 1) → E, (Bi *ᵥ y) (Fin.last m) = y (Fin.last m) := by
          intro y
          rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last m)]
          · rw [hBl, if_pos rfl, one_mul]
          · intro k _ hk
            rw [hBl, if_neg hk, zero_mul]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [hXm, hYm, hfx, hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBv]
  · have hY : ¬ ((∀ a b, (A * X * B) a b ∈ Mp.R) ∧ IsUnit (A * X * B).det) :=
      fun h => hX ⟨hint.1 h.1, hdet.1 h.2⟩
    rw [dif_neg hY, dif_neg hX]

end ClsInv

section ThInv

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

theorem permSign_mul_self₂ (p : PlF D) : sgnP (D := D) p * sgnP p = 1 := by
  unfold sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgnP_int (p : PlF D) (i j : Fin (D.R.rS + 1)) : sgnP (D := D) p i j ∈ (M p).R := by
  unfold sgnP
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · exact Subring.zero_mem _

theorem sgnP_last (p : PlF D) (j : Fin (D.R.rS + 1)) :
    sgnP (D := D) p (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
  unfold sgnP
  rw [Matrix.diagonal_apply]
  by_cases h : j = Fin.last D.R.rS
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem one_int (p : PlF D) (i j : Fin (D.R.rS + 1)) : (1 : MatP D p) i j ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem mem_kkOrb_self (p : PlF D) (Y : MatP D p) : Y ∈ kkOrb M p Y :=
  ⟨1, 1, Formalism.L2.SG.Pf.LocOrbCut.intLow_one (M p), Formalism.L2.SG.Pf.LocOrbCut.intUp_one (M p), by
    rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem thL_inv (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Y' : MatP D p)
    (h : Y ∈ kkOrb M p (Y' * sgnP p)) : thL M δ T T' p w Y = thL M δ T T' p w Y' := by
  obtain ⟨l, ρ, hl, hρ, rfl⟩ := h
  unfold thL
  set C : MatP D p := Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0 with hCdef
  have hC1 : l * C * ρ = C :=
    Formalism.L2.SG.Pf.LocOrbSumPf.mul_of_mul l ρ _ (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_low l hl.1 hl.2.1)
      (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_up ρ hρ.1 hρ.2.1)
  have hC2 : C * sgnP p = C := by
    have := Formalism.L2.SG.Pf.LocOrbSumPf.mul_of_mul (1 : MatP D p) (sgnP p) (cornerSh δ T T' p w)
      (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_low 1 (fun a => Matrix.one_apply_eq a)
        (fun a b h => Matrix.one_apply_ne (ne_of_lt h))) (sgnP_last p)
    rw [Matrix.one_mul] at this
    exact this
  have e : l * (Y' * sgnP p) * ρ + C = l * ((Y' + C) * sgnP p) * ρ := by
    rw [add_mul, mul_add, add_mul, hC2, hC1]
  rw [e]
  have hli := Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (M p) hl
  have hρi := Formalism.L2.SG.Pf.LocOrbCut.intUp_inv (M p) hρ
  have dl : l.det = 1 := Formalism.DoubleCosetMeasures.isLowUni_det _ (Formalism.L2.SG.Pf.LocOrbCut.lowUni_of (M p) hl)
  have dρ : ρ.det = 1 := Formalism.DoubleCosetMeasures.isUpUni_det _ (Formalism.L2.SG.Pf.LocOrbCut.upUni_of (M p) hρ)
  have ul : IsUnit l.det := by rw [dl]; exact isUnit_one
  have uρ : IsUnit ρ.det := by rw [dρ]; exact isUnit_one
  rw [clsOf_mul (M p) ((Y' + C) * sgnP p) l l⁻¹ ρ ρ⁻¹ hl.2.2 hli.2.2 hρ.2.2 hρi.2.2
    (Matrix.mul_nonsing_inv l ul) (Matrix.nonsing_inv_mul l ul) (Matrix.mul_nonsing_inv ρ uρ)
    (Matrix.nonsing_inv_mul ρ uρ) (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_low l hl.1 hl.2.1)
    (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_up ρ⁻¹ hρi.1 hρi.2.1)]
  have e2 : (Y' + C) * sgnP p = 1 * (Y' + C) * sgnP p := by rw [Matrix.one_mul]
  rw [e2, clsOf_mul (M p) (Y' + C) 1 1 (sgnP p) (sgnP p) (one_int M p) (one_int M p) (sgnP_int M p)
    (sgnP_int M p) (Matrix.mul_one 1) (Matrix.mul_one 1) (permSign_mul_self₂ p) (permSign_mul_self₂ p)
    (Formalism.L2.SG.Pf.LocOrbSumPf.last_of_low 1 (fun a => Matrix.one_apply_eq a)
      (fun a b h => Matrix.one_apply_ne (ne_of_lt h))) (sgnP_last p)]

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem theta_of_tuple : ThOfTup M δ u u' F0 what₂ := by
  intro hN hrows hRel γ w hγ Z hZ hloc
  funext p
  have hpt := ptT_eq hN hrows hγ (hRel γ w hγ)
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ)) =
    thL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p Z)
  rw [hpt]
  have hl : kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p) =
      kkOrb M p (CntLocal.ZZP (M := M) δ u u' p Z * sgnP p) := congrFun hloc p
  have hmem : CntLocal.ZZP (M := M) δ u u' p Z * sgnP p ∈
      kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p) := by
    rw [hl]
    exact mem_kkOrb_self M p _
  rw [← thL_inv M δ _ _ p w _ _ hmem,
    thL_inv M δ _ _ p w _ _ (mem_kkOrb_self M p (CntLocal.ZZP (M := M) δ u u' p Z * sgnP p))]

theorem theta_of_class : ThOfCls M δ u u' := by
  intro w Z hZ p hcls
  have hrep : repL M δ (D.mem u).A.T (D.mem u').A.T p w (tupZ M δ u u' Z p) = hcls.choose := dif_pos hcls
  obtain ⟨-, -, hO⟩ := hcls.choose_spec
  rw [hrep]
  have hmem : hcls.choose ∈ kkOrb M p (CntLocal.ZZP (M := M) δ u u' p Z * sgnP p) := by
    have h := mem_kkOrb_self M p hcls.choose
    rw [← hO] at h
    exact h
  exact thL_inv M δ _ _ p w _ _ hmem

end ThInv

section Final

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fiberCount_of_rest {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hPH : PrimeHyp D u (Tu D u')) (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : EligRel u u' F0 what₂)
    (hE : Exist M δ u u') (hTS : ThSome M δ u u' F0 what₂) (hFS : FibSum M δ u u' F0 what₂)
    (hNN : NuNotCls M δ u u' F0 what₂) (hDT : DensTh M δ L u u') (hEP : EligPos u u' F0 what₂) :
    FiberCount M δ L u u' F0 what₂ :=
  fiberCount_of hA hT hPH hU hR hrows hN hRel (Formalism.L2.SG.Pf.pcount_restr hA hrows hN) hE hTS
    (theta_of_tuple M δ u u' F0 what₂) (theta_of_class M δ u u') hFS hNN hDT (leadingMinors_of_matrix u u') hEP

end Final

end Formalism.L2.SG.Pf.FCount
