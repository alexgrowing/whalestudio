import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel Topology Filter
open scoped TensorProduct

namespace GlobalTheory.SmGL.PrinProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev eSt (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

abbrev sB {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) : Representation ℂ (parab k (points (Fin n))) ℂ :=
  (twist ((ofChar (torusChar χ)).comp (leviTorus k (Fin n)).symm.toMonoidHom)
    (deltaHalf k (fun _ : Fin n => Unit))).comp (leviProj k (points (Fin n)))

def dg {n : ℕ} : parab k (points (Fin n)) →* (Fin n → kˣ) :=
  (leviTorus k (Fin n)).symm.toMonoidHom.comp (leviProj k (points (Fin n)))

theorem val_dg {n : ℕ} (p : parab k (points (Fin n))) (i : Fin n) :
    (dg p i : k) = (p : GL (Fin n) k).val i i := by
  show ((Matrix.GeneralLinearGroup.det (leviProj k (points (Fin n)) p i) : kˣ) : k) = _
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  rfl

variable (k) in

def twoBlockParabolicFirstBlock (r t : ℕ) : parab k (two (eSt r t)) →* GL (Fin r) k := (MonoidHom.fst _ _).comp (Stages.pr _)

variable (k) in

def midPar (r t : ℕ) : Subgroup (GL (Fin (r + t)) k) :=
  ((parab k (points (Fin r))).comap (twoBlockParabolicFirstBlock k r t)).map (parab k (two (eSt r t))).subtype

theorem midPar_le (r t : ℕ) : midPar k r t ≤ parab k (two (eSt r t)) := Subgroup.map_subtype_le _

theorem mem_midPar (r t : ℕ) (q : parab k (two (eSt r t))) :
    (q : GL (Fin (r + t)) k) ∈ midPar k r t ↔ twoBlockParabolicFirstBlock k r t q ∈ parab k (points (Fin r)) := by
  constructor
  · rintro ⟨x, hx, hxq⟩
    obtain rfl : x = q := Subtype.ext hxq
    exact hx
  · intro h
    exact ⟨q, h, rfl⟩

end GlobalTheory.SmGL.PrinProd

namespace GlobalTheory.SmGL.PrinProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : ℕ}

def incl : midPar k r t →* parab k (two (eSt r t)) := Subgroup.inclusion (midPar_le r t)

def fstB : midPar k r t →* parab k (points (Fin r)) :=
  ((twoBlockParabolicFirstBlock k r t).comp incl).codRestrict _ fun q => (mem_midPar r t (incl q)).1 q.2

def rho1 (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :=
  Representation.tprod ((sB ψ₁).comp fstB) ((Stages.tauSnd (eSt r t) (prinSeries ψ₂)).comp incl)

theorem stage_one (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((prod₂ (prinSeries ψ₁) (prinSeries ψ₂)).Equiv (smInd (midPar k r t) (rho1 ψ₁ ψ₂))) :=
  Stages.stage (midPar_le r t) (twoBlockParabolicFirstBlock k r t) ((Stages.sec _).comp (MonoidHom.inl _ _))
    ((Stages.continuous_sec _).comp (Continuous.prodMk_left 1))
    (fun m => congrArg Prod.fst (Stages.pr_sec _ (m, 1))) (mem_midPar r t) SplitFlip.isCompact_KO
    (fun m => MultiIrr.exists_parab_mul (points (Fin r)) m) (sB ψ₁) (Stages.tauSnd _ (prinSeries ψ₂))
    ((((Continuous.prodMk_left 1).tendsto 1).eventually (Stages.dl_sec (eSt r t))).mono fun u hu => by
      refine LinearMap.ext fun v => ?_
      show Stages.tauSnd (eSt r t) (prinSeries ψ₂) (Stages.sec (eSt r t) (u, 1)) v = v
      rw [Stages.tauSnd_apply, hu, Stages.pr_sec]
      simp only [Units.val_one, one_smul, map_one, Module.End.one_apply])
    _ (.refl _ _) (fun q y => Stages.dat_snd _ _ _ q y) (rho1 ψ₁ ψ₂) (.refl _ _) (fun q h z => rfl)

end GlobalTheory.SmGL.PrinProd

namespace GlobalTheory.SmGL.PrinProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : ℕ}

def cB {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) : ℂˣ :=
  deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) * torusChar χ (dg p)

theorem sB_apply {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) (c : ℂ) :
    sB χ p c = (cB χ p : ℂ) * c := by
  show (deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂ) • ((torusChar χ (dg p) : ℂ) * c) = _
  rw [smul_eq_mul, cB, Units.val_mul, mul_assoc]

theorem cB_eq {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) :
    cB χ p = (∏ i : Fin n, absPow k (((n : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) / 2) (dg p i)) * ∏ i, χ i (dg p i) := by
  rw [cB, deltaHalf_apply, torusChar_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [modExp_fin _ (fun _ => by simp)]
  push_cast
  rfl

theorem char_split (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) (x : Fin (r + t) → kˣ) :
    (∏ i : Fin (r + t), absPow k ((((r + t : ℕ) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) / 2) (x i)) *
        ∏ i, Fin.append ψ₁ ψ₂ i (x i) =
      ((∏ j : Fin t, absPow k (((t : ℂ) - 1 - 2 * ((j : ℕ) : ℂ)) / 2) (x (Fin.natAdd r j))) *
          ∏ j, ψ₂ j (x (Fin.natAdd r j))) *
        (absPow k ((t : ℂ) / 2) (∏ i : Fin r, x (Fin.castAdd t i)) *
          absPow k (-(r : ℂ) / 2) (∏ j : Fin t, x (Fin.natAdd r j))) *
        ((∏ i : Fin r, absPow k (((r : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) / 2) (x (Fin.castAdd t i))) *
          ∏ i, ψ₁ i (x (Fin.castAdd t i))) := by
  have h1 : ∀ i : Fin r, absPow k ((((r + t : ℕ) : ℂ) - 1 - 2 * (((Fin.castAdd t i : Fin (r + t)) : ℕ) : ℂ)) / 2)
      (x (Fin.castAdd t i)) = absPow k (((r : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) / 2) (x (Fin.castAdd t i)) *
        absPow k ((t : ℂ) / 2) (x (Fin.castAdd t i)) := fun i => by
    rw [← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    simp only [Fin.coe_castAdd]
    push_cast
    ring
  have h2 : ∀ j : Fin t, absPow k ((((r + t : ℕ) : ℂ) - 1 - 2 * (((Fin.natAdd r j : Fin (r + t)) : ℕ) : ℂ)) / 2)
      (x (Fin.natAdd r j)) = absPow k (((t : ℂ) - 1 - 2 * ((j : ℕ) : ℂ)) / 2) (x (Fin.natAdd r j)) *
        absPow k (-(r : ℂ) / 2) (x (Fin.natAdd r j)) := fun j => by
    rw [← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    simp only [Fin.coe_natAdd]
    push_cast
    ring
  rw [Fin.prod_univ_add, Fin.prod_univ_add, Finset.prod_congr rfl fun i _ => h1 i,
    Finset.prod_congr rfl fun j _ => h2 j, map_prod, map_prod]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_mul_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.SmGL.PrinProd

namespace GlobalTheory.SmGL.PrinProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : ℕ}

theorem eSt_inl (i : Fin r) : eSt r t (.inl i) = Fin.castAdd t i := Fin.ext (by simp [eSt])

theorem eSt_inr (j : Fin t) : eSt r t (.inr j) = Fin.natAdd r j := Fin.ext (by simp [eSt])

def sndB : midPar k r t →* GL (Fin t) k := (MonoidHom.snd _ _).comp ((Stages.pr (eSt r t)).comp incl)

theorem sec_mem (m : GL (Fin t) k) :
    ((Stages.sec (eSt r t) (1, m) : parab k (two (eSt r t))) : GL (Fin (r + t)) k) ∈ midPar k r t :=
  (mem_midPar r t _).2 (by
    show (Stages.pr (eSt r t) (Stages.sec (eSt r t) (1, m))).1 ∈ _
    rw [Stages.pr_sec]; exact one_mem _)

def secS : GL (Fin t) k →* midPar k r t :=
  ((parab k (two (eSt r t))).subtype.comp ((Stages.sec (eSt r t)).comp (MonoidHom.inr _ _))).codRestrict _
    sec_mem

theorem continuous_secS : Continuous (secS (k := k) (r := r) (t := t)) :=
  (continuous_subtype_val.comp ((Stages.continuous_sec _).comp (Continuous.prodMk_right 1))).subtype_mk _

theorem sndB_secS (m : GL (Fin t) k) : sndB (secS (r := r) m) = m :=
  congrArg Prod.snd (Stages.pr_sec (eSt r t) (1, m))

theorem mem_parab_of_borel {g : GL (Fin (r + t)) k} (hg : g ∈ parab k (points (Fin (r + t)))) :
    g ∈ parab k (two (eSt r t)) :=
  (mem_parab_two k).2 fun j i => (mem_borel _).1 hg _ _ (by
    rw [eSt_inl, eSt_inr, Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega)

theorem borel_le_midPar : parab k (points (Fin (r + t))) ≤ midPar k r t := fun g hg =>
  (mem_midPar r t ⟨g, mem_parab_of_borel hg⟩).2 ((mem_borel _).2 fun i j hij => by
    show ((Stages.pr (eSt r t) ⟨g, mem_parab_of_borel hg⟩).1 : Matrix (Fin r) (Fin r) k) i j = 0
    rw [Stages.pr_fst, eSt_inl, eSt_inl]
    exact (mem_borel _).1 hg _ _ (by rw [Fin.lt_def, Fin.coe_castAdd, Fin.coe_castAdd]; exact hij))

theorem mem_borel_iff (q : midPar k r t) :
    (q : GL (Fin (r + t)) k) ∈ parab k (points (Fin (r + t))) ↔ sndB q ∈ parab k (points (Fin t)) := by
  constructor
  · intro h
    refine (mem_borel _).2 fun i j hij => ?_
    show ((Stages.pr (eSt r t) (incl q)).2 : Matrix (Fin t) (Fin t) k) i j = 0
    rw [Stages.pr_snd, eSt_inr, eSt_inr]
    exact (mem_borel _).1 h _ _ (by rw [Fin.lt_def, Fin.coe_natAdd, Fin.coe_natAdd]; have := Fin.lt_def.1 hij; omega)
  · intro h
    have h1 : twoBlockParabolicFirstBlock k r t (incl q) ∈ parab k (points (Fin r)) := (mem_midPar r t (incl q)).1 q.2
    refine (mem_borel _).2 fun a b hab => ?_
    obtain ⟨a | a, rfl⟩ := (eSt r t).surjective a <;> obtain ⟨b | b, rfl⟩ := (eSt r t).surjective b
    · have := (mem_borel _).1 h1 a b (by rw [eSt_inl, eSt_inl, Fin.lt_def, Fin.coe_castAdd, Fin.coe_castAdd] at hab; exact Fin.lt_def.2 hab)
      rwa [twoBlockParabolicFirstBlock, MonoidHom.comp_apply, MonoidHom.coe_fst, Stages.pr_fst] at this
    · exfalso
      rw [eSt_inl, eSt_inr, Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at hab
      omega
    · exact (mem_parab_two k).1 (incl q).2 a b
    · have := (mem_borel _).1 h a b (by rw [eSt_inr, eSt_inr, Fin.lt_def, Fin.coe_natAdd, Fin.coe_natAdd] at hab; exact Fin.lt_def.2 (by omega))
      rwa [sndB, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.coe_snd, Stages.pr_snd] at this

theorem dg_fstB (q : midPar k r t) (h : (q : GL (Fin (r + t)) k) ∈ parab k (points (Fin (r + t)))) (i : Fin r) :
    dg (fstB q) i = dg (⟨q, h⟩ : parab k (points (Fin (r + t)))) (Fin.castAdd t i) := Units.ext (by
  rw [val_dg, val_dg]
  show ((Stages.pr (eSt r t) (incl q)).1 : Matrix (Fin r) (Fin r) k) i i = _
  rw [Stages.pr_fst, eSt_inl]
  rfl)

theorem dg_sndB (q : midPar k r t) (h : (q : GL (Fin (r + t)) k) ∈ parab k (points (Fin (r + t))))
    (hs : sndB q ∈ parab k (points (Fin t))) (j : Fin t) :
    dg (⟨sndB q, hs⟩ : parab k (points (Fin t))) j =
      dg (⟨q, h⟩ : parab k (points (Fin (r + t)))) (Fin.natAdd r j) := Units.ext (by
  rw [val_dg, val_dg]
  show ((Stages.pr (eSt r t) (incl q)).2 : Matrix (Fin t) (Fin t) k) j j = _
  rw [Stages.pr_snd, eSt_inr]
  rfl)

theorem cB_split (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) (q : midPar k r t)
    (h : (q : GL (Fin (r + t)) k) ∈ parab k (points (Fin (r + t)))) (hs : sndB q ∈ parab k (points (Fin t))) :
    cB (Fin.append ψ₁ ψ₂) ⟨q, h⟩ = cB ψ₂ ⟨sndB q, hs⟩ * Stages.dl (eSt r t) (incl q) * cB ψ₁ (fstB q) := by
  have d1 : Matrix.GeneralLinearGroup.det (Stages.pr (eSt r t) (incl q)).1 = ∏ i, dg (fstB q) i :=
    det_parab k (points (Fin r)) (fstB q)
  have d2 : Matrix.GeneralLinearGroup.det (Stages.pr (eSt r t) (incl q)).2 = ∏ j, dg (⟨sndB q, hs⟩ : parab k (points (Fin t))) j :=
    det_parab k (points (Fin t)) ⟨sndB q, hs⟩
  rw [cB_eq, cB_eq, cB_eq, Stages.dl_apply, d1, d2, Fintype.card_fin, Fintype.card_fin]
  simp only [dg_fstB q h, dg_sndB q h hs]
  exact char_split ψ₁ ψ₂ _

def tau2 (ψ₁ : Fin r → kˣ →* ℂˣ) : Representation ℂ (midPar k r t) ℂ :=
  twist ((sB ψ₁).comp fstB) ((Stages.dl (eSt r t)).comp incl)

theorem stage_two (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((smInd (midPar k r t) (rho1 ψ₁ ψ₂)).Equiv (prinSeries (Fin.append ψ₁ ψ₂))) :=
  Stages.stage borel_le_midPar sndB secS continuous_secS sndB_secS mem_borel_iff SplitFlip.isCompact_KO
    (fun m => MultiIrr.exists_parab_mul (points (Fin t)) m) (sB ψ₂) (tau2 ψ₁)
    ((((Continuous.prodMk_right 1).tendsto 1).eventually (Stages.dl_sec (eSt r t))).mono fun u hu => by
      refine LinearMap.ext fun v => ?_
      have h1 : fstB (secS (r := r) u) = 1 :=
        Subtype.ext (congrArg Prod.fst (Stages.pr_sec (eSt r t) (1, u)))
      show ((Stages.dl (eSt r t) (Stages.sec (eSt r t) (1, u)) : ℂˣ) : ℂ) • (sB ψ₁) (fstB (secS u)) v = v
      rw [h1, hu, map_one]
      simp only [Units.val_one, one_smul, Module.End.one_apply])
    (rho1 ψ₁ ψ₂) (TensorProduct.comm _ _ _) (fun q y => by
      induction y with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a f =>
        show TensorProduct.comm ℂ _ _ ((sB ψ₁ (fstB q) a) ⊗ₜ (Stages.tauSnd (eSt r t) (prinSeries ψ₂) (incl q) f)) = _
        rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.map_tmul, Stages.tauSnd_apply]
        exact TensorProduct.smul_tmul _ _ _)
    (sB (Fin.append ψ₁ ψ₂)) (TensorProduct.lid ℂ ℂ) (fun q h z => by
      induction z with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b =>
        rw [TensorProduct.lid_tmul, TensorProduct.map_tmul, TensorProduct.lid_tmul]
        show sB (Fin.append ψ₁ ψ₂) ⟨q, h⟩ (a • b) =
          sB ψ₂ ⟨sndB q, (mem_borel_iff q).1 h⟩ a • ((Stages.dl (eSt r t) (incl q) : ℂˣ) : ℂ) • sB ψ₁ (fstB q) b
        rw [sB_apply, sB_apply, sB_apply, cB_split ψ₁ ψ₂ q h ((mem_borel_iff q).1 h)]
        simp only [smul_eq_mul, Units.val_mul]
        ring)

end GlobalTheory.SmGL.PrinProd

namespace GlobalTheory.SmGL.PrinProd

theorem prinSeries_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), Nonempty (A.Equiv (prinSeries ψ₁)) → Nonempty (B.Equiv (prinSeries ψ₂)) → IsSubquotient (prinSeries (Fin.append ψ₁ ψ₂)) (prod₂ A B) := by
  intro k _ _ _ _ r t ψ₁ ψ₂ V _ _ W _ _ A B ⟨φA⟩ ⟨φB⟩
  obtain ⟨E1⟩ := stage_one (k := k) ψ₁ ψ₂
  obtain ⟨E2⟩ := stage_two (k := k) ψ₁ ψ₂
  let E := (GlobalTheory.LocGL.prod₂Equiv φA φB).trans (E1.trans E2)
  exact IsSubquotient.of_injective E.symm.toIntertwiningMap E.symm.toLinearEquiv.injective

end GlobalTheory.SmGL.PrinProd
