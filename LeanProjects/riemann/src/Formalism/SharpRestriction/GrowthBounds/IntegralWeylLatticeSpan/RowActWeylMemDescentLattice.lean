import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescent
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylEqSpanInt
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.EvenBlockRowActionEval

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem int_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    φ.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _

theorem lamStar_anti {m : ℕ} (lam : Fin (m + 1) → ℤ) (hd : Antitone lam) : Antitone (lamStar lam) := by
  intro i j hij
  simp only [lamStar, neg_le_neg_iff]
  exact hd (Fin.rev_le_rev.2 hij)

theorem lamAt_odd {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : ¬ Even s.val) :
    lamAt lam0 s = lamStar (lam0 s) := by
  unfold lamAt; rw [if_neg hs]; rfl

theorem lamAt_even {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : Even s.val) :
    lamAt lam0 s = lam0 s := by
  unfold lamAt; rw [if_pos hs]

theorem lamAt_anti {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (s : Fin n') :
    Antitone (lamAt lam0 s) := by
  by_cases hs : Even s.val
  · rw [lamAt_even lam0 s hs]; exact hd s
  · rw [lamAt_odd lam0 s hs]; exact lamStar_anti _ (hd s)

theorem rowAct_weyl_mem_span_integral {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (a : Kf) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O)
    (hf : f ∈ weyl O (m + 1) (m + 1) le_rfl ν) :
    a • rowAct Kf g (map (algebraMap O Kf) f) ∈ Submodule.span O
      ((fun f0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ => a • rowAct Kf g (map (Int.castRingHom Kf) f0)) ''
        (weyl ℤ (m + 1) (m + 1) le_rfl ν : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ))) := by
  rw [weyl_eq_span_int] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f0, hf0, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨f0, hf0, ?_⟩
    show _ = a • rowAct Kf g (map (algebraMap O Kf) (map (Int.castRingHom O) f0))
    rw [MvPolynomial.map_map, int_comp]
  | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add, smul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : map (algebraMap O Kf) (c • x) = algebraMap O Kf c • map (algebraMap O Kf) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    rw [e1, map_smul, smul_comm, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem rowAct_weyl_mem_descentLattice {O K : Type} [CommRing O] [Field K] [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O) (hf : f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam)) :
    (g.det ^ (-(lam (Fin.last m)))) • rowAct K g⁻¹ (map (algebraMap O K) f) ∈ Dl0 O m lam (colSpan O g) := by
  rw [dw_eq hinj m lam hlam g hg]
  refine ⟨rowAct K g⁻¹ (map (algebraMap O K) f), ⟨f, hf, ?_⟩, rfl⟩
  change map (algebraMap O K) f = rowAct K g (rowAct K g⁻¹ (map (algebraMap O K) f))
  rw [rowAct_cancel g g⁻¹ (Matrix.nonsing_inv_mul g hg)]

theorem descentLattice_eq_span_weyl {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) = Submodule.span O
      ((fun f0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ =>
          (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf g⁻¹ (map (Int.castRingHom Kf) f0)) ''
        (weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ))) := by
  apply le_antisymm
  · rw [dw_eq hinj m lam hlam g hg]
    rintro _ ⟨F0, ⟨f, hf, hfe⟩, rfl⟩
    have hfe' : map (algebraMap O Kf) f = rowAct Kf g F0 := hfe
    have hF0 : F0 = rowAct Kf g⁻¹ (map (algebraMap O Kf) f) := by
      rw [hfe', rowAct_cancel g⁻¹ g (Matrix.mul_nonsing_inv g hg)]
    show g.det ^ (-(lam (Fin.last m))) • F0 ∈ _
    rw [hF0]
    exact rowAct_weyl_mem_span_integral m _ g⁻¹ _ f hf
  · rw [Submodule.span_le]
    rintro _ ⟨f0, hf0, rfl⟩
    have h1 := rowAct_weyl_mem_descentLattice hinj m lam hlam g hg (map (Int.castRingHom O) f0) (map_mem_weyl le_rfl _ f0 hf0)
    rw [MvPolynomial.map_map, int_comp] at h1
    exact h1

theorem sub_rfl {k : ℕ} {R : Type} (h : k = k) (A : Matrix (Fin k) (Fin k) R) :
    A.submatrix (finCongr h) (finCongr h) = A := by
  ext i j; rfl

theorem gl_map_det {k : ℕ} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (A : GL (Fin k) R) :
    IsUnit ((A : Matrix (Fin k) (Fin k) R).map φ).det := by
  have h1 : ((A : Matrix (Fin k) (Fin k) R).map φ).det = φ (A : Matrix (Fin k) (Fin k) R).det :=
    (RingHom.map_det φ _).symm
  rw [h1]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).map φ

section Blocks

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]
  (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (N : Tau → GL (Fin n) LL)

def niAt (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL :=
  if Even s.val then (((N (pos ⟨v, s⟩))⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).submatrix (finCongr h) (finCongr h)
  else (N (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr h) (finCongr h)

theorem niAt_mul_nAt (v : Fin P.nV) (s : Fin (P.n' v)) : niAt P h pos N v s * nAt P h pos N v s = 1 := by
  unfold niAt nAt
  split_ifs
  · rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.submatrix_one_equiv]

theorem niAt_map_mul {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    (niAt P h pos N v s).map φ * (nAt P h pos N v s).map φ = 1 := by
  rw [← Matrix.map_mul, niAt_mul_nAt, Matrix.map_one φ φ.map_zero φ.map_one]

theorem nAt_map_inv {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((nAt P h pos N v s).map φ)⁻¹ = (niAt P h pos N v s).map φ :=
  Matrix.inv_eq_left_inv (niAt_map_mul P h pos N φ v s)

theorem nAt_map_det {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v)) :
    IsUnit ((nAt P h pos N v s).map φ).det :=
  Matrix.isUnit_det_of_left_inverse (niAt_map_mul P h pos N φ v s)

def bl (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) LL :=
  ((nAt P h pos N v s).det ^ (-(eAt P v s))) • rowAct LL (niAt P h pos N v s) (map (Int.castRingHom LL) f)

theorem map_bl {R : Type} [Field R] (φ : LL →+* R) (v : Fin P.nV) (s : Fin (P.n' v))
    (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map φ (bl P h pos N v s f) = (((nAt P h pos N v s).map φ).det ^ (-(eAt P v s))) •
      rowAct R ((nAt P h pos N v s).map φ)⁻¹ (map (Int.castRingHom R) f) := by
  unfold bl
  rw [Cmp.map_smul', map_rowAct, MvPolynomial.map_map, int_comp, map_zpow₀, nAt_map_inv, RingHom.map_det]
  rfl

def gen (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) : XR P LL :=
  ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb LL s (bl P h pos N v s (f v s)))

def genSet : Set (XR P LL) :=
  {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧ X = gen P h pos N f}

theorem map_gen {R : Type} [Field R] (φ : LL →+* R)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map φ (gen P h pos N f) =
      ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb R s (map φ (bl P h pos N v s (f v s)))) := by
  unfold gen
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [MvPolynomial.map_rename, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  exact MvPolynomial.map_rename _ _ _

theorem htupW_eq (hinj : Function.Injective (algebraMap O Kf)) (e : LL →+* Kf) (L : P.Tup)
    (HL : ∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e)) :
    P.HtupW L = Submodule.span O ((fun q => map e q) '' genSet P h pos N) := by
  classical
  let Tb : ∀ v, ∀ _ : Fin (P.n' v), Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) := fun v s =>
    (fun f0 => map e (bl P h pos N v s f0)) ''
      (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) : Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hD : ∀ v (s : Fin (P.n' v)), Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v)) =
      Submodule.span O (Tb v s) := by
    intro v s
    rw [HL v s, descentLattice_eq_span_weyl hinj P.m _ (lamAt_anti _ (P.dom v) s) _ (nAt_map_det P h pos N e v s)]
    congr 1
    apply Set.image_congr
    intro f0 _
    exact (map_bl P h pos N e v s f0).symm
  let Tv : ∀ v, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf) := fun v =>
    {X | ∃ F : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
      (∀ s, F s ∈ Tb v s) ∧ X = ∏ s, blockEmb Kf s (F s)}
  have hs : ∀ v, HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) = Submodule.span O (Tv v) := by
    intro v
    unfold HtenW tensorLat
    simp only [hD]
    exact prodSpan (O := O) (A := MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
      (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
      (fun s => (blockEmb Kf s).toLinearMap.restrictScalars O) (Tb v)
  unfold Places.HtupW Places.tenV
  simp only [hs]
  refine (prodSpan (O := O) (A := P.Xsp)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
    (fun v => (P.vEmb v).toLinearMap.restrictScalars O) Tv).trans ?_
  congr 1
  ext X
  constructor
  · rintro ⟨F, hF, rfl⟩
    choose F' hF' hFe using hF
    choose f hf hfe using hF'
    refine ⟨gen P h pos N f, ⟨f, hf, rfl⟩, ?_⟩
    show map e (gen P h pos N f) = _
    rw [map_gen]
    refine Finset.prod_congr rfl fun v _ => ?_
    show _ = P.vEmb v (F v)
    rw [hFe v]
    have e2 : ∀ s, map e (bl P h pos N v s (f v s)) = F' v s := fun s => hfe v s
    simp only [e2]
    rfl
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨fun v => ∏ s, blockEmb Kf s (map e (bl P h pos N v s (f v s))),
      fun v => ⟨fun s => map e (bl P h pos N v s (f v s)), fun s => ⟨f v s, hf v s, rfl⟩, rfl⟩,
      map_gen P h pos N e f⟩

theorem mem_htupW_iff (hD : DescVal) (hfr : IsFractionRing O Kf) (e : LL →+* Kf) (R0 : Subring LL)
    (hR0 : ∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) (L : P.Tup)
    (HL : ∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e))
    (Q : XR P LL) : map e Q ∈ P.HtupW L ↔ Q ∈ Submodule.span R0 (genSet P h pos N) := by
  rw [htupW_eq P h pos N (IsFractionRing.injective O Kf) e L HL]
  constructor
  · exact hD e R0 hR0 _ Q
  · intro hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨o, ho⟩ := (hR0 r.1).1 r.2
      have e1 : map e (r • x) = o • map e x := by
        rw [Subring.smul_def, Cmp.map_smul', ← ho, algebraMap_smul]
      rw [e1]; exact Submodule.smul_mem _ o hx

end Blocks

end Formalism.L2.G.RelativeIndexFlags.Core
