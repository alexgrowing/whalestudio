import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def IsOBas (Z : Fin n → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∀ x, x ∈ latLoc (E := E) v Λ ↔
    ∃ c : Fin n → Fv F v ⊗[F] E, (∀ i, c i ∈ OEv (E := E) v) ∧ x = ∑ i, c i • Z i

def eSp {a : ℕ} (h : a ≤ n) : Fin a ⊕ Fin (n - a) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

def gT {a : ℕ} (h : a ≤ n) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  Matrix.reindex (eSp h) (eSp h) (Matrix.fromBlocks T 0 0 1)

def ExtOrth (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodY σ J ψ v Λ a Y → ∀ X ∈ LamT v Λ a,
    gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = gT v h (gramR (Fv F v) σ J Y)

def colM (Z : Fin n → Fin n → Fv F v ⊗[F] E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  fun i p => Z p i

theorem gram_eq_colM (Z : Fin n → Fin n → Fv F v ⊗[F] E) :
    gramR (Fv F v) σ J Z = cT (sigR (Fv F v) σ) (colM v Z) * JR (Fv F v) J * colM v Z := by
  ext p q
  simp only [gramR, hR, hform, cT, colM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_eq_colM (Z : Fin n → Fin n → Fv F v ⊗[F] E) (c : Fin n → Fv F v ⊗[F] E) :
    ∑ i, c i • Z i = colM v Z *ᵥ c := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colM, mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem col_eq_colM (Z : Fin n → Fin n → Fv F v ⊗[F] E) (p : Fin n) :
    Z p = colM v Z *ᵥ Pi.single p 1 := by
  rw [mulVec_single_one]
  rfl

theorem det_gT {a : ℕ} (h : a ≤ n) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    (gT v h T).det = T.det := by
  rw [gT, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem isUnit_det_colM {a : ℕ} (h : a ≤ n) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : IsUnit T.det)
    (Z : Fin n → Fin n → Fv F v ⊗[F] E) (hZ : gramR (Fv F v) σ J Z = gT v h T) : IsUnit (colM v Z).det := by
  have h1 := congrArg Matrix.det hZ
  rw [gram_eq_colM, det_gT, det_mul, det_mul] at h1
  rw [← h1] at hT
  exact isUnit_of_mul_isUnit_right hT

theorem orbAll_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtOrth σ J ψ v Λ a Y) :
    OrbAll σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  have hYL : Y ∈ LamT v Λ a := hG.2.2.2.2.2.1.1
  obtain ⟨w, -, -, hw⟩ := hG.2.2.2.2.2.2
  have hT : IsUnit (gramR (Fv F v) σ J Y).det := ⟨⟨_, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  obtain ⟨ZX, hbX, heX, hgX⟩ := hE h hG X hX hXY
  obtain ⟨ZY, hbY, heY, hgY⟩ := hE h hG Y hYL rfl
  have hdX := isUnit_det_colM σ J v h _ hT ZX hgX
  have hdY := isUnit_det_colM σ J v h _ hT ZY hgY
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end Glue

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PerpL {a : ℕ} (X : TupV (E := E) v n a) : Set (Fin n → Fv F v ⊗[F] E) :=
  {w | w ∈ latLoc (E := E) v Λ ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0}

def OrthoB (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ _ : a ≤ n, GoodY σ J ψ v Λ a Y → ∀ X ∈ LamT v Λ a,
    gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ e : Fin (n - a) → Fin n → Fv F v ⊗[F] E, (∀ j, e j ∈ PerpL σ J v Λ X) ∧
      (∀ i j, hR (Fv F v) σ J (e j) (X i) = 0) ∧ gramR (Fv F v) σ J e = 1 ∧
      ∀ w ∈ PerpL σ J v Λ X, ∃ d : Fin (n - a) → Fv F v ⊗[F] E, (∀ j, d j ∈ OEv (E := E) v) ∧
        w = ∑ j, d j • e j

def OSub : Prop :=
  (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v ∧ ∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x * y ∈ OEv (E := E) v

def OSmul : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ c ∈ OEv (E := E) v, ∀ x ∈ latLoc (E := E) v Λ, c • x ∈ latLoc (E := E) v Λ

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v := Submodule.neg_mem _ hx

def oRing (hS : OSub (E := E) v) : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := fun hx hy => hS.2 _ hx _ hy
  one_mem' := hS.1
  add_mem' := fun hx hy => oev_add v hx hy
  zero_mem' := oev_zero v
  neg_mem' := fun hx => oev_neg v hx

theorem hR_sum_right {a : ℕ} (x : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (y : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ k, c k • y k) = ∑ k, c k * hR (Fv F v) σ J x (y k) := by
  simp only [hR, hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hR_sub_right (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y - z) = hR (Fv F v) σ J x y - hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem adj_mem (hS : OSub (E := E) v) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OEv (E := E) v) (i j : Fin a) : T.adjugate i j ∈ OEv (E := E) v := by
  let T' : Matrix (Fin a) (Fin a) (oRing v hS) := fun i j => ⟨T i j, hT i j⟩
  have h2 : ((oRing v hS).subtype.mapMatrix T').adjugate i j = (oRing v hS).subtype (T'.adjugate i j) := by
    rw [← RingHom.map_adjugate]; rfl
  have h3 : (oRing v hS).subtype.mapMatrix T' = T := rfl
  rw [← h3, h2]
  exact (T'.adjugate i j).2

theorem split (hS : OSub (E := E) v)
    (hM : ∀ c ∈ OEv (E := E) v, ∀ y ∈ latLoc (E := E) v Λ, c • y ∈ latLoc (E := E) v Λ)
    (hsd : IsSDLoc σ J v Λ) {a : ℕ} (X : TupV (E := E) v n a)
    (hX : X ∈ LamT v Λ a) (w : Fv F v ⊗[F] E) (hw0 : w ∈ OEv (E := E) v)
    (hw : (gramR (Fv F v) σ J X).det * w = 1) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    ∃ c : Fin a → Fv F v ⊗[F] E, (∀ i, c i ∈ OEv (E := E) v) ∧
      x - ∑ k, c k • X k ∈ PerpL σ J v Λ X := by
  set T := gramR (Fv F v) σ J X with hTdef
  have hTO : ∀ i j, T i j ∈ OEv (E := E) v := fun i j => (hsd (X j)).1 (hX j) (X i) (hX i)
  let b : Fin a → Fv F v ⊗[F] E := fun j => hR (Fv F v) σ J (X j) x
  have hbO : ∀ j, b j ∈ OEv (E := E) v := fun j => (hsd x).1 hx (X j) (hX j)
  let c : Fin a → Fv F v ⊗[F] E := w • (T.adjugate *ᵥ b)
  have hcO : ∀ k, c k ∈ OEv (E := E) v := by
    intro k
    show w * ∑ j, T.adjugate k j * b j ∈ OEv (E := E) v
    refine hS.2 _ hw0 _ ?_
    exact Submodule.sum_mem _ fun j _ => hS.2 _ (adj_mem v hS T hTO k j) _ (hbO j)
  have hTc : T *ᵥ c = b := by
    show T *ᵥ (w • (T.adjugate *ᵥ b)) = b
    rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, smul_smul, mul_comm, hw, one_smul]
  refine ⟨c, hcO, ?_, ?_⟩
  · exact Submodule.sub_mem _ hx (Submodule.sum_mem _ fun k _ => hM _ (hcO k) _ (hX k))
  · intro i
    rw [hR_sub_right, hR_sum_right]
    have h1 : ∑ k, c k * hR (Fv F v) σ J (X i) (X k) = (T *ᵥ c) i := by
      simp only [mulVec, dotProduct, hTdef, gramR]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [h1, hTc]
    exact sub_self _

theorem extOrth_of (a : ℕ) (Y : TupV (E := E) v n a) (hS : OSub (E := E) v) (hM : OSmul v Λ)
    (hO : OrthoB σ J ψ v Λ a Y) : ExtOrth σ J ψ v Λ a Y := by
  intro h hG X hX hXY
  obtain ⟨e, hePerp, heX, hee, hspan⟩ := hO h hG X hX hXY
  have hM' := hM hG.2.1
  have hsd : IsSDLoc σ J v Λ := hG.2.2.1
  obtain ⟨w, hw0, -, hw⟩ := hG.2.2.2.2.2.2
  rw [← hXY] at hw
  let Z : Fin n → Fin n → Fv F v ⊗[F] E := fun p => Sum.elim X e ((eSp h).symm p)
  have hsum : ∀ c : Fin n → Fv F v ⊗[F] E, ∑ p, c p • Z p =
      ∑ i, c (eSp h (Sum.inl i)) • X i + ∑ j, c (eSp h (Sum.inr j)) • e j := by
    intro c
    rw [← (eSp h).sum_comp, Fintype.sum_sum_type]
    simp [Z]
  refine ⟨Z, ?_, fun i => by simp [Z], ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨c, hcO, hperp⟩ := split σ J v Λ hS hM' hsd X hX w hw0 hw x hx
      obtain ⟨d, hdO, hd⟩ := hspan _ hperp
      refine ⟨fun p => Sum.elim c d ((eSp h).symm p), fun p => ?_, ?_⟩
      · show Sum.elim c d ((eSp h).symm p) ∈ OEv (E := E) v
        generalize (eSp h).symm p = s
        rcases s with i | j
        · exact hcO i
        · exact hdO j
      · rw [hsum]
        simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
        rw [← hd]
        abel
    · rintro ⟨c, hcO, rfl⟩
      refine Submodule.sum_mem _ fun p _ => hM' _ (hcO p) _ ?_
      show Sum.elim X e ((eSp h).symm p) ∈ latLoc (E := E) v Λ
      generalize (eSp h).symm p = s
      rcases s with i | j
      · exact hX i
      · exact (hePerp j).1
  · ext p q
    show hR (Fv F v) σ J (Sum.elim X e ((eSp h).symm p)) (Sum.elim X e ((eSp h).symm q)) =
      Matrix.fromBlocks (gramR (Fv F v) σ J Y) 0 0 1 ((eSp h).symm p) ((eSp h).symm q)
    generalize (eSp h).symm p = s
    generalize (eSp h).symm q = t
    rcases s with i | i <;> rcases t with j | j
    · simp only [Sum.elim_inl, fromBlocks_apply₁₁, ← hXY]
      rfl
    · simp only [Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂]
      exact (hePerp j).2 i
    · simp only [Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁]
      exact heX j i
    · simp only [Sum.elim_inr, fromBlocks_apply₂₂]
      exact congrFun (congrFun hee i) j

theorem orbAll_of_orthoB (a : ℕ) (Y : TupV (E := E) v n a) (hS : OSub (E := E) v) (hM : OSmul v Λ)
    (hO : OrthoB σ J ψ v Λ a Y) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of σ J ψ v Λ a Y (extOrth_of σ J ψ v Λ a Y hS hM hO)

end Ext

end PI.OmLocU.Orb
