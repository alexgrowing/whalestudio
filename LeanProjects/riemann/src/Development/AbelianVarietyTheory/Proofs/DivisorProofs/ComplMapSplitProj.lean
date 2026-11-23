import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

def blkId (hld : l + d ≤ n) : Matrix (Fin n) (Fin d) R :=
  fun i j => if i.val = l + j.val then 1 else 0

theorem blkId_map {S : Type} [CommRing S] (f : R →+* S) (hld : l + d ≤ n) : (blkId R hld).map f = blkId S hld := by
  ext i j
  simp [blkId, apply_ite f]

theorem tripPlace_val (hld : l + d ≤ n) (a : Fin 3) (i : Fin (tripSizes l d n a)) :
    (tripPlace hld ⟨a, i⟩).val = ![0, l, l + d] a + i.val := by
  simp only [tripPlace, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  congr 1
  fin_cases a <;> simp [tripSizes, Fin.sum_univ_succ]

theorem blkId_ne (hld : l + d ≤ n) (a : Fin 3) (ha : a ≠ 1) (i : Fin (tripSizes l d n a)) (j : Fin d) :
    blkId R hld (tripPlace hld ⟨a, i⟩) j = 0 := by
  have hi := i.2
  have hj := j.2
  rw [blkId, if_neg]
  rw [tripPlace_val]
  fin_cases a
  · simp [tripSizes] at hi ⊢; omega
  · exact absurd rfl ha
  · simp; omega

theorem blkId_one (hld : l + d ≤ n) (i : Fin d) (j : Fin d) :
    blkId R hld (tripPlace hld ⟨1, i⟩) j = if i = j then 1 else 0 := by
  have e : (tripPlace hld ⟨1, i⟩).val = l + i.val := tripPlace_val hld 1 i
  rw [blkId, e]
  simp [Fin.ext_iff]

theorem blkId_mid (hld : l + d ≤ n) (A : Matrix (Fin d) (Fin d) R) (i j : Fin d) (a b : Fin n)
    (ha : ∀ k, blkId R hld a k = if i = k then 1 else 0) (hb : ∀ k, blkId R hld b k = if j = k then 1 else 0) :
    (blkId R hld * A * (blkId R hld)ᵀ) a b = A i j := by
  simp [Matrix.mul_apply, ha, hb]

theorem leviEmb_midHom (hld : l + d ≤ n) (g : GL (Fin d) R) :
    (GlobalTheory.SmGL.leviEmb R (tripPlace hld) (midHom R l d n g)).1 = 1 + blkId R hld * (g.1 - 1) * (blkId R hld)ᵀ := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (tripPlace hld).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (tripPlace hld).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases ha : a = 1
    · subst ha
      have e : midHom R l d n g 1 = g :=
        Pi.mulSingle_eq_same (M := fun j : Fin 3 => GL (Fin (tripSizes l d n j)) R) 1 g
      rw [e, Matrix.add_apply, blkId_mid R hld _ i j _ _ (blkId_one R hld i) (blkId_one R hld j)]
      have e2 : (1 : Matrix (Fin n) (Fin n) R) (tripPlace hld ⟨1, i⟩) (tripPlace hld ⟨1, j⟩) =
          (1 : Matrix (Fin (tripSizes l d n 1)) (Fin (tripSizes l d n 1)) R) i j := by
        simp [Matrix.one_apply]
      rw [e2]
      exact (add_sub_cancel _ _).symm
    · have e : midHom R l d n g a = 1 := Pi.mulSingle_eq_of_ne ha _
      rw [e]
      simp [Matrix.mul_apply, blkId_ne R hld a ha, Matrix.one_apply]
  · rw [leviEmb_apply_ne _ _ _ hab]
    have h1 : (1 : Matrix (Fin n) (Fin n) R) (tripPlace hld ⟨a, i⟩) (tripPlace hld ⟨b, j⟩) = 0 :=
      Matrix.one_apply_ne fun e => hab (congrArg Sigma.fst ((tripPlace hld).injective e))
    rw [Matrix.add_apply, h1, zero_add]
    by_cases ha : a = 1
    · have hb : b ≠ 1 := fun e => hab (ha.trans e.symm)
      simp [Matrix.mul_apply, blkId_ne R hld b hb]
    · simp [Matrix.mul_apply, blkId_ne R hld a ha]

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

theorem conj_leviEmb (hld : l + d ≤ n) (B : GL (Fin n) R) (g : GL (Fin d) R) {X : Matrix (Fin n) (Fin d) R}
    {Y' : Matrix (Fin d) (Fin n) R} (h1 : B.1 * blkId R hld = X) (h2 : Y' * B.1 = (blkId R hld)ᵀ) :
    1 + X * (g.1 - 1) * Y' = (B * GlobalTheory.SmGL.leviEmb R (tripPlace hld) (midHom R l d n g) * B⁻¹).1 := by
  have h3 : Y' = (blkId R hld)ᵀ * (B⁻¹).1 := by rw [← h2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, leviEmb_midHom, h3, ← h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv]
  simp only [Matrix.mul_assoc]

end Lin

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
  {C : GL (Fin n) E} {l d : ℕ}

theorem yx_eq_one (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  ext i j
  have h := congrArg σ (congrFun₂ hW.xy j i)
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, RingHom.coe_coe,
    cm_conj_conj hσ, hJ.1, Matrix.one_apply, apply_ite σ, map_one, map_zero, Finset.sum_mul] at h ⊢
  rw [Finset.sum_comm, if_congr eq_comm rfl rfl, ← h]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [NumberField F] [NumberField E] in
theorem mul_blkId (hC : IsAdapted σ J X Y C) (h : l + d ≤ r) (hld : l + d ≤ n) :
    C.1 * blkId E hld = blkCols h X := by
  ext k j
  have hj := j.2
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l + j.val, by omega⟩ : Fin n)]
  · simp only [blkId, if_true, mul_one]
    exact hC.colX _ _ rfl k
  · intro b _ hb
    rw [blkId, if_neg fun e => hb (Fin.ext e), mul_zero]
  · simp

theorem dual_mul (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (hC : IsAdapted σ J X Y C)
    (h : l + d ≤ r) (hld : l + d ≤ n) :
    cT (σ : E →+* E) (blkCols h Y) * J * C.1 = (blkId E hld)ᵀ := by
  ext j i
  have hj := j.2
  have hi := i.2
  have hr := hC.le
  have e : (cT (σ : E →+* E) (blkCols h Y) * J * C.1) j i =
      ((cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i)) ⟨l + j.val, by omega⟩ := rfl
  rw [e, Matrix.transpose_apply, blkId]
  by_cases h1 : i.val < r
  · have e1 : (fun k => C.1 k i) = fun k => X k ⟨i.val, h1⟩ := funext (hC.colX _ _ rfl)
    rw [e1]
    refine (congrFun₂ (yx_eq_one hσ hJ hW) ⟨l + j.val, by omega⟩ ⟨i.val, h1⟩).trans ?_
    simp [Matrix.one_apply, eq_comm]
  · rw [if_neg (by omega)]
    by_cases h2 : i.val + r < n
    · rw [hC.perpY i (by omega) h2]; rfl
    · have e1 : (fun k => C.1 k i) = fun k => Y k ⟨n - 1 - i.val, by omega⟩ :=
        funext (hC.columnBlock _ _ (by simp; omega))
      rw [e1]
      exact congrFun₂ hW.yy ⟨l + j.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩

end Frame

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in
theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    infTens F E (sigR _ σ z) = sigR _ σ (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem toCompl_compFin {u : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = u)
    (z : AF F ⊗[F] E) : toCompl h (compFin F E u z) = pLoc E w (finAdEquiv F E (finTens F E z)) := by
  rw [compFin_eq, ← finAdEquiv_apply]; rfl

theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2

omit [Algebra F E] [NumberField F] [Field F] in
theorem pFin_finGL {d : ℕ} (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) : pFin E ((finGL E d k).1 a b) = k.1 a b :=
  gl_entry (map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun _ => rfl) k) a b

omit [Algebra F E] [NumberField F] [Field F] in
theorem fst_finGL {d : ℕ} (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    RingHom.fst (InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E) ((finGL E d k).1 a b) =
      (1 : Matrix (Fin d) (Fin d) (InfiniteAdeleRing E)) a b :=
  gl_entry ((map_cornerGL_of_zero (S := Ad E) (sFin E)
    (RingHom.fst (InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) (fun _ => rfl) k)) a b

variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

theorem map_infTens (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) : ((finGL E d k).1.map Φ.symm).map (infTens F E) = 1 := by
  refine Matrix.ext fun a b => ?_
  refine j.injective (((congrArg Prod.fst (hΦ (Φ.symm _))).symm.trans
    (congrArg Prod.fst (Φ.apply_symm_apply _))).trans ((fst_finGL k a b).trans ?_))
  simp [Matrix.one_apply, apply_ite j]

theorem map_compFin_ne {u : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hu : w.under (𝓞 F) ≠ u)
    (k : GL (Fin d) (w.adicCompletion E)) :
    ((finGL E d (locGL E d w k)).1.map Φ.symm).map (compFin F E u) = 1 := by
  refine Matrix.ext fun a b => ?_
  have h1 := compFin_eq_zero u (Φ.symm ((finGL E d (locGL E d w k)).1 a b) - (1 : Matrix (Fin d) (Fin d) _) a b)
    fun w' hw' => by
      have hne : w' ≠ w := fun e => hu (e ▸ hw')
      have h2 : pLoc E w' ((locGL E d w k).1 a b) = (1 : Matrix (Fin d) (Fin d) _) a b :=
        gl_entry (pLoc_locGL_of_ne hne k) a b
      rw [map_sub, map_sub, map_sub, fin_symm hΦ, pFin_finGL, h2, sub_eq_zero]
      by_cases e : a = b
      · subst e; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne e, map_zero]
  rw [map_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  by_cases e : a = b
  · subst e; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne e, map_zero]

theorem complMap_splitProj {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E))
    (a b : Fin d) : complMap (splitPrime_under t) (splitProj t (compFin F E v (Φ.symm ((finGL E d k).1 a b)))) =
      pLoc E (splitPrime t) (k.1 a b) := by
  rw [← toCompl_eq_complMap, toCompl_compFin, fin_symm hΦ, pFin_finGL]

theorem map_split_self {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) (g : GL (Fin d) (Fv F v)) :
    ((finGL E d (locGL E d (splitPrime t) (glEquiv d (complEquiv t (splitPrime_under t)) g))).1.map Φ.symm).map
      ((splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)) = g.1 := by
  refine Matrix.ext fun a b => ?_
  refine (complMap_bijective t (splitPrime_under t)).1 ((complMap_splitProj hΦ t _ a b).trans ?_)
  exact gl_entry (pLoc_locGL (splitPrime t) _) a b

theorem map_split_ne {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) {w : HeightOneSpectrum (𝓞 E)}
    (hw : splitPrime t ≠ w) (k : GL (Fin d) (w.adicCompletion E)) :
    ((finGL E d (locGL E d w k)).1.map Φ.symm).map
      ((splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)) = 1 := by
  refine Matrix.ext fun a b => ?_
  refine (complMap_bijective t (splitPrime_under t)).1 ((complMap_splitProj hΦ t _ a b).trans ?_)
  refine (gl_entry (pLoc_locGL_of_ne hw k) a b).trans ?_
  by_cases e : a = b
  · subst e; simp only [Units.val_one, Matrix.one_apply_eq, map_one]
  · simp only [Units.val_one, Matrix.one_apply_ne e, map_zero]

end Adele

open GlobalTheory.LFun GlobalTheory.CuspRep in

theorem blockEmb_locGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (C : GL (Fin n) E), GlobalTheory.BlockForms.IsAdapted σ J Xf Yf C →
    ∀ (l d : ℕ) (h : l + d ≤ r) (hld : l + d ≤ n) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ g : GL (Fin d) (Fv F v), ∃ x : GLoc σ J v,
        IsCompAt σ J t (Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C)
          (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) x ∧
        emb σ J v x = ι (GlobalTheory.CuspRep.finGL E d (GlobalTheory.CuspRep.locGL E d (splitPrime t)
          (glEquiv d (complEquiv t (splitPrime_under t)) g))) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW v t C hC l d h hld ι hι g
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := hι
  set H := glEquiv d (complEquiv t (splitPrime_under t)) g with hH
  have hM' := hM (finGL E d (locGL E d (splitPrime t) H))
  rw [← map_inv, ← map_inv] at hM'
  refine ⟨proj σ J v (ι (finGL E d (locGL E d (splitPrime t) H))), ?_, ?_⟩
  · let p : AF F ⊗[F] E →+* Fv F v := (splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)
    have hp : ∀ {a b : Type} (Z : Matrix a b E), (adMat F Z).map p = Z.map (t : E →+* Fv F v) := fun Z =>
      Matrix.ext fun a b => by
        change splitProj t (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (Z a b))) = t (Z a b)
        simp
    have hs : p.comp (sigR (AF F) σ) = (splitProj (t.comp σ) : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v) :=
      RingHom.ext fun z => by
        change splitProj t (compFin F E v (sigR _ σ z)) = splitProj (t.comp σ) (compFin F E v z)
        rw [compFin_sigR, splitProj_comp]
    change (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map p = _
    rw [hM', map_formula p _ _ _ _ _ _ _ (by rw [hs]; exact map_split_ne hΦ _ (splitPrime_comp_ne hσ t) _),
      map_split_self hΦ t g, hp, hp]
    set B := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C with hB
    have hBv : B.1 = C.1.map (t : E →+* Fv F v) := rfl
    have h1 : B.1 * blkId _ hld = (blkCols h X).map (t : E →+* Fv F v) := by
      rw [hBv, ← mul_blkId hC h hld, ← blkId_map E (t : E →+* Fv F v) hld]
      exact Matrix.map_mul.symm
    have h2 : (cT (σ : E →+* E) (blkCols h Y) * J).map (t : E →+* Fv F v) * B.1 = (blkId _ hld)ᵀ := by
      rw [hBv, ← Matrix.map_mul, dual_mul hσ hJ hW hC h hld, ← blkId_map E (t : E →+* Fv F v) hld]
      rfl
    exact conj_leviEmb hld B g h1 h2
  · refine ext_inf_fin σ J ?_ (GFin_ext σ J fun u => ?_)
    · rw [projInf_emb]
      refine matHom_injective _ σ J (Units.ext ?_)
      change 1 = (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map (infTens F E)
      rw [hM', map_formula _ _ _ _ _ _ _ _ ?_, map_infTens hΦ]
      · simp
      · have e : (infTens F E).comp (sigR (AF F) σ) = (sigR _ σ).comp (infTens F E) := RingHom.ext (infTens_sigR σ)
        rw [e, RingHom.coe_comp, ← Matrix.map_map, map_infTens hΦ, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [projFinLoc_projFin, projFinLoc_projFin]
      by_cases hu : u = v
      · subst hu; rw [proj_emb_self]
      · have hu' : (splitPrime t).under (𝓞 F) ≠ u := fun e => hu (e.symm.trans (splitPrime_under t))
        rw [proj_emb_ne σ J hu]
        refine matHom_injective _ σ J (Units.ext ?_)
        change 1 = (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map (compFin F E u)
        rw [hM', map_formula _ _ _ _ _ _ _ _ ?_, map_compFin_ne hΦ hu']
        · simp
        · have e : (compFin F E u).comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E u) :=
            RingHom.ext (compFin_sigR σ u)
          rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compFin_ne hΦ hu', Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.BlockForms.LeviLoc

end
