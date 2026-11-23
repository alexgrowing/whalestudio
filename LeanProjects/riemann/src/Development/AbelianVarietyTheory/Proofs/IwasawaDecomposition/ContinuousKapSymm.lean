import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

open Formalism.UG (cT cT_mul cT_one)

variable {D : D7}

def conjGen {A : Type} [CommRing A] {m n : ℕ} (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (PQ : P * Q = 1)
    (QP : Q * P = 1) : Matrix (Fin n) (Fin n) A →* Matrix (Fin m) (Fin m) A where
  toFun x := P * x * Q
  map_one' := by rw [Matrix.mul_one, PQ]
  map_mul' x y := by
    have e : P * x * (Q * P) * (y * Q) = P * (x * y) * Q := by
      rw [QP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [← e]; simp only [Matrix.mul_assoc]

theorem conjGen_conjGen {A : Type} [CommRing A] {m n : ℕ} (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : Matrix (Fin n) (Fin n) A) : conjGen Q P QP PQ (conjGen P Q PQ QP x) = x := by
  show Q * (P * x * Q) * P = x
  calc _ = (Q * P) * x * (Q * P) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [QP, Matrix.one_mul, Matrix.mul_one]

theorem map_conj {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ι : A →+* B) (P : Matrix (Fin m) (Fin n) A)
    (Q : Matrix (Fin n) (Fin m) A) (x : Matrix (Fin n) (Fin n) A) : (P * x * Q).map ι = P.map ι * x.map ι * Q.map ι := by
  rw [Matrix.map_mul, Matrix.map_mul]

theorem unit_conj {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} {g : Matrix (Fin n) (Fin n) A}
    (hP : cT σ P * J' * P = J) (hQ : cT σ Q * J * Q = J') (hg : cT σ g * J * g = J) :
    cT σ (P * g * Q) * J' * (P * g * Q) = J' := by
  calc _ = cT σ Q * (cT σ g * (cT σ P * J' * P) * g) * Q := by simp only [cT_mul, Matrix.mul_assoc]
    _ = J' := by rw [hP, hg, hQ]

theorem map_gram {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ι : A →+* B) (σ : A →+* A) (s : B →+* B)
    (hs : ∀ x, s (ι x) = ι (σ x)) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A} {P : Matrix (Fin m) (Fin n) A}
    (h : cT σ P * J' * P = J) : cT s (P.map ι) * J'.map ι * P.map ι = J.map ι := by
  have e : cT s (P.map ι) = (cT σ P).map ι := by
    ext i j
    exact hs _
  rw [e, ← h, Matrix.map_mul, Matrix.map_mul]

theorem tauE_sig (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (D.sp.cm.sig x) = star (tauE D τ x) := by
  have hcm := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _

theorem skew_rect {m n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {H' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hb : bᴴ * H * b = H') (hba : b * a = 1) (hab : a * b = 1) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * H + H * X = 0) : (a * X * b)ᴴ * H' + H' * (a * X * b) = 0 := by
  have h1 : H' * a = bᴴ * H := by rw [← hb, Matrix.mul_assoc, hba, Matrix.mul_one]
  have h2 : aᴴ * H' = H * b := by
    rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hba, conjTranspose_one, Matrix.one_mul]
  have e : (a * X * b)ᴴ * H' + H' * (a * X * b) = bᴴ * (Xᴴ * (aᴴ * H')) + (H' * a) * X * b := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, h1, h2]
  calc _ = bᴴ * (Xᴴ * H + H * X) * b := by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

theorem bar_rect {m n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {H' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hu : IsUnit H.det) (hu' : IsUnit H'.det) (hb : bᴴ * H * b = H') (hba : b * a = 1)
    (hab : a * b = 1) (Z : Matrix (Fin n) (Fin n) ℂ) : -(H'⁻¹ * (a * Z * b)ᴴ * H') = a * (-(H⁻¹ * Zᴴ * H)) * b := by
  have h1 : H' * a = bᴴ * H := by rw [← hb, Matrix.mul_assoc, hba, Matrix.mul_one]
  have h2 : aᴴ * H' = H * b := by
    rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hba, conjTranspose_one, Matrix.one_mul]
  have h3 : H'⁻¹ * bᴴ = a * H⁻¹ := by
    rw [← nonsing_inv_mul_cancel_left H' (a * H⁻¹) hu', ← Matrix.mul_assoc H', h1, mul_nonsing_inv_cancel_right _ _ hu]
  have e : H'⁻¹ * (a * Z * b)ᴴ * H' = (H'⁻¹ * bᴴ) * Zᴴ * (aᴴ * H') := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, h3, h2]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem exp_rect {m n : ℕ} (hmn : n = m) {a : Matrix (Fin m) (Fin n) ℂ} {b : Matrix (Fin n) (Fin m) ℂ} (hab : a * b = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : a * NormedSpace.exp (t • X) * b = NormedSpace.exp (t • (a * X * b)) := by
  subst hmn
  have hba : b * a = 1 := mul_eq_one_comm.1 hab
  rw [Matrix.mul_assoc, GlobalTheory.Mem.RealTranslate.exp_conj_eq hba X t, ← Matrix.mul_assoc, hab, Matrix.one_mul]

theorem sum_form {A : Type} [CommRing A] {n k : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Matrix (Fin n) (Fin k) A)
    (c : A) (a b : Fin k) :
    ∑ i, ∑ j, c * s (y i b) * J i j * x j a = c * (cT s y * J * x) b a := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_conj {A : Type} [CommRing A] {m n k : ℕ} (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    {P : Matrix (Fin m) (Fin n) A} (h : cT s P * J' * P = J) (x y : Matrix (Fin n) (Fin k) A) :
    cT s (P * y) * J' * (P * x) = cT s y * J * x := by
  rw [← h, cT_mul]
  simp only [Matrix.mul_assoc]

theorem act_conj {A : Type} [CommRing A] {m n k : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (QP : Q * P = 1)
    (h : Matrix (Fin n) (Fin n) A) (x : Matrix (Fin n) (Fin k) A) (y : Matrix (Fin k) (Fin k) A) :
    P * (h * x * y) = P * h * Q * (P * x) * y := by
  calc _ = P * h * (Q * P) * x * y := by rw [QP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

structure IsoMat (V V' : HSp D) where

  P : Matrix (Fin V'.rank) (Fin V.rank) D.host.E

  Q : Matrix (Fin V.rank) (Fin V'.rank) D.host.E
  PQ : P * Q = 1
  QP : Q * P = 1
  gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V'.gram * P = V.gram

namespace IsoMat

def refl (V : HSp D) : IsoMat V V where
  P := 1
  Q := 1
  PQ := Matrix.one_mul 1
  QP := Matrix.one_mul 1
  gram := by rw [cT_one, Matrix.one_mul, Matrix.mul_one]

variable {V V' : HSp D} (I : IsoMat V V')

def symm : IsoMat V' V where
  P := I.Q
  Q := I.P
  PQ := I.QP
  QP := I.PQ
  gram := by
    have h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P = 1 := by
      rw [← cT_mul, I.PQ, cT_one]
    rw [← I.gram]
    calc _ = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P) * V'.gram * (I.P * I.Q) := by
          simp only [Matrix.mul_assoc]
      _ = V'.gram := by rw [h, I.PQ, Matrix.one_mul, Matrix.mul_one]

def ofEquiv (e : V.V ≃ₗ[D.host.E] V'.V) (he : HSpace.IsIsomEmb V V' e.toLinearMap) : IsoMat V V' where
  P := frameMat V' V e.toLinearMap
  Q := frameMat V V' e.symm.toLinearMap
  PQ := by
    unfold frameMat
    rw [← LinearMap.toMatrix_comp]
    simp
  QP := by
    unfold frameMat
    rw [← LinearMap.toMatrix_comp]
    simp
  gram := GlobalTheory.AutFunCounterexample.gram_pull V' V _ he

include I in
theorem rank_eq : V.rank = V'.rank := by
  simpa using (Matrix.square_of_invertible I.Q I.P I.QP I.PQ)

def aP : Matrix (Fin V'.rank) (Fin V.rank) (AE D) := I.P.map (incA D)

def aQ : Matrix (Fin V.rank) (Fin V'.rank) (AE D) := I.Q.map (incA D)

theorem aP_aQ : HMul.hMul I.aP I.aQ = (1 : Matrix _ _ (AE D)) := by
  rw [aP, aQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem aQ_aP : HMul.hMul I.aQ I.aP = (1 : Matrix _ _ (AE D)) := I.symm.aP_aQ

def conjM : Matrix (Fin V.rank) (Fin V.rank) (AE D) →* Matrix (Fin V'.rank) (Fin V'.rank) (AE D) :=
  conjGen I.aP I.aQ I.aP_aQ I.aQ_aP

theorem conjM_apply (x : Matrix (Fin V.rank) (Fin V.rank) (AE D)) : I.conjM x = HMul.hMul (HMul.hMul I.aP x) I.aQ := rfl

def kapF (g : GA D V) : GA D V' :=
  (⟨Units.map I.conjM (matHom V g), unit_conj (sigR (AF D.host.F) D.sp.cm.sig)
    (map_gram (incA D) _ _ (fun _ => rfl) I.gram) (map_gram (incA D) _ _ (fun _ => rfl) I.symm.gram)
    (Subtype.property (show HR (AF D.host.F) D.sp.cm.sig V.gram from g))⟩ : HR (AF D.host.F) D.sp.cm.sig V'.gram)

theorem mat_kapF (g : GA D V) : (matHom V' (I.kapF g)).1 = I.conjM (matHom V g).1 := rfl

theorem kapF_one : I.kapF 1 = 1 :=
  GlobalTheory.AutFunCounterexample.GA_ext V' (by simp only [mat_kapF, map_one, Units.val_one])

theorem kapF_mul (a b : GA D V) : I.kapF (a * b) = I.kapF a * I.kapF b :=
  GlobalTheory.AutFunCounterexample.GA_ext V' (by
    rw [map_mul (matHom V'), Units.val_mul, mat_kapF, mat_kapF, mat_kapF, map_mul, Units.val_mul, map_mul])

theorem kapF_symm (g : GA D V) : I.symm.kapF (I.kapF g) = g :=
  GlobalTheory.AutFunCounterexample.GA_ext V (conjGen_conjGen I.aP I.aQ I.aP_aQ I.aQ_aP _)

def kap : GA D V ≃* GA D V' where
  toFun := I.kapF
  invFun := I.symm.kapF
  left_inv := I.kapF_symm
  right_inv := I.symm.kapF_symm
  map_mul' := I.kapF_mul

theorem mt_kap (g : GA D V) : mt V' (I.kap g) = I.conjM (mt V g) := rfl

theorem kap_symm_apply (h : GA D V') : I.kap.symm h = I.symm.kap h := rfl

theorem continuous_kap : Continuous I.kap := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

theorem continuous_kap_symm : Continuous I.kap.symm := I.symm.continuous_kap

theorem kap_mem_GQ {g : GA D V} (hg : g ∈ GQ V) : I.kap g ∈ GQ V' := by
  obtain ⟨γ, hγ, e⟩ := hg
  refine ⟨Units.map (conjGen I.P I.Q I.PQ I.QP) γ, ?_, ?_⟩
  · exact unit_conj _ I.gram I.symm.gram hγ
  · refine Units.ext ?_
    have e' : (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = mt V g := congrArg Units.val e
    refine (map_conj (incA D) I.P I.Q (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).trans ?_
    rw [e']
    rfl

theorem map_conjM {B : Type} [CommRing B] (ρ : AE D →+* B) (x : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :
    (I.conjM x).map ρ = I.aP.map ρ * x.map ρ * I.aQ.map ρ :=
  map_conj ρ I.aP I.aQ x

theorem map_conjM_one {B : Type} [CommRing B] (ρ : AE D →+* B) {x : Matrix (Fin V.rank) (Fin V.rank) (AE D)} (hx : x.map ρ = 1) :
    (I.conjM x).map ρ = 1 := by
  rw [map_conjM, hx, Matrix.mul_one, ← Matrix.map_mul, I.aP_aQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem kap_mem_GfC {k : GA D V} (hk : k ∈ GfC V) : I.kap k ∈ GfC V' :=
  Units.ext (I.map_conjM_one _ (congrArg Units.val hk))

theorem kap_mem_GinfC {k : GA D V} (hk : k ∈ GinfC V) : I.kap k ∈ GinfC V' :=
  Units.ext (I.map_conjM_one _ (congrArg Units.val hk))

def pT (τ : D.what₂.Tau) : Matrix (Fin V'.rank) (Fin V.rank) ℂ := I.P.map (tauE D τ)

def qT (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V'.rank) ℂ := I.Q.map (tauE D τ)

theorem pT_qT (τ : D.what₂.Tau) : I.pT τ * I.qT τ = 1 := by
  rw [pT, qT, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qT_pT (τ : D.what₂.Tau) : I.qT τ * I.pT τ = 1 := I.symm.pT_qT τ

theorem qT_gram (τ : D.what₂.Tau) : (I.qT τ)ᴴ * gramAt D V τ * I.qT τ = gramAt D V' τ := by
  have h := map_gram (tauE D τ) _ (starRingEnd ℂ) (fun x => (tauE_sig D τ x).symm) I.symm.gram
  exact h

variable {θ : InfF D}

theorem infMat_kap (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) = I.pT τ * infMat D.sp.cm.sig V.gram (θ τ) g * I.qT τ := by
  let ρ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ x := fun x => by
    have := (hθ τ).1 x
    rw [← this]
    simp [ρ, incA, inclR]
  have e1 : I.aP.map ρ = I.pT τ := by ext i j; exact hρ _
  have e2 : I.aQ.map ρ = I.qT τ := by ext i j; exact hρ _
  have := I.map_conjM ρ (mt V g)
  rw [e1, e2] at this
  exact this

def adP (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V'.rank) (Fin V'.rank) ℂ := I.pT τ * X * I.qT τ

theorem adP_mem {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : I.adP τ X ∈ lieAt V' τ :=
  skew_rect (I.qT_gram τ) (I.qT_pT τ) (I.pT_qT τ) hX

theorem conjAt_adP (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V' τ (I.adP τ Z) = I.adP τ (conjAt V τ Z) :=
  bar_rect (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V' τ) (I.qT_gram τ) (I.qT_pT τ) (I.pT_qT τ) Z

theorem kap_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (t : ℝ) :
    I.kap (oneP θ V τ X t) = oneP θ V' τ (I.adP τ X) t := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have R' := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V'
  have h1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 τ).2 hX t)
  have h2 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V' τ (GlobalTheory.SmoothAutCheck.exp_mem_UH (R'.1 τ).2 (I.adP_mem hX) t)
  refine R'.2.2.1 _ (I.kap_mem_GinfC h1.1) _ h2.1 fun τ' => ?_
  rw [I.infMat_kap hθ]
  unfold oneP
  by_cases c : τ' = τ
  · subst c
    rw [h1.2.1, h2.2.1]
    exact exp_rect I.rank_eq (I.pT_qT τ') X t
  · rw [h1.2.2 τ' c, h2.2.2 τ' c, Matrix.mul_one, I.pT_qT]

def tr (φ : GA D V → ℂ) : GA D V' → ℂ := fun h => φ (I.kap.symm h)

theorem Rder_tr (hθ : IsInfFam θ) {τ : D.what₂.Tau} {Y : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hY : Y ∈ lieAt V' τ) (φ : GA D V → ℂ) :
    Rder θ V' τ Y (I.tr φ) = I.tr (Rder θ V τ (I.symm.adP τ Y) φ) := by
  funext h
  unfold Rder tr
  congr 1
  funext t
  rw [map_mul, I.kap_symm_apply (oneP θ V' τ Y t), I.symm.kap_oneP hθ hY]

theorem RderC_tr (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V' τ Z (I.tr φ) = I.tr (RderC θ V τ (I.symm.adP τ Z) φ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V' τ Z
  unfold RderC
  rw [I.Rder_tr hθ h1, I.Rder_tr hθ h2]
  have e1 : I.symm.adP τ ((1 / 2 : ℂ) • (Z + conjAt V' τ Z)) = (1 / 2 : ℂ) • (I.symm.adP τ Z + conjAt V τ (I.symm.adP τ Z)) := by
    rw [I.symm.conjAt_adP]
    simp only [adP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  have e2 : I.symm.adP τ ((1 / (2 * Complex.I)) • (Z - conjAt V' τ Z)) =
      (1 / (2 * Complex.I)) • (I.symm.adP τ Z - conjAt V τ (I.symm.adP τ Z)) := by
    rw [I.symm.conjAt_adP]
    simp only [adP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  rw [e1, e2]
  rfl

theorem tr_mem_SmFun (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) :
    I.tr φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V' := by
  intro k τs Xs hX g
  have := hφ k τs (fun i => I.symm.adP (τs i) (Xs i)) (fun i => I.symm.adP_mem (hX i)) (I.kap.symm g)
  convert this using 2 with t
  unfold tr
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 3
  exact congrArg List.ofFn (funext fun i => I.symm.kap_oneP hθ (hX i) (t i))

variable (S : HSp D)

def phi : WO S V ≃+ WO S V' where
  toFun x := HMul.hMul I.aP x
  invFun y := HMul.hMul I.aQ y
  left_inv x := by
    show HMul.hMul I.aQ (HMul.hMul I.aP x) = x
    rw [← Matrix.mul_assoc, I.aQ_aP, Matrix.one_mul]
  right_inv x := by
    show HMul.hMul I.aP (HMul.hMul I.aQ x) = x
    rw [← Matrix.mul_assoc, I.aP_aQ, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem phi_apply (x : WO S V) : I.phi S x = HMul.hMul I.aP x := rfl

theorem phi_symm_apply (y : WO S V') : (I.phi S).symm y = I.symm.phi S y := rfl

theorem continuous_phi : Continuous (I.phi S) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact continuous_const.matrix_mul continuous_id

theorem continuous_phi_symm : Continuous (I.phi S).symm := I.symm.continuous_phi S

theorem hO_phi (x y : WO S V) : hO S V' (I.phi S x) (I.phi S y) = hO S V x y := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e := sum_form (cA D) (V'.gram.map (incA D)) (I.phi S x) (I.phi S y) (incA D (S.gram⁻¹ a b)) a b
  have e2 := sum_form (cA D) (V.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b
  have e3 := form_conj (cA D) (map_gram (incA D) _ (cA D) (fun _ => rfl) I.gram) x y
  exact e.trans ((congrArg (fun M => incA D (S.gram⁻¹ a b) * M b a) e3).trans e2.symm)

theorem symplOH_phi (x y : WO S V) : symplOH S V' (I.phi S x) (I.phi S y) = symplOH S V x y := by
  unfold symplOH symplO
  rw [I.hO_phi]

theorem phi_ratW (γ : Matrix (Fin V.rank) (Fin S.rank) D.host.E) : I.phi S (ratW V S γ) = ratW V' S (I.P * γ) :=
  by
  show HMul.hMul (I.P.map (incA D)) (γ.map (incA D)) = (I.P * γ).map (incA D)
  rw [Matrix.map_mul]

def trW (f : WO S V → ℂ) : WO S V' → ℂ := fun w => f ((I.phi S).symm w)

theorem trW_symm_trW (f : WO S V → ℂ) : I.symm.trW S (I.trW S f) = f :=
  funext fun w => congrArg f ((I.phi S).symm_apply_apply w)

theorem heisO_trW (ψ : AddChar (AF D.host.F) ℂ) (u : WO S V) (f : WO S V → ℂ) :
    heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S (heisO ψ S V u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (I.phi S).surjective w
  simp only [heisO, trW, ← map_add, AddEquiv.symm_apply_apply, symplOH_phi]

theorem actO_phi (g : GA D S) (h : GA D V) (x : WO S V) :
    I.phi S (actO S V g h x) = actO S V' g (I.kap h) (I.phi S x) :=
  act_conj I.aQ_aP (mt V h) x (mt S g⁻¹)

def trL : (WO S V → ℂ) →ₗ[ℂ] (WO S V' → ℂ) where
  toFun := I.trW S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def omT (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) : GA D S × GA D V' →* Module.End ℂ (WO S V' → ℂ) where
  toFun p := I.trL S ∘ₗ om (p.1, I.kap.symm p.2) ∘ₗ I.symm.trL S
  map_one' := by
    have e : ((1 : GA D S × GA D V').1, I.kap.symm (1 : GA D S × GA D V').2) = (1 : GA D S × GA D V) := by simp
    rw [e, map_one]
    refine LinearMap.ext fun f => ?_
    exact I.symm.trW_symm_trW S f
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have e : ((p * q).1, I.kap.symm (p * q).2) = (p.1, I.kap.symm p.2) * (q.1, I.kap.symm q.2) := by simp
    rw [e, map_mul]
    show I.trW S (om _ (om _ (I.symm.trW S f))) = I.trW S (om _ (I.symm.trW S (I.trW S (om _ (I.symm.trW S f)))))
    rw [I.trW_symm_trW]

theorem omT_apply (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (g : GA D S) (h : GA D V') (f : WO S V' → ℂ) :
    I.omT S om (g, h) f = I.trW S (om (g, I.kap.symm h) (I.symm.trW S f)) := rfl

end IsoMat
end GlobalTheory.Mem.Isom
end
