import Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAlt
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def tfaExt {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact extE f

theorem tfa_std_iff {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)) :
    x ∈ stdAt E (n + 1) Q ↔ initL E n x ∈ stdAt E n Q ∧ IntAt Q (x (Fin.last n)) := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact h1 j

theorem tfa_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet E n ∅ SG) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (x : Sp E N) :
    tfaExt hN (d.1.liftFr w) x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔ x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) x ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) x ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN, initL_extE, extE_last, tfa_std_iff]
  exact and_congr_left' (hl.1 _)

theorem tfa_conj {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (g : UF E n) (x : Sp E N) (l : Fin N) :
    (tfaExt hN f)⁻¹ ((extUH hN g).1 (tfaExt hN f x)) l =
      if h : l.1 < n then (f⁻¹ (g.1 (f (fun i : Fin n => x ⟨i.1, by omega⟩)))) ⟨l.1, h⟩ else x l := by
  subst hN
  show (extE f).symm (extE g.1 (extE f x)) l = _
  by_cases h : l.1 < n
  · rw [dif_pos h]
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, l = Fin.castSucc i := ⟨⟨l.1, h⟩, Fin.ext rfl⟩
    have e1 : (extE f).symm (extE g.1 (extE f x)) (Fin.castSucc i) = initL E n ((extE f).symm (extE g.1 (extE f x))) i := rfl
    rw [e1, initL_extE_symm, initL_extE, initL_extE]
    rfl
  · rw [dif_neg h]
    obtain rfl : l = Fin.last n := Fin.ext (by have := l.2; simp; omega)
    rw [extE_symm_last, extE_last, extE_last]

def tfaD {n : ℕ} (z : E) (hz : z ≠ 0) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (n + 1) => if i = Fin.last n then LinearEquiv.smulOfNeZero E E z hz else LinearEquiv.refl E E

theorem tfaD_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    tfaD z hz x i = if i = Fin.last n then z * x i else x i := by
  unfold tfaD
  rw [LinearEquiv.piCongrRight_apply]
  split_ifs with h
  · simp [LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  · rfl

theorem tfaD_symm_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    (tfaD z hz).symm x i = if i = Fin.last n then z⁻¹ * x i else x i := by
  have key : tfaD z hz (fun j => if j = Fin.last n then z⁻¹ * x j else x j) = x := by
    funext j
    rw [tfaD_apply]
    by_cases h : j = Fin.last n
    · subst h
      simp [hz]
    · simp only [h, if_false]
  conv_lhs => rw [← key]
  rw [LinearEquiv.symm_apply_apply]

def tfaExtZ {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact (tfaD z hz).trans (extE f)

theorem tfaZ_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet E n ∅ SG) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (hw : pi ∉ w.1.asIdeal) (hz : (algebraMap (𝓞 E) E pi) ≠ 0)
    (x : Sp E N) :
    tfaExtZ hN (d.1.liftFr w) (algebraMap (𝓞 E) E pi) hz x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  have hinit : initL E n (tfaD (algebraMap (𝓞 E) E pi) hz x) = initL E n x := by
    funext i
    show tfaD _ hz x (Fin.castSucc i) = x (Fin.castSucc i)
    rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
  have hlast : tfaD (algebraMap (𝓞 E) E pi) hz x (Fin.last n) = algebraMap (𝓞 E) E pi * x (Fin.last n) := by
    rw [tfaD_apply, if_pos rfl]
  rw [mem_localization_tilN, initL_extE, extE_last, hinit, hlast, tfa_std_iff]
  refine and_congr (hl.1 _) ⟨fun h => ?_, fun h => (IntAt.coe w.1 pi).mul h⟩
  have h2 := (xtIntAt_piInv hw).mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hz, one_mul] at h2

theorem tfaZ_conj {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) (g : UF E n) (x : Sp E N) (l : Fin N) :
    (tfaExtZ hN f z hz)⁻¹ ((extUH hN g).1 (tfaExtZ hN f z hz x)) l =
      if h : l.1 < n then (f⁻¹ (g.1 (f (fun i : Fin n => x ⟨i.1, by omega⟩)))) ⟨l.1, h⟩ else x l := by
  subst hN
  show (tfaD z hz).symm ((extE f).symm (extE g.1 (extE f (tfaD z hz x)))) l = _
  rw [tfaD_symm_apply]
  by_cases h : l.1 < n
  · rw [dif_pos h, if_neg (fun h' => by rw [h'] at h; simp at h)]
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, l = Fin.castSucc i := ⟨⟨l.1, h⟩, Fin.ext rfl⟩
    have e1 : (extE f).symm (extE g.1 (extE f (tfaD z hz x))) (Fin.castSucc i) =
        initL E n ((extE f).symm (extE g.1 (extE f (tfaD z hz x)))) i := rfl
    rw [e1, initL_extE_symm, initL_extE, initL_extE]
    have hinit : initL E n (tfaD z hz x) = initL E n x := by
      funext i
      show tfaD z hz x (Fin.castSucc i) = x (Fin.castSucc i)
      rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
    rw [hinit]
    rfl
  · rw [dif_neg h]
    obtain rfl : l = Fin.last n := Fin.ext (by have := l.2; simp; omega)
    rw [if_pos rfl, extE_symm_last, extE_last, extE_last, tfaD_apply, if_pos rfl, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

end Gen

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (u : Pr.Word)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable (sel mu) in
open Classical in

def topFrA (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') : TopFr (R := R) sel mu u hSG where
  fr P d := if h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal then
      tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩) (algebraMap (𝓞 X.E) X.E (Pr.piT u))
        (fun h0 => h.2 (by rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0; rw [h0]; exact zero_mem _))
    else frameOfY u P.1 (tilR hSG u d)
  spec P d x := by
    by_cases h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal
    · rw [dif_pos h]
      exact tfaZ_spec (N_m_succ R) (Pr.piT u) d h.1 ⟨P.1, hQS P.1 P.2⟩ h.2 _ x
    · rw [dif_neg h]
      exact frameOfY_spec u P.1 (tilR hSG u d) x

open Classical in

theorem topFrA_conj (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (x : Sp X.E (R.N R.m))
    (l : Fin (R.N R.m)) :
    ((topFrA (R := R) sel mu u hSG hQS).fr P d)⁻¹ ((extR R hSG (s.1, s.2.1)).1.1 ((topFrA (R := R) sel mu u hSG hQS).fr P d x)) l =
      if h : l.1 < R.N R.m - 1 then
        ((d.1.liftFr ⟨P.1, hQS P.1 P.2⟩)⁻¹ (s.1.1 (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩ (fun i : Fin (R.N R.m - 1) => x ⟨i.1, by omega⟩))))
          ⟨l.1, h⟩
      else x l := by
  have hOk : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal :=
    ⟨d.2.til (fun P => conj_piT_notMem hPr u P) hpi, hpi ⟨P.1, hQS P.1 P.2⟩⟩
  unfold topFrA
  simp only [dif_pos hOk]
  exact tfaZ_conj (N_m_succ R) _ _ _ s.1 x l

end Top

end Formalism.L2.Col.Sc.Fr
