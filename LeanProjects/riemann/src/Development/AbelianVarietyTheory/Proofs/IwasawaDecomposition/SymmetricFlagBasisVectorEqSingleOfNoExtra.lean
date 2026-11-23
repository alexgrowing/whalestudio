import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem extE_zero (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + 0)) : GlobalTheory.CongLevel.extE 0 κ v = κ v := by
  funext l
  rw [GlobalTheory.CongLevel.extE_apply, Pi.add_apply, GlobalTheory.CongLevel.inX_apply, dif_pos (show l.1 < n from l.2)]
  show v l + (κ v l - v l) = κ v l
  ring

omit [StarRing E] in
theorem intAt_of_ite {a : E} {p : Prop} [Decidable p]
    (h : IntAt P (((qOf P : E) ^ (if p then (1 : ℤ) else 0))⁻¹ * a)) : IntAt P a := by
  split_ifs at h
  · have := (intAt_nat (P := P) (qOf P)).mul h
    rwa [zpow_one, mul_inv_cancel_left₀ qOf_ne_zero] at this
  · simpa using h

theorem maps_D (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))) (κ : GLint E n P)
    (D : ℕ → Prop) [DecidablePred D] (h : ∀ l b : Fin n, D l.1 → ¬ D b.1 → redMat κ l b = 0) (x : Sp E n)
    (hx : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if D l.1 then (1 : ℤ) else 0))⁻¹ * x l)) :
    ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if D l.1 then (1 : ℤ) else 0))⁻¹ * κ.1 x l) := by
  intro l
  have e : κ.1 x l = ∑ b, x b * κ.1 (Pi.single b 1) l := apply_eq_sum (κ.1 : Sp E n →ₗ[E] Sp E n) x l
  rw [e, Finset.mul_sum]
  refine intAt_sum _ fun b _ => ?_
  have ha := glint_entry κ l b
  have hxb := intAt_of_ite (hx b)
  by_cases hl : D l.1
  · rw [if_pos hl, zpow_one]
    by_cases hb : D b.1
    · have h1 := hx b
      rw [if_pos hb, zpow_one] at h1
      have := h1.mul ha
      convert this using 1
      ring
    · have h0 : redP P (κ.1 (Pi.single b 1) l) = 0 := h l b hl hb
      have := hxb.mul (hd _ ha h0)
      convert this using 1
      ring
  · rw [if_neg hl, zpow_zero, inv_one, one_mul]
    exact hxb.mul ha

theorem stab_D (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))) (κ : GLint E n P)
    (D : ℕ → Prop) [DecidablePred D] (h : ∀ l b : Fin n, D l.1 → ¬ D b.1 → redMat κ l b = 0)
    (h' : ∀ l b : Fin n, D l.1 → ¬ D b.1 → redMat κ⁻¹ l b = 0) (x : Sp E n) :
    (∀ l : Fin n, IntAt P (((qOf P : E) ^ (if D l.1 then (1 : ℤ) else 0))⁻¹ * κ.1 x l)) ↔
      ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if D l.1 then (1 : ℤ) else 0))⁻¹ * x l) := by
  refine ⟨fun hx => ?_, maps_D hd κ D h x⟩
  have := maps_D hd κ⁻¹ D h' _ hx
  have e : (κ⁻¹ : GLint E n P).1 (κ.1 x) = x := κ.1.symm_apply_apply x
  rwa [e] at this

theorem mem_symmetricFlagLattice_iff_of_no_extra (k rS s : ℕ) (x : Sp E (n + 0)) :
    x ∈ LocE.flagS P (qOf P) k rS n 0 s ↔
      ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if LocE.bd5 k rS s ≤ symIdx k rS l.1 then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold LocE.flagS
  rw [GlobalTheory.CongLevel.mem_sclLat]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  have hf : LocE.fPos k 0 n l.1 = l.1 := by unfold LocE.fPos; split_ifs <;> omega
  have hs : LocE.scE n (fun i => i + 1) l.1 = 0 := by unfold LocE.scE; rw [if_pos hl]
  rw [hf, hs, zero_add]

omit [StarRing E] in
theorem symmetricFlagBasisVector_eq_single_of_no_extra (k rS s : ℕ) (h : symIdxInv k rS s < n) :
    LocE.bvecS E (qOf P) k rS n 0 s = (Pi.single (⟨symIdxInv k rS s, h⟩ : Fin n) 1 : Sp E n) := by
  unfold LocE.bvecS LocE.bvecG
  have hf : LocE.fIdx k 0 n (symIdxInv k rS s) = symIdxInv k rS s := by unfold LocE.fIdx; split_ifs <;> omega
  have hs : LocE.scE n (fun i => i + 1) (symIdxInv k rS s) = 0 := by unfold LocE.scE; rw [if_pos h]
  rw [hf, hs, zpow_zero, one_smul]
  funext l
  unfold Loc.eN
  simp [Pi.single_apply, Fin.ext_iff]

end Local

end GlobalTheory.Mem.LastGrp

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.TopStep

theorem lv_lt {k rS t b l : ℕ} (hb : b < rSym k rS) (h : symIdx k rS b < symIdx k rS l) :
    lvSym k rS t b < lvSym k rS t l := by
  rw [lvSym_of_lt hb]
  by_cases hl : l < rSym k rS
  · rw [lvSym_of_lt hl]
    unfold posSym symIdx at *
    split_ifs at * <;> omega
  · have h1 := lvSym_of_ge (t := t) hl
    have h2 := posSym_lt hb
    omega

theorem lv_flag {k rS t s l b : ℕ} (hs : s < rSym k rS ∨ ∃ i, s = rSym k rS + i * t)
    (hl : LocE.bd5 k rS s ≤ symIdx k rS l) (hb : ¬ LocE.bd5 k rS s ≤ symIdx k rS b) :
    lvSym k rS t b < lvSym k rS t l := by
  have hbl : symIdx k rS b < symIdx k rS l := by omega
  by_cases hbr : b < rSym k rS
  · exact lv_lt hbr hbl
  · have hsb : symIdx k rS b = b := by unfold symIdx rSym at *; split_ifs <;> omega
    rcases hs with hs | ⟨i, rfl⟩
    · exfalso
      have : LocE.bd5 k rS s ≤ s := by unfold LocE.bd5; split_ifs <;> omega
      omega
    · have hd : LocE.bd5 k rS (rSym k rS + i * t) = rSym k rS + i * t := by
        unfold LocE.bd5 rSym; rw [if_neg (by omega)]
      rw [hd] at hl hb
      have hlr : ¬ l < rSym k rS := by
        intro h; unfold symIdx rSym at *; split_ifs at hl <;> omega
      have hsl : symIdx k rS l = l := by unfold symIdx rSym at *; split_ifs <;> omega
      rw [hsb] at hb
      rw [hsl] at hl
      unfold lvSym
      rw [if_neg hbr, if_neg hlr]
      have ht : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; simp at hb; omega
        · exact h0
      have h1 : (b - rSym k rS) / t < i := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
      have h2 : i ≤ (l - rSym k rS) / t := (Nat.le_div_iff_mul_le ht).2 (by omega)
      omega

end GlobalTheory.Mem.LastGrp

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_JGsym0 (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))) {k rS t : ℕ}
    (hn : rSym k rS ≤ n) (κ : GLint E n P)
    (h1 : ∀ x y : Fin n, lvSym k rS t y.1 < lvSym k rS t x.1 → redMat κ x y = 0)
    (h1' : ∀ x y : Fin n, lvSym k rS t y.1 < lvSym k rS t x.1 → redMat κ⁻¹ x y = 0)
    (h2 : ∀ x : Fin n, x.1 < rSym k rS → redMat κ x x = 1)
    (h3 : ∀ x y : Fin n, x.1 < k → y.1 = k + rS → redMat κ x y = 0) :
    GlobalTheory.CongLevel.extE 0 κ.1 ∈ LocE.JGsym P (qOf P) k rS (rSym k rS) t n 0 := by
  have hst : ∀ s, (s < rSym k rS ∨ ∃ i, s = rSym k rS + i * t) →
      GlobalTheory.CongLevel.extE 0 κ.1 ∈ stabL E (n + 0) (LocE.flagS P (qOf P) k rS n 0 s) := by
    intro s hs v
    rw [extE_zero, mem_symmetricFlagLattice_iff_of_no_extra, mem_symmetricFlagLattice_iff_of_no_extra]
    exact stab_D hd κ (fun y => LocE.bd5 k rS s ≤ symIdx k rS y) (fun l b hl hb => h1 l b (lv_flag hs hl hb))
      (fun l b hl hb => h1' l b (lv_flag hs hl hb)) v
  refine ⟨GlobalTheory.CongLevel.extE_stab P (qOf P) 0 _ κ.1 κ.2, fun s hs => hst s (Or.inr hs),
    fun s hs => ⟨hst s (Or.inl hs), ?_⟩⟩
  have hb : symIdxInv k rS s < n := by unfold symIdxInv rSym at *; split_ifs <;> omega
  rw [extE_zero, symmetricFlagBasisVector_eq_single_of_no_extra k rS s hb, mem_symmetricFlagLattice_iff_of_no_extra]
  intro l
  set b : Fin n := ⟨symIdxInv k rS s, hb⟩ with hbdef
  have ha := glint_entry κ l b
  have hbr : b.1 < rSym k rS := by
    show symIdxInv k rS s < rSym k rS
    unfold symIdxInv rSym at *; split_ifs <;> omega
  have hsg : IntAt P ((Pi.single b 1 : Sp E n) l) := by
    by_cases h : l = b
    · subst h; simpa using intAt_one
    · simpa [h] using intAt_zero
  rw [Pi.sub_apply]
  split_ifs with hl
  · rw [zpow_one]
    have key : redMat κ l b = (Pi.single b 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l := by
      by_cases hlb : l = b
      · subst hlb
        rw [Pi.single_eq_same]
        exact h2 _ hbr
      · rw [Pi.single_eq_of_ne hlb]
        have hsb : symIdx k rS b.1 = s := symIdx_symIdxInv k rS s
        by_cases hsk : s = rS + k
        · have hb1 : b.1 = k + rS := by
            show symIdxInv k rS s = k + rS
            unfold symIdxInv; split_ifs <;> omega
          by_cases hlk : l.1 < k
          · exact h3 l b hlk hb1
          · refine h1 l b (lv_lt (by rw [hb1]; unfold rSym; omega) ?_)
            have hd5 : LocE.bd5 k rS s = rS := by unfold LocE.bd5; rw [if_pos hsk]
            rw [hd5] at hl
            have : l.1 ≠ b.1 := fun e => hlb (Fin.ext e)
            rw [hsb]
            unfold symIdx at hl ⊢
            split_ifs at hl ⊢ <;> omega
        · have hd5 : LocE.bd5 k rS s = s := by unfold LocE.bd5; rw [if_neg hsk]
          rw [hd5] at hl
          refine h1 l b (lv_lt hbr ?_)
          have hne : symIdx k rS l.1 ≠ symIdx k rS b.1 := fun e => hlb (Fin.ext (by
            have := congrArg (symIdxInv k rS) e
            rwa [symIdxInv_symIdx, symIdxInv_symIdx] at this))
          omega
    have h0 : redP P (κ.1 (Pi.single b 1) l - (Pi.single b 1 : Sp E n) l) = 0 := by
      rw [reduction_sub ha hsg]
      have e1 : redP P (κ.1 (Pi.single b 1) l) = redMat κ l b := rfl
      have e2 : redP P ((Pi.single b 1 : Sp E n) l) = (Pi.single b 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l := by
        by_cases h : l = b
        · subst h; simpa using reduction_one₂
        · simpa [h] using reduction_zero
      rw [e1, e2, key, sub_self]
    have := hd _ (intAt_sub ha hsg) h0
    convert this using 1
    ring
  · rw [zpow_zero, inv_one, one_mul]
    exact intAt_sub ha hsg

theorem mem_JGsym_c (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))) {k rS t c : ℕ} (hc : c = 0)
    (hn : rSym k rS ≤ n) (κ : GLint E n P)
    (h1 : ∀ x y : Fin n, lvSym k rS t y.1 < lvSym k rS t x.1 → redMat κ x y = 0)
    (h1' : ∀ x y : Fin n, lvSym k rS t y.1 < lvSym k rS t x.1 → redMat κ⁻¹ x y = 0)
    (h2 : ∀ x : Fin n, x.1 < rSym k rS → redMat κ x x = 1)
    (h3 : ∀ x y : Fin n, x.1 < k → y.1 = k + rS → redMat κ x y = 0) :
    GlobalTheory.CongLevel.extE c κ.1 ∈ LocE.JGsym P (qOf P) k rS (rSym k rS) t n c := by
  subst hc
  exact mem_JGsym0 hd hn κ h1 h1' h2 h3

end Local

end GlobalTheory.Mem.LastGrp

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.TopStep

theorem mem_levG_last : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Matrix.GeneralLinearGroup.map e.toRingHom M ∈ JSymG κ (R.N j) R.k (rSD R) R.t false → M ∈ (L.levG j b w).H := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL hs j hj b w κ _ e M hM
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  rw [hL.grpG]
  obtain ⟨k0, hk0⟩ := GlobalTheory.Mem.Col2.redGL_surjective (n := R.N (m2 + 1)) w.1 M
  refine ⟨k0.1, ?_, fun x hx => by rw [redV_redGL k0 hx, hk0]⟩
  rw [hL.last_h]
  have hd := GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX hPr w.1 w.2
  have eM : ∀ x y, redMat k0 x y = M.1 x y := fun x y => by rw [← redGL_val, hk0]
  have eMi : ∀ x y, redMat k0⁻¹ x y = (M⁻¹).1 x y := fun x y => by rw [← redGL_val, map_inv, hk0]
  obtain ⟨hA, hB⟩ := hM
  have hr : rSym R.k R.rS = R.r := rSym_rSD R
  have hn : rSym R.k R.rS ≤ R.N (m2 + 1) := by
    rw [hr]
    unfold Ranks.r Ranks.N
    have := Nat.le_mul_of_pos_right (m2 + 1) (by omega : 0 < R.t + 1)
    omega
  have ent : ∀ x y, ((Matrix.GeneralLinearGroup.map e.toRingHom M : GL _ _) : Matrix _ _ _) x y = e (M.1 x y) :=
    fun _ _ => rfl
  have ent' : ∀ x y, (((Matrix.GeneralLinearGroup.map e.toRingHom M)⁻¹ : GL _ _) : Matrix _ _ _) x y = e ((M⁻¹).1 x y) :=
    fun x y => by rw [← map_inv]; rfl
  have z : ∀ a, e a = 0 → a = 0 := fun a h => e.injective (h.trans (map_zero e).symm)
  have o : ∀ a, e a = 1 → a = 1 := fun a h => e.injective (h.trans (map_one e).symm)
  have hJ : GlobalTheory.CongLevel.extE (cOf R (m2 + 1)) k0.1 ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) w.1 := by
    unfold Jat
    rw [if_pos w.2, hs, if_pos rfl, ← hr]
    refine mem_JGsym_c hd hc hn k0 (fun x y hxy => ?_) (fun x y hxy => ?_) (fun x hx => ?_) (fun x y hx hy => ?_)
    · rw [eM]; exact z _ (by rw [← ent]; exact hA.1 x y hxy)
    · rw [eMi]; exact z _ (by rw [← ent']; exact hB.1 x y hxy)
    · rw [eM]; exact o _ (by rw [← ent]; exact hA.2.1 x hx)
    · rw [eM]; exact z _ (by rw [← ent]; exact hA.2.2.1 x y hx hy)
  exact ⟨GlobalTheory.CongLevel.extE (cOf R (m2 + 1)) k0.1, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ _, by simpa using hJ⟩,
    GlobalTheory.CongLevel.extE_inX _ _⟩

end GlobalTheory.Mem.LastGrp
