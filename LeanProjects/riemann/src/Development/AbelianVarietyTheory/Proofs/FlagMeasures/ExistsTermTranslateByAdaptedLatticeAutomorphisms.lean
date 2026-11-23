import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspaceStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransT

open IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def IA (P : HeightOneSpectrum (𝓞 E)) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * x = o

theorem one_nmem (P : HeightOneSpectrum (𝓞 E)) : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem mul_nmem (P : HeightOneSpectrum (𝓞 E)) {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) :
    s * t ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem IA_coe (P : HeightOneSpectrum (𝓞 E)) (o : 𝓞 E) : IA P (o : E) := ⟨1, one_nmem P, o, by simp⟩

theorem IA_zero (P : HeightOneSpectrum (𝓞 E)) : IA P (0 : E) := by simpa using IA_coe P 0

theorem IA_one (P : HeightOneSpectrum (𝓞 E)) : IA P (1 : E) := by simpa using IA_coe P 1

theorem IA_add {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : IA P x) (hy : IA P y) : IA P (x + y) := by
  obtain ⟨s, hs, o, e1⟩ := hx
  obtain ⟨t, ht, p, e2⟩ := hy
  refine ⟨s * t, mul_nmem P hs ht, t * o + s * p, ?_⟩
  push_cast
  linear_combination (t : E) * e1 + (s : E) * e2

theorem IA_mul {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : IA P x) (hy : IA P y) : IA P (x * y) := by
  obtain ⟨s, hs, o, e1⟩ := hx
  obtain ⟨t, ht, p, e2⟩ := hy
  refine ⟨s * t, mul_nmem P hs ht, o * p, ?_⟩
  push_cast
  linear_combination ((t : E) * y) * e1 + (o : E) * e2

theorem IA_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i, IA P (f i)) :
    IA P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IA P) (fun _ _ => IA_add) (IA_zero P) (fun i _ => h i)

theorem locP_smul (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) S.V) {k : E} (hk : IA P k) {x : S.V}
    (hx : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) :
    k • x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) := by
  obtain ⟨s, hs, o, ho⟩ := hk
  obtain ⟨t, ht, htx⟩ := hx
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have e : (s * t) • (k • x) = o • (t • x) := by
    rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O o, Formalism.L2.SG.Pf.smul_O t, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [← ho]; ring
  rw [e]
  exact M.smul_mem o htx

theorem modG_smul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {k : E}
    (hk : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → IA P k) {x : S.V} (hx : ModG S Λ g x) :
    ModG S Λ g (k • x) := fun P hP => locP_smul P _ (hk P hP) (hx P hP)

theorem modG_sum {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {ι : Type*} (s : Finset ι) (f : ι → S.V)
    (h : ∀ i, ModG S Λ g (f i)) : ModG S Λ g (∑ i ∈ s, f i) := fun P hP =>
  Submodule.sum_mem _ fun i _ => h i P hP

theorem mem_localization_aut (P : HeightOneSpectrum (𝓞 E)) {Λ : Submodule (𝓞 E) S.V} {a : S.V ≃ₗ[E] S.V}
    (ha : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) {x : S.V} (hx : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    a x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  rw [← ha, Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_apply_mem]
  exact hx

theorem frame_locP (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ b,
      frame F b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  intro P hP b
  haveI := P.isPrime
  have hsub : ∀ (M : Submodule (𝓞 E) S.V), ∀ y ∈ M, y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M :=
    fun M y hy => ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hy⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · have e : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [e]; exact hsub _ _ hl.1
  · have e : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [e]
    obtain ⟨c, -, hc1, hloc⟩ := hconv.1 P
    have he : F.fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
        (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)) := by
      refine hsub _ _ (Submodule.subset_span ⟨i, ?_⟩)
      simp [hc1 hP i]
    rw [← hloc] at he
    obtain ⟨t, ht, hte⟩ := he
    exact ⟨t, ht, (Submodule.mem_inf.1 hte).1⟩

def triM (w : Fin (r + 1) → Fin r → E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun c b => (if c = b then 1 else 0) + (if h : c.val < r then w b ⟨c.val, h⟩ else 0)

theorem triM_lower (w : Fin (r + 1) → Fin r → E) (hw : ∀ b (c : Fin r), b.val ≤ c.val → w b c = 0) :
    ∀ c b, b < c → triM w c b = 0 := by
  intro c b hbc
  unfold triM
  rw [if_neg hbc.ne']
  split_ifs with h
  · rw [hw b _ (le_of_lt (Fin.lt_def.1 hbc))]; simp
  · simp

theorem triM_diag (w : Fin (r + 1) → Fin r → E) (hw : ∀ b (c : Fin r), b.val ≤ c.val → w b c = 0) :
    ∀ b, triM w b b = 1 := by
  intro b
  unfold triM
  rw [if_pos rfl]
  split_ifs with h
  · rw [hw b _ le_rfl]; simp
  · simp

theorem triM_IA (P : HeightOneSpectrum (𝓞 E)) (w : Fin (r + 1) → Fin r → E) (hw : ∀ b c, IA P (w b c)) :
    ∀ c b, IA P (triM w c b) := by
  intro c b
  unfold triM
  refine IA_add ?_ ?_
  · split_ifs
    · exact IA_one P
    · exact IA_zero P
  · split_ifs
    · exact hw _ _
    · exact IA_zero P

theorem triM_sum {T : E} (F : LFlag S r T) (w : Fin (r + 1) → Fin r → E) (b : Fin (r + 1)) :
    ∑ c, triM w c b • frame F c = frame F b + ∑ i, w b i • F.fl.e i := by
  simp only [triM, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [frame, FlagG.fvec]

theorem mul_lower {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) : ∀ a b, b < a → (A * B) a b = 0 := by
  intro a b hba
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  rcases lt_or_ge d a with h | h
  · rw [hA a d h, zero_mul]
  · rw [hB d b (lt_of_lt_of_le hba h), mul_zero]

theorem mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) (hA1 : ∀ a, A a a = 1) (hB1 : ∀ a, B a a = 1) : ∀ a, (A * B) a a = 1 := by
  intro a
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hA1, hB1, one_mul]
  · intro d _ hd
    rcases lt_or_gt_of_ne hd with h | h
    · rw [hA a d h, zero_mul]
    · rw [hB d a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem mul_IA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, IA P (A a b))
    (hB : ∀ a b, IA P (B a b)) : ∀ a b, IA P ((A * B) a b) := by
  intro a b
  rw [Matrix.mul_apply]
  exact IA_sum _ _ fun d => IA_mul (hA a d) (hB d b)

theorem adapt_mat (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) (a : S.V ≃ₗ[E] S.V) (haΛ : Formalism.HermitianLatticesTheory.gmap a Λ = Λ)
    (haf : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ c b, b < c → W c b = 0) ∧ (∀ b, W b b = 1) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c b, IA P (W c b)) ∧
      ∀ b, a (frame F b) = ∑ c, W c b • frame F c := by
  have hloc := frame_locP Λ g F hconv hl
  have h := fun b : Fin (r + 1) => GlobalTheory.T.flag_coef_integral_of_local_integral Λ g F hconv b.val (a (frame F b) - frame F b) (haf b)
    (fun P hP => sub_mem (mem_localization_aut P haΛ (hloc P hP b)) (hloc P hP b))
  choose w hw0 hw1 hw2 using h
  refine ⟨triM w, triM_lower w hw1, triM_diag w hw1, fun P hP => triM_IA P w (fun b c => hw2 b P hP c), fun b => ?_⟩
  rw [triM_sum, ← hw0 b]
  abel

theorem map_lower {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h : ∀ a b, b < a → ξ a b = 0) :
    ∀ a b, b < a → (ξ.map (fun x : 𝓞 E => (x : E))) a b = 0 := by
  intro a b hba; simp [h a b hba]

theorem map_diag {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h : ∀ a, ξ a a = 1) :
    ∀ a, (ξ.map (fun x : 𝓞 E => (x : E))) a a = 1 := by
  intro a; simp [h a]

theorem isAdmissible_flagPair_of_unitriangular_left_automorphism (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E} (F : LFlag S r T) (G : LFlag S r T')
    (a : S.V ≃ₗ[E] S.V) (haI : a ∈ Formalism.HermitianLatticesTheory.isom S.hT) (haΛ : Formalism.HermitianLatticesTheory.gmap a Λ = Λ)
    (haf : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) (hA : IsAdmissible Λ g F G) :
    IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL a haI G) := by
  have hA2 := (Formalism.L2.SG.Pf.IsAdmissible_mapL a haI g Λ F G).2 hA
  rw [haΛ] at hA2
  obtain ⟨ξ, hξ0, hξ1, hξc⟩ := hA2
  obtain ⟨W, hW0, hW1, hWi, hWe⟩ := adapt_mat Λ g F hconv hl a haΛ haf
  refine GlobalTheory.T.frame_admissible_of_congr_unitriangular Λ g hg F _ (W * ξ.map (fun x : 𝓞 E => (x : E)))
    (mul_lower _ _ hW0 (map_lower ξ hξ0)) (mul_diag _ _ hW0 (map_lower ξ hξ0) hW1 (map_diag ξ hξ1))
    (fun P hP => mul_IA P _ _ (hWi P hP) (fun a b => by simpa using IA_coe P (ξ a b)))
    (frame_locP Λ g F hconv hl) (fun b => ?_)
  have key : ∑ c, (W * ξ.map (fun x : 𝓞 E => (x : E))) c b • frame F c =
      frameAct (frame (Formalism.L2.SG.Saturated.mapL a haI F)) ξ b := by
    simp only [frameAct, Formalism.L2.SG.Saturated.frame_mapL, hWe, Matrix.mul_apply, Matrix.map_apply,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [key]
  exact hξc b

theorem isAdmissible_flagPair_of_unitriangular_right_automorphism (Λ Λ' : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E} (F : LFlag S r T)
    (F' : LFlag S r T') (γ a' : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (ha'I : a' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (ha'Λ : Formalism.HermitianLatticesTheory.gmap a' Λ' = Λ') (ha'f : ∀ b : Fin (r + 1), a' (frame F' b) - frame F' b ∈ Xflag F' b.val)
    (hconv' : IsFixedConv Λ' g F') (hl' : IsLift Λ' F')
    (hFf : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hA : IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL γ hγ F')) :
    IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL (γ * a'⁻¹) (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)) F') := by
  obtain ⟨ξ, hξ0, hξ1, hξc⟩ := hA
  obtain ⟨K, hK0, hK1, hKi, hKe⟩ := adapt_mat Λ' g F' hconv' hl' a'⁻¹ (Formalism.L2.SG.Pf.gmap_inv ha'Λ)
    (GlobalTheory.T.inv_unitriangular_move_frame_mem_flagSubspace F' a' ha'f)
  refine GlobalTheory.T.frame_admissible_of_congr_unitriangular Λ g hg F _ (ξ.map (fun x : 𝓞 E => (x : E)) * K)
    (mul_lower _ _ (map_lower ξ hξ0) hK0) (mul_diag _ _ (map_lower ξ hξ0) hK0 (map_diag ξ hξ1) hK1)
    (fun P hP => mul_IA P _ _ (fun a b => by simpa using IA_coe P (ξ a b)) (hKi P hP))
    hFf (fun b => ?_)
  have key : frame (Formalism.L2.SG.Saturated.mapL (γ * a'⁻¹) (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)) F') b -
      ∑ c, (ξ.map (fun x : 𝓞 E => (x : E)) * K) c b • frame F c =
      ∑ d, K d b • (frame (Formalism.L2.SG.Saturated.mapL γ hγ F') d - frameAct (frame F) ξ d) := by
    rw [Formalism.L2.SG.Saturated.frame_mapL, LinearEquiv.mul_apply, hKe b]
    simp only [Formalism.L2.SG.Saturated.frame_mapL, map_sum, map_smul, frameAct, smul_sub, Finset.sum_sub_distrib,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [key]
  exact modG_sum _ _ fun d => modG_smul (fun P hP => hKi P hP d b) (hξc d)

end Gen

theorem trans_main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∀ a ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∃ s : TauC Y u u', s.lam = t.lam ∧ s.lam' = t.lam' ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), s.lin = n * (a * t.lin * a'⁻¹) * n' := by
  intro D X Y u u' t a ha a' ha'
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hPD := t.rep.2.2.2.2
  have haI : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := ha.1.1
  have ha'I : a' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := ha'.1.1
  have hβ : a * t.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ haI hγ) (Subgroup.inv_mem _ ha'I)
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (a * t.lin * a'⁻¹) t.lam' = t.lam := by
    rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_inv ha'.2, Formalism.L2.SG.Pf.gmap_mul, hγΛ, ha.2]
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hβ
  have hPDβ : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' (mapLF (a * t.lin * a'⁻¹) (lf D (X.Fu u'))) := by
    have hRow := (Y.rowsOK u).1 _ t.mem
    have hRow' := (Y.rowsOK u').1 _ t.mem'
    have hFO' : FrameOK D t.lam' (lf D (X.Fu u')) := ⟨hRow'.2.1.2.2.2, hRow'.2.2⟩
    have hg : Formalism.MainNotions.S.Lat.gS D ≠ 0 := by
      unfold Formalism.MainNotions.S.Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    have emap : ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
        (F : LFlag (VS D) D.R.rS T), mapLF β F = Formalism.L2.SG.Saturated.mapL β hβ F := by
      intro β hβ T F; unfold mapLF; rw [dif_pos hβ]; rfl
    refine ⟨?_, ?_, GlobalTheory.FrameIsom.frameOK_mapLF D _ hβ t.lam' t.lam hβΛ _ _ hFO'⟩
    · rw [emap _ hβ, ← hβΛ]; exact (Formalism.L2.SG.Pf.IsLift_mapL _ hβ _ _).2 hRow'.2.1.2.2.1
    · have hA : IsAdmissible t.lam (Formalism.MainNotions.S.Lat.gS D) (lf D (X.Fu u)) (Formalism.L2.SG.Saturated.mapL t.lin hγ (lf D (X.Fu u'))) := by
        rw [← emap]; exact hPD.2.1
      have hβ2 : t.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)
      have e : Formalism.L2.SG.Saturated.mapL (a * t.lin * a'⁻¹) hβ (lf D (X.Fu u')) =
          Formalism.L2.SG.Saturated.mapL a haI (Formalism.L2.SG.Saturated.mapL (t.lin * a'⁻¹) hβ2 (lf D (X.Fu u'))) := by
        rw [← Formalism.L2.SG.Saturated.mapL_mul]
        congr 1
      rw [emap _ hβ]
      refine (congrArg (fun G => IsAdmissible t.lam (Formalism.MainNotions.S.Lat.gS D) (lf D (X.Fu u)) G) e).mpr ?_
      exact isAdmissible_flagPair_of_unitriangular_left_automorphism t.lam (Formalism.MainNotions.S.Lat.gS D) hg (lf D (X.Fu u))
        (Formalism.L2.SG.Saturated.mapL (t.lin * a'⁻¹) hβ2 (lf D (X.Fu u'))) a haI ha.2 ha.1.2 hRow.2.1.2.2.2 hRow.2.1.2.2.1
        (isAdmissible_flagPair_of_unitriangular_right_automorphism t.lam t.lam' (Formalism.MainNotions.S.Lat.gS D) hg (lf D (X.Fu u)) (lf D (X.Fu u')) t.lin a' hγ ha'I ha'.2 ha'.1.2
          hRow'.2.1.2.2.2 hRow'.2.1.2.2.1 (frame_locP t.lam (Formalism.MainNotions.S.Lat.gS D) _ hRow.2.1.2.2.2 hRow.2.1.2.2.1) hA)
  let p : GCar X u u' (X.Fu u) (X.Fu u') t.lam t.lam' := ⟨(x, a * t.lin * a'⁻¹), hx, hβ, hβΛ, hPDβ⟩
  let s : TauC Y u u' := ⟨t.lam, t.mem, t.lam', t.mem', Quot.mk _ p⟩
  refine ⟨s, rfl, rfl, ?_⟩
  have heq : Equivalence (GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam') := by
    refine ⟨fun p => ⟨1, (Formalism.L2.SG.Pf.NLamSub _ _).one_mem, 1, (Formalism.L2.SG.Pf.NLamSub _ _).one_mem, by simp⟩, ?_, ?_⟩
    · rintro p q ⟨n, hn, n', hn', e⟩
      refine ⟨n⁻¹, (Formalism.L2.SG.Pf.NLamSub t.lam _).inv_mem hn, n'⁻¹, (Formalism.L2.SG.Pf.NLamSub t.lam' _).inv_mem hn', ?_⟩
      rw [e]; group
    · rintro p q w ⟨n, hn, n', hn', e⟩ ⟨m, hm, m', hm', e'⟩
      refine ⟨m * n, (Formalism.L2.SG.Pf.NLamSub t.lam _).mul_mem hm hn, n' * m', (Formalism.L2.SG.Pf.NLamSub t.lam' _).mul_mem hn' hm', ?_⟩
      rw [e', e]; group
  have hq : GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam' p s.rep := by
    have h1 : Quot.mk (GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam') s.rep = Quot.mk _ p := Quot.out_eq _
    exact heq.symm ((heq.eqvGen_iff).1 (Quot.eqvGen_exact h1))
  obtain ⟨n, hn, n', hn', e⟩ := hq
  exact ⟨n, hn, n', hn', e⟩

end GlobalTheory.TransT
