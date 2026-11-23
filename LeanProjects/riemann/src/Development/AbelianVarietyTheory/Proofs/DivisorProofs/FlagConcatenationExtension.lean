import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCokernelComposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactOfPullbackCokernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactPullbackCompatibleSubStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Flag.Concat

variable {X : Scheme.{0}} {E₁ E₂ E₃ : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (hab : a ≫ b = 0)
  {r₁ r₃ : ℕ} (fl₁ : Flag E₁ r₁) (fl₃ : Flag E₃ r₃)

def obj (k : Fin (r₁ + r₃ + 1)) : X.Modules :=
  if h : (k : ℕ) ≤ r₁ then fl₁.F ⟨k, by omega⟩ else pullback b (fl₃.ι ⟨k - r₁, by have := k.2; omega⟩)

theorem obj_of_le {k : Fin (r₁ + r₃ + 1)} {i : Fin (r₁ + 1)} (h : (k : ℕ) = i) :
    obj b fl₁ fl₃ k = fl₁.F i := by
  obtain ⟨i, hi⟩ := i
  simp only at h
  subst h
  exact dif_pos (by omega)

theorem obj_of_gt {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j)
    (hj : 0 < (j : ℕ)) : obj b fl₁ fl₃ k = pullback b (fl₃.ι j) := by
  obtain ⟨j, hj'⟩ := j
  simp only at h hj
  obtain rfl : j = k - r₁ := by omega
  exact dif_neg (by omega)

def incl (k : Fin (r₁ + r₃ + 1)) : obj b fl₁ fl₃ k ⟶ E₂ :=
  if h : (k : ℕ) ≤ r₁ then
    eqToHom (obj_of_le b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl) ≫ fl₁.ι ⟨k, by omega⟩ ≫ a
  else
    eqToHom (obj_of_gt b fl₁ fl₃ (j := ⟨k - r₁, by have := k.2; omega⟩) (by simp only; omega)
      (by simp only; omega)) ≫ pullback.fst b (fl₃.ι _)

theorem incl_of_le {k : Fin (r₁ + r₃ + 1)} {i : Fin (r₁ + 1)} (h : (k : ℕ) = i) :
    incl a b fl₁ fl₃ k = eqToHom (obj_of_le b fl₁ fl₃ h) ≫ fl₁.ι i ≫ a := by
  obtain ⟨i, hi⟩ := i
  simp only at h
  subst h
  exact dif_pos (by omega)

theorem incl_of_gt {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j)
    (hj : 0 < (j : ℕ)) :
    incl a b fl₁ fl₃ k = eqToHom (obj_of_gt b fl₁ fl₃ h hj) ≫ pullback.fst b (fl₃.ι j) := by
  obtain ⟨j, hj'⟩ := j
  simp only at h hj
  obtain rfl : j = k - r₁ := by omega
  exact dif_neg (by omega)

def proj (k : Fin (r₁ + r₃ + 1)) : obj b fl₁ fl₃ k ⟶ fl₃.F ⟨k - r₁, by have := k.2; omega⟩ :=
  if h : (k : ℕ) ≤ r₁ then 0 else
    eqToHom (obj_of_gt b fl₁ fl₃ (j := ⟨k - r₁, by have := k.2; omega⟩) (by simp only; omega)
      (by simp only; omega)) ≫ pullback.snd b (fl₃.ι _)

include hab in

theorem incl_comp (k : Fin (r₁ + r₃ + 1)) :
    incl a b fl₁ fl₃ k ≫ b = proj b fl₁ fl₃ k ≫ fl₃.ι ⟨k - r₁, by have := k.2; omega⟩ := by
  unfold incl proj
  split_ifs with h
  · simp [hab]
  · simp [pullback.condition]

def step (i : Fin (r₁ + r₃)) : obj b fl₁ fl₃ i.castSucc ⟶ obj b fl₁ fl₃ i.succ :=
  if h : (i : ℕ) + 1 ≤ r₁ then
    eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl) ≫
      fl₁.step ⟨i, by omega⟩ ≫
      eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl).symm
  else
    pullback.lift (incl a b fl₁ fl₃ i.castSucc)
        (proj b fl₁ fl₃ i.castSucc ≫ fl₃.step ⟨i - r₁, by omega⟩)
        (by rw [incl_comp a b hab, Category.assoc, Flag.step_ι]; rfl) ≫
      eqToHom (obj_of_gt b fl₁ fl₃ (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
        (by simp only [Fin.val_succ]; omega) (by simp)).symm

theorem step_of_le (i : Fin (r₁ + r₃)) (h : (i : ℕ) + 1 ≤ r₁) :
    step a b hab fl₁ fl₃ i =
      eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl) ≫
        fl₁.step ⟨i, by omega⟩ ≫
        eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl).symm :=
  dif_pos h

theorem step_of_ge (i : Fin (r₁ + r₃)) (h : r₁ ≤ (i : ℕ)) :
    step a b hab fl₁ fl₃ i =
      pullback.lift (incl a b fl₁ fl₃ i.castSucc)
        (proj b fl₁ fl₃ i.castSucc ≫ fl₃.step ⟨i - r₁, by omega⟩)
        (by rw [incl_comp a b hab, Category.assoc, Flag.step_ι]; rfl) ≫
      eqToHom (obj_of_gt b fl₁ fl₃ (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
        (by simp only [Fin.val_succ]; omega) (by simp)).symm :=
  dif_neg (by omega)

theorem step_ι (i : Fin (r₁ + r₃)) :
    step a b hab fl₁ fl₃ i ≫ incl a b fl₁ fl₃ i.succ = incl a b fl₁ fl₃ i.castSucc := by
  unfold step
  split_ifs with h
  · rw [incl_of_le a b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl,
      incl_of_le a b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Flag.step_ι_assoc]
  · rw [incl_of_gt a b fl₁ fl₃ (k := i.succ) (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
      (by simp only [Fin.val_succ]; omega) (by simp)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact pullback.lift_fst _ _ _

end GlobalTheory.Vert.Flag.Concat

namespace GlobalTheory.Vert.Flag.Concat

open GlobalTheory.VB

theorem short_exact_zero_concat : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := GlobalTheory.T.short_exact_cokernel_compose

theorem short_exact_pullback_fst_concat : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := GlobalTheory.T.shortExact_of_pullback_cokernel

theorem short_exact_lift_concat : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := GlobalTheory.T.shortExact_pullback_compatible_sub

theorem isVB_cokernel_comp {X : Scheme.{0}} {E₁ E₂ E₃ G : X.Modules} {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃}
    {h : a ≫ b = 0} (hS : (ShortComplex.mk a b h).ShortExact) (g : G ⟶ E₁) {m n : ℕ}
    (hg : IsVB (cokernel g) m) (h₃ : IsVB E₃ n) : IsVB (cokernel (g ≫ a)) (m + n) := by
  have := hS.mono_f
  exact VBExt.isVB_X₂_of_shortExact X _ m n (shortExact_cokernel_comp g a) hg
    (h₃.of_iso (hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)))

theorem isSubbundle_iso_comp {X : Scheme.{0}} {A B E : X.Modules} (e : A ⟶ B) [IsIso e] {f : B ⟶ E}
    (hf : IsSubbundle f) : IsSubbundle (e ≫ f) := by
  obtain ⟨_, s, hs⟩ := hf
  exact ⟨inferInstance, s, hs.of_iso (cokernelEpiComp e f).symm⟩

variable {X : Scheme.{0}} {E₁ E₂ E₃ : X.Modules} {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃} {hab : a ≫ b = 0}
  (hS : (ShortComplex.mk a b hab).ShortExact) {r₁ r₃ : ℕ} (fl₁ : Flag E₁ r₁) (fl₃ : Flag E₃ r₃)

include hS in

theorem shortExact_incl {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j) :
    ∃ hz : incl a b fl₁ fl₃ k ≫ b ≫ cokernel.π (fl₃.ι j) = 0,
      (ShortComplex.mk (incl a b fl₁ fl₃ k) (b ≫ cokernel.π (fl₃.ι j)) hz).ShortExact := by
  have := hS.epi_g
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · have hk : (k : ℕ) = (Fin.last r₁ : ℕ) := by simp; omega
    have hz : IsZero (fl₃.F j) := by
      have h0 := fl₃.isVB j
      rw [hj] at h0
      exact VB.isVB_zero_iff.1 h0
    exact short_exact_zero_concat X a b hab hS _ (eqToHom (obj_of_le b fl₁ fl₃ hk) ≫ fl₁.ι (Fin.last r₁))
      (by rw [incl_of_le a b fl₁ fl₃ hk, Category.assoc]) _ hz
  · exact short_exact_pullback_fst_concat X b (fl₃.ι j) _ (eqToHom (obj_of_gt b fl₁ fl₃ h hj)) (incl_of_gt a b fl₁ fl₃ h hj)

include hS fl₁ fl₃ in

theorem isVB_E₂ : IsVB E₂ (r₁ + r₃) :=
  VBExt.isVB_X₂_of_shortExact X _ r₁ r₃ hS fl₁.isVB_self fl₃.isVB_self

include hS in
theorem isVB_obj (k : Fin (r₁ + r₃ + 1)) : IsVB (obj b fl₁ fl₃ k) k := by
  by_cases hk : (k : ℕ) ≤ r₁
  · exact (fl₁.isVB ⟨k, by omega⟩).of_iso (eqToIso (obj_of_le b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl)).symm
  · have hkj : (k : ℕ) = r₁ + ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ) := by simp; omega
    obtain ⟨_, hS'⟩ := shortExact_incl hS fl₁ fl₃ hkj
    have h₂ := isVB_E₂ hS fl₁ fl₃
    rw [show r₁ + r₃ = k + (r₃ - ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ)) by simp; omega] at h₂
    exact VB.isVB_X₁_of_shortExact X _ _ _ hS' h₂ (fl₃.isVB_cokernel _)

include hS in
theorem isSubbundle_incl (k : Fin (r₁ + r₃ + 1)) : IsSubbundle (incl a b fl₁ fl₃ k) := by
  by_cases hk : (k : ℕ) < r₁
  · have := hS.mono_f
    rw [incl_of_le a b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl]
    refine isSubbundle_iso_comp _ ⟨inferInstance, _, isVB_cokernel_comp hS _ (fl₁.isVB_cokernel _)
      fl₃.isVB_self⟩
  · have hkj : (k : ℕ) = r₁ + ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ) := by simp; omega
    obtain ⟨_, hS'⟩ := shortExact_incl hS fl₁ fl₃ hkj
    exact isSubbundle_of_shortExact hS' (fl₃.isVB_cokernel _)

include hS in
theorem isIso_incl_last : IsIso (incl a b fl₁ fl₃ (Fin.last (r₁ + r₃))) := by
  rcases Nat.eq_zero_or_pos r₃ with h3 | h3
  · have hk : ((Fin.last (r₁ + r₃) : Fin _) : ℕ) = (Fin.last r₁ : ℕ) := by simp [h3]
    rw [incl_of_le a b fl₁ fl₃ hk]
    have h0 := fl₃.isVB_self
    rw [h3] at h0
    have : IsIso a := hS.isIso_f_iff.2 (VB.isVB_zero_iff.1 h0)
    infer_instance
  · rw [incl_of_gt a b fl₁ fl₃ (j := Fin.last r₃) (by simp) (by simpa using h3)]
    infer_instance

def concat : Flag E₂ (r₁ + r₃) where
  F := obj b fl₁ fl₃
  ι := incl a b fl₁ fl₃
  isSubbundle := isSubbundle_incl hS fl₁ fl₃
  isVB := isVB_obj hS fl₁ fl₃
  step := step a b hab fl₁ fl₃
  step_ι := step_ι a b hab fl₁ fl₃
  isIso_last := isIso_incl_last hS fl₁ fl₃

end GlobalTheory.Vert.Flag.Concat

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

theorem GlobalTheory.Vert.Flag.concat_spec : ∀ (X : Scheme.{0}) (E₁ E₂ E₃ : X.Modules) (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃)
    (h : a ≫ b = 0), (ShortComplex.mk a b h).ShortExact → ∀ (r₁ r₃ : ℕ)
    (fl₁ : GlobalTheory.Vert.Flag E₁ r₁) (fl₃ : GlobalTheory.Vert.Flag E₃ r₃), ∃ fl₂ : GlobalTheory.Vert.Flag E₂ (r₁ + r₃),
    (∀ (k : Fin (r₁ + r₃ + 1)) (i : Fin (r₁ + 1)), (k : ℕ) = i →
      ∃ e : fl₂.F k ≅ fl₁.F i, fl₂.ι k = e.hom ≫ fl₁.ι i ≫ a) ∧
    (∀ (k : Fin (r₁ + r₃ + 1)) (j : Fin (r₃ + 1)), (k : ℕ) = r₁ + j →
      ∃ hz : fl₂.ι k ≫ b ≫ cokernel.π (fl₃.ι j) = 0,
        (ShortComplex.mk (fl₂.ι k) (b ≫ cokernel.π (fl₃.ι j)) hz).ShortExact) ∧
    (∀ (k : Fin (r₁ + r₃)) (i : Fin r₁), (k : ℕ) = i →
      ∃ (e : fl₂.F k.succ ≅ fl₁.F i.succ) (u : fl₂.gr k ≅ fl₁.gr i),
        fl₂.ι k.succ = e.hom ≫ fl₁.ι i.succ ≫ a ∧ fl₂.π k ≫ u.hom = e.hom ≫ fl₁.π i) ∧
    (∀ (k : Fin (r₁ + r₃)) (j : Fin r₃), (k : ℕ) = r₁ + j →
      ∃ (m : fl₂.F k.succ ⟶ fl₃.F j.succ) (u : fl₂.gr k ≅ fl₃.gr j),
        m ≫ fl₃.ι j.succ = fl₂.ι k.succ ≫ b ∧ fl₂.π k ≫ u.hom = m ≫ fl₃.π j) := by
  intro X E₁ E₂ E₃ a b h hS r₁ r₃ fl₁ fl₃
  open GlobalTheory.Vert.Flag.Concat in
  refine ⟨concat hS fl₁ fl₃, fun k i hki => ⟨eqToIso (obj_of_le b fl₁ fl₃ hki), incl_of_le a b fl₁ fl₃ hki⟩,
    fun k j hkj => shortExact_incl hS fl₁ fl₃ hkj, fun k i hki => ?_, fun k j hkj => ?_⟩
  · obtain ⟨i, hi⟩ := i
    simp only at hki
    subst hki
    dsimp only [concat, Flag.gr, Flag.π]
    have hs := Concat.step_of_le a b h fl₁ fl₃ k (by omega)
    refine ⟨eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp)),
      cokernel.mapIso _ _ (eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.castSucc)
        (i := (⟨k, hi⟩ : Fin r₁).castSucc) rfl))
        (eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp))) ?_,
      Concat.incl_of_le a b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp), ?_⟩
    · rw [hs]
      simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    · exact cokernel.π_desc _ _ _
  · obtain ⟨j, hj⟩ := j
    simp only at hkj
    obtain rfl : j = k - r₁ := by omega
    dsimp only [concat, Flag.gr, Flag.π]
    have hs := Concat.step_of_ge a b h fl₁ fl₃ k (by omega)
    have := hS.epi_g
    obtain ⟨hz, hS₁⟩ := Concat.shortExact_incl hS fl₁ fl₃ (k := k.castSucc)
      (j := (⟨k - r₁, hj⟩ : Fin r₃).castSucc) (by simp; omega)
    obtain ⟨hz', hS₂⟩ := Concat.short_exact_lift_concat X b (fl₃.ι (⟨k - r₁, hj⟩ : Fin r₃).castSucc)
      (fl₃.ι (⟨k - r₁, hj⟩ : Fin r₃).succ) (fl₃.step ⟨k - r₁, hj⟩) (fl₃.step_ι _) _ hz hS₁
      (pullback.lift (Concat.incl a b fl₁ fl₃ k.castSucc)
        (Concat.proj b fl₁ fl₃ k.castSucc ≫ fl₃.step ⟨k - r₁, hj⟩)
        (by rw [Concat.incl_comp a b h, Category.assoc, Flag.step_ι]; rfl))
      (Concat.proj b fl₁ fl₃ k.castSucc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    have E := Concat.obj_of_gt b fl₁ fl₃ (k := k.succ) (j := (⟨k - r₁, hj⟩ : Fin r₃).succ)
      (by simp; omega) (by simp)
    refine ⟨eqToHom E ≫ pullback.snd b _, cokernelIsoOfEq hs ≪≫ cokernelCompIsIso _ _ ≪≫
      (cokernelIsCokernel _).coconePointUniqueUpToIso hS₂.gIsCokernel, ?_, ?_⟩
    · rw [Concat.incl_of_gt a b fl₁ fl₃ (k := k.succ) (j := (⟨k - r₁, hj⟩ : Fin r₃).succ)
        (by simp; omega) (by simp)]
      simp [pullback.condition]
    · simp
      erw [(cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hS₂.gIsCokernel WalkingParallelPair.one]
      simp
