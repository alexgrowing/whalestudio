import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Abs

variable {A K R : Type} [CommRing A] [CommRing K] [CommRing R] {n : ℕ}

theorem mem_range_bc_iff (ι : R →+* K) (hι : Function.Injective ι) (M : GL (Fin n) K) :
    M ∈ (bc (n := Fin n) ι).range ↔ (∀ a b, (M : Matrix (Fin n) (Fin n) K) a b ∈ ι.range) ∧
      (∀ a b, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ ι.range) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun a b => ⟨(g : Matrix (Fin n) (Fin n) R) a b, rfl⟩,
      fun a b => ⟨((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b, ?_⟩⟩
    rw [← map_inv]; rfl
  · rintro ⟨h1, h2⟩
    choose A0 hA using h1
    choose B0 hB using h2
    have eA : (Matrix.of A0).map ι = (M : Matrix (Fin n) (Fin n) K) := by ext a b; exact hA a b
    have eB : (Matrix.of B0).map ι = ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext a b; exact hB a b
    have h12 : Matrix.of A0 * Matrix.of B0 = 1 := by
      apply Matrix.map_injective hι
      show (Matrix.of A0 * Matrix.of B0).map ι = (1 : Matrix (Fin n) (Fin n) R).map ι
      rw [Matrix.map_mul, eA, eB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero ι) (map_one ι)]
    have h21 : Matrix.of B0 * Matrix.of A0 = 1 := by
      apply Matrix.map_injective hι
      show (Matrix.of B0 * Matrix.of A0).map ι = (1 : Matrix (Fin n) (Fin n) R).map ι
      rw [Matrix.map_mul, eA, eB, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero ι) (map_one ι)]
    exact ⟨⟨Matrix.of A0, Matrix.of B0, h12, h21⟩, Units.ext eA⟩

def IntIn (ι : R →+* K) (fr : GL (Fin n) K) (t : Fin n → K) : Prop :=
  ∀ b, ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec t b ∈ ι.range

theorem entries_iff (ι : R →+* K) (fr x1 : GL (Fin n) K) :
    (∀ a b, ((fr⁻¹ * x1 * fr : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ ι.range) ↔
      ∀ t, IntIn ι fr t → IntIn ι fr ((x1 : Matrix (Fin n) (Fin n) K) *ᵥ t) := by
  constructor
  · intro h t ht a
    have e : ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((x1 : Matrix (Fin n) (Fin n) K) *ᵥ t) =
        ((fr⁻¹ * x1 * fr : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ t) := by
      simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Units.mul_inv, Matrix.mul_one]
    rw [e]
    show ∑ b, ((fr⁻¹ * x1 * fr : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b *
      (((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ t) b ∈ ι.range
    exact Subring.sum_mem _ fun b _ => Subring.mul_mem _ (h a b) (ht b)
  · intro h a b
    have h0 : IntIn ι fr ((fr : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1) := by
      intro c
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    have h1 := h _ h0 a
    have e : (((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((x1 : Matrix (Fin n) (Fin n) K) *ᵥ ((fr : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1))) a =
        ((fr⁻¹ * x1 * fr : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b := by
      simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [e] at h1

variable (s : A →+* A) (Jm : Matrix (Fin n) (Fin n) A) (spl : A ≃+* K × K)

theorem hform_fst (hs : ∀ x, spl (s x) = ((spl x).2, (spl x).1)) (z y : Fin n → A) :
    (spl (hform s Jm z y)).1 = ∑ i, ∑ j, (spl (z i)).2 * (spl (Jm i j)).1 * (spl (y j)).1 := by
  simp only [hform, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, hs]

theorem hform_snd (hs : ∀ x, spl (s x) = ((spl x).2, (spl x).1)) (z y : Fin n → A) :
    (spl (hform s Jm z y)).2 = ∑ i, ∑ j, (spl (z i)).1 * (spl (Jm i j)).2 * (spl (y j)).2 := by
  simp only [hform, map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, hs]

theorem fst_mulVec (g : GL (Fin n) A) (y : Fin n → A) (b : Fin n) :
    (spl (((g : Matrix (Fin n) (Fin n) A) *ᵥ y) b)).1 =
      ((bc ((RingHom.fst K K).comp spl.toRingHom) g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
        (fun c => (spl (y c)).1) b :=
  RingHom.map_mulVec ((RingHom.fst K K).comp spl.toRingHom) (g : Matrix (Fin n) (Fin n) A) y b

variable {S : Type} [CommRing S] [Algebra S A] (Λ : Submodule S (Fin n → A)) (ι : R →+* K) (OA : Set A) (fr : GL (Fin n) K)

theorem stab_fwd (hfr : ∀ t : Fin n → K, (∃ y ∈ Λ, ∀ b, (spl (y b)).1 = t b) ↔ IntIn ι fr t)
    (g : GL (Fin n) A) (hg : g ∈ stabGL Λ) (t : Fin n → K) (ht : IntIn ι fr t) :
    IntIn ι fr (((bc ((RingHom.fst K K).comp spl.toRingHom) g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ t) := by
  obtain ⟨y, hy, hyt⟩ := (hfr t).2 ht
  refine (hfr _).1 ⟨(g : Matrix (Fin n) (Fin n) A) *ᵥ y, (hg y).1 hy, fun b => ?_⟩
  rw [fst_mulVec]
  congr 1
  funext c
  exact hyt c

theorem stab_bwd (hs : ∀ x, spl (s x) = ((spl x).2, (spl x).1))
    (hOA : ∀ x, x ∈ OA ↔ (spl x).1 ∈ ι.range ∧ (spl x).2 ∈ ι.range)
    (hdual : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform s Jm z y ∈ OA)
    (hfr : ∀ t : Fin n → K, (∃ y ∈ Λ, ∀ b, (spl (y b)).1 = t b) ↔ IntIn ι fr t)
    (g : GL (Fin n) A) (hg : g ∈ UJ s Jm)
    (h1 : ∀ t, IntIn ι fr t → IntIn ι fr
      (((bc ((RingHom.fst K K).comp spl.toRingHom) g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ t))
    (h2 : ∀ t, IntIn ι fr t → IntIn ι fr
      (((bc ((RingHom.fst K K).comp spl.toRingHom) g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ t))
    (y : Fin n → A) (hy : y ∈ Λ) : (g : Matrix (Fin n) (Fin n) A) *ᵥ y ∈ Λ := by
  rw [hdual]
  intro z hz
  rw [hOA]
  constructor
  · have ht : IntIn ι fr (fun c => (spl (y c)).1) := (hfr _).1 ⟨y, hy, fun _ => rfl⟩
    obtain ⟨y', hy', hyy⟩ := (hfr _).2 (h1 _ ht)
    have e : (spl (hform s Jm z ((g : Matrix (Fin n) (Fin n) A) *ᵥ y))).1 = (spl (hform s Jm z y')).1 := by
      rw [hform_fst s Jm spl hs, hform_fst s Jm spl hs]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [fst_mulVec, hyy j]
    rw [e]
    exact ((hOA _).1 ((hdual y').1 hy' z hz)).1
  · have ht : IntIn ι fr (fun c => (spl (z c)).1) := (hfr _).1 ⟨z, hz, fun _ => rfl⟩
    obtain ⟨z', hz', hzz⟩ := (hfr _).2 (h2 _ ht)
    have e0 : hform s Jm z ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) =
        hform s Jm (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ z) y := by
      have hgJ : cT s (g : Matrix (Fin n) (Fin n) A) * Jm * (g : Matrix (Fin n) (Fin n) A) = Jm := hg
      have hz0 : z = (g : Matrix (Fin n) (Fin n) A) *ᵥ (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      conv_lhs => rw [hz0]
      rw [Formalism.UG.P.hform_mulVec, hgJ]
    have e : (spl (hform s Jm z ((g : Matrix (Fin n) (Fin n) A) *ᵥ y))).2 = (spl (hform s Jm z' y)).2 := by
      rw [e0, hform_snd s Jm spl hs, hform_snd s Jm spl hs]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [fst_mulVec, hzz i]
    rw [e]
    exact ((hOA _).1 ((hdual y).1 hy z' hz')).2

theorem splitStab_abs (hι : Function.Injective ι) (hs : ∀ x, spl (s x) = ((spl x).2, (spl x).1))
    (hOA : ∀ x, x ∈ OA ↔ (spl x).1 ∈ ι.range ∧ (spl x).2 ∈ ι.range)
    (hdual : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform s Jm z y ∈ OA)
    (hfr : ∀ t : Fin n → K, (∃ y ∈ Λ, ∀ b, (spl (y b)).1 = t b) ↔ IntIn ι fr t)
    (x : GL (Fin n) A) (hx : x ∈ UJ s Jm) :
    x ∈ stabGL Λ ↔ fr⁻¹ * bc ((RingHom.fst K K).comp spl.toRingHom) x * fr ∈ (bc (n := Fin n) ι).range := by
  have hinv : (fr⁻¹ * bc ((RingHom.fst K K).comp spl.toRingHom) x * fr)⁻¹ =
      fr⁻¹ * bc ((RingHom.fst K K).comp spl.toRingHom) x⁻¹ * fr := by
    rw [map_inv]; group
  rw [mem_range_bc_iff ι hι, hinv, entries_iff, entries_iff]
  constructor
  · intro h
    exact ⟨stab_fwd spl Λ ι fr hfr x h, stab_fwd spl Λ ι fr hfr x⁻¹ ((stabGL Λ).inv_mem h)⟩
  · rintro ⟨h1, h2⟩ y
    constructor
    · exact stab_bwd s Jm spl Λ ι OA fr hs hOA hdual hfr x hx h1 h2 y
    · intro hy
      have := stab_bwd s Jm spl Λ ι OA fr hs hOA hdual hfr x⁻¹ ((UJ s Jm).inv_mem hx) h2 (by rwa [inv_inv]) _ hy
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Abs

section Conc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_int_iff (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) :
    a ∈ v.adicCompletionIntegers F ↔ a ∈ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).range :=
  ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨b, rfl⟩; exact b.2⟩

theorem splitStabL_of (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (Lb : Submodule (𝓞 E) (Fin n → E))
    (fr : GL (Fin n) (v.adicCompletion F))
    (hsig : ∀ x, spl (sigR σ (v.adicCompletion F) x) = swapR _ (spl x))
    (hint : ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ↔
      (spl x).1 ∈ v.adicCompletionIntegers F ∧ (spl x).2 ∈ v.adicCompletionIntegers F)
    (hdual : ∀ y, y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb ↔
      ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
    (hfr : ∀ x : Fin n → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F)
          (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
        ∀ b, (spl (y b)).1 = x b) ↔
      ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F) :
    SplitStabL σ J v spl Lb fr := by
  intro x hx
  rw [toFr_apply]
  rw [← splitStab_abs (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) spl
    (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb)
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring : Set _) fr
    (algMapV_injective F v) (fun y => hsig y)
    (fun y => by rw [← mem_int_iff, ← mem_int_iff]; exact hint y) hdual
    (fun t => by unfold IntIn; simp only [← mem_int_iff]; exact hfr t) x hx]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

def SplitInt (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ↔
    (spl x).1 ∈ v.adicCompletionIntegers F ∧ (spl x).2 ∈ v.adicCompletionIntegers F

def SelfDualAt (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y, y ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb ↔
    ∀ z ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y ∈
        tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}

def levAtG_of_GLev' (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (G : Formalism.L2.Forms.GLoc F E σ gp) (k m t j nb skip fc : ℕ)
    (hfc : fc = fcX k m j n) (X : Formalism.L2.Forms.GLev S G (aX k m j) t nb skip fc (fixX m j))
    (hint : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), SplitInt v (G.sp i v h))
    (hdual : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → SelfDualAt σ J v S.Lb) :
    LevAtG σ J gp G.sp S.Lb S.Uloc k m t j :=
  levAtG_of_GLev S G k m t j nb skip fc hfc X fun i v h =>
    splitStabL_of σ J v (G.sp i v h) S.Lb (X.fr i v h) (G.sp_sig i v h) (hint i v h) (hdual i v h) (X.fr_lat i v h)

end Conc

end Formalism.L2.G
