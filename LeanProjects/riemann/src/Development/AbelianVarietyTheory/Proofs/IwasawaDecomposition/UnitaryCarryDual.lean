import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem sigR_int (σ : E →ₐ[F] E) (x : E ⊗[F] 𝔸)
    (hx : x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) :
    sigR σ 𝔸 x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  have hle : tensInt (F := F) 𝔸 (intOE E) (intAd F) ≤
      (tensInt (F := F) 𝔸 (intOE E) (intAd F)).comap (sigR σ 𝔸) := by
    conv_lhs => unfold tensInt
    rw [Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      obtain ⟨a, r, hr⟩ := a
      subst hr
      have hi : IsIntegral ℤ (σ (r : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)
      change (σ (r : E)) ⊗ₜ[F] (1 : 𝔸) ∈ _
      exact Subring.subset_closure (Or.inl ⟨⟨σ (r : E), ⟨⟨σ (r : E), hi⟩, rfl⟩⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      change (σ (1 : E)) ⊗ₜ[F] (y : 𝔸) ∈ _
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  exact hle hx

theorem form_latS_int (σ : E →ₐ[F] E) {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L')
    (u : Fin n → E ⊗[F] 𝔸)
    (hu : u ∈ latS (F := F) 𝔸 (tensInt (F := F) 𝔸 (intOE E) (intAd F)) L') :
    (fun i => sigR σ 𝔸 (u i)) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) ∈
      tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    obtain ⟨r, hr⟩ := hz l hl
    have e : (fun i => sigR σ 𝔸 (inclE (F := F) 𝔸 (l i))) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) =
        inclE (F := F) 𝔸 (hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z) := by
      have h1 : hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) l z = ∑ i, σ (l i) * z i := by
        unfold hform
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.one_apply]
      rw [h1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      rfl
    simp only [] at e ⊢
    rw [e, ← hr]
    exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨r, rfl⟩⟩, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb =>
    have : (fun i => sigR σ 𝔸 ((a + b) i)) = (fun i => sigR σ 𝔸 (a i)) + (fun i => sigR σ 𝔸 (b i)) := by
      funext i; simp
    rw [this, add_dotProduct]
    exact add_mem ha hb
  | smul c a _ ha =>
    have : (fun i => sigR σ 𝔸 ((c • a) i)) = sigR σ 𝔸 (c : E ⊗[F] 𝔸) • (fun i => sigR σ 𝔸 (a i)) := by
      funext i
      simp [Subring.smul_def]
    rw [this, smul_dotProduct]
    exact mul_mem (sigR_int σ _ c.2) ha

end GlobalTheory.Mem.LevDual

namespace GlobalTheory.Mem.LevDual

theorem sigR_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (σ e) := rfl

theorem hform_one {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma prV_mem_latS (w : HeightOneSpectrum (𝓞 F)) {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E))
    {v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) :
    (fun i => _root_.Formalism.UG.prV w (v i)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L := by
  unfold _root_.Formalism.UG.latS at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨x, hx, ?_⟩
    funext i
    exact (_root_.Formalism.UG.P.afsplit_prV_inclE w (x i)).symm
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    funext i
    simp
  | smul c a _ ha =>
    have hc : _root_.Formalism.UG.prV w (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w :=
      by unfold _root_.Formalism.BasicNotions.intV; exact _root_.Formalism.UG.P.afsplit_prV_int w _ c.2
    convert Submodule.smul_mem _ (⟨_, hc⟩ : _root_.Formalism.BasicNotions.intV (F := F) E w) ha using 1
    funext i
    simp [Subring.smul_def]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma inclE_mem_intV_of_mem_intOE (w : HeightOneSpectrum (𝓞 F)) {a : E} (ha : a ∈ _root_.Formalism.UG.intOE E) :
    _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) a ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma hform_one_apply {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (x y : Fin m → A) :
    _root_.Formalism.UG.hform σ 1 x y = ∑ i, σ (x i) * y i := by
  unfold _root_.Formalism.UG.hform
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma algHom_coe_mem_intOE (σ : E →ₐ[F] E) (r : 𝓞 E) : σ (r : E) ∈ _root_.Formalism.UG.intOE E := by
  unfold _root_.Formalism.UG.intOE
  exact ⟨⟨σ r, (r.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)⟩, rfl⟩

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma sigR_mem_intV' (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    {c : E ⊗[F] w.adicCompletion F} (hc : c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w) :
    _root_.Formalism.UG.sigR σ (w.adicCompletion F) c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt at *
  have hle : Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F]
        (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring => (1 : E) ⊗ₜ[F] (y : w.adicCompletion F)) ≤
      (Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring =>
        (1 : E) ⊗ₜ[F] (y : w.adicCompletion F))).comap (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) := by
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨r, hr⟩ : (x : E) ∈ (algebraMap (𝓞 E) E).range := x.2
      have hσ : σ (x : E) ∈ _root_.Formalism.UG.intOE E := by rw [← hr]; exact algHom_coe_mem_intOE σ r
      apply Subring.subset_closure
      left
      refine ⟨⟨σ x, hσ⟩, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
    · apply Subring.subset_closure
      right
      refine ⟨y, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
  exact hle hc

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma pairing_mem_intV_of_mem_dualSet (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {m : ℕ}
    (L : Submodule (𝓞 E) (Fin m → E)) {z : Fin m → E} (hz : z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L)
    {x : Fin m → E ⊗[F] w.adicCompletion F}
    (hx : x ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L) :
    ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) (x j) * _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z j) ∈
      _root_.Formalism.BasicNotions.intV (F := F) E w := by
  have hz' : ∀ y ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 y z ∈ (algebraMap (𝓞 E) E).range := hz
  unfold _root_.Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    have h := inclE_mem_intV_of_mem_intOE (F := F) w (hz' y hy)
    rw [hform_one_apply, map_sum] at h
    convert h using 2 with j
    rw [map_mul]
    congr 1
    all_goals (unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE; simp)
  | zero => simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    simp [map_add, add_mul, Finset.sum_add_distrib]
  | smul c a _ ha =>
    convert mul_mem (sigR_mem_intV' σ w c.2) ha using 1
    simp [Subring.smul_def, map_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.Mem.LevDual.unitary_carry_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ _root_.Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) → ∀ z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L', ((_root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L)) := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL L' Y hY hLat z hz
  subst hJ
  cases n with
  | zero =>
    convert Submodule.zero_mem _ using 1
  | succ m =>
    set Yw := _root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y with hYw_def
    have hYwU : Yw ∈ _root_.Formalism.UG.UPts σ 1 (w.adicCompletion F) := _root_.Formalism.UG.P.afsplit_bc_mem σ 1 w Y hY
    have hunit : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
        (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) = 1 := by
      have h := hYwU
      unfold _root_.Formalism.UG.UPts _root_.Formalism.UG.UJ at h
      change _ * _ * _ = _ at h
      rwa [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h
    have hinv : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) =
        _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by
      calc ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) _)
          = (_root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
              (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _)) * ((Yw⁻¹ : GL (Fin (m + 1)) _) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by rw [hunit, one_mul]
        _ = _ := by rw [mul_assoc, Units.mul_inv, mul_one]
    set v : Fin (m + 1) → E ⊗[F] w.adicCompletion F :=
      fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a) with hv
    have hu_apply : ∀ i, (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i =
        ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j i) * v j := by
      intro i
      rw [hinv]
      unfold _root_.Formalism.UG.cT
      simp [Matrix.mulVec, dotProduct]
    have hcol : ∀ x ∈ L, (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
        (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (x a)) ∈
        _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L' := by
      intro x hx
      have hA : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) ∈
          _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
            (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' := by
        rw [hLat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      have h := prV_mem_latS w L' hA
      convert h using 1
      funext i
      rw [hYw_def, _root_.Formalism.UG.P.afsplit_coe_bc_prV, RingHom.map_mulVec]
      congr 1
    have hlast : ∀ j : Fin (m + 1), j.1 + 1 = m + 1 ↔ j = Fin.last m := fun j => by
      rw [Fin.ext_iff, Fin.val_last]
      omega
    have hsingle : ∀ i, i ≠ Fin.last m → (Pi.single i 1 : Fin (m + 1) → E) ∈ L := by
      intro i hi
      rw [hL]
      intro j
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp, fun h => absurd ((hlast j).1 h) hi⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hpL : (Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) ∈ L := by
      rw [hL]
      intro j
      by_cases hj : j = Fin.last m
      · subst hj
        exact ⟨p, by simp, fun _ => dvd_refl _⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hcoef_low : ∀ i, i ≠ Fin.last m → (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      intro i hi
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ (hsingle i hi))
      rw [hu_apply]
      convert h using 2 with j
      congr 2
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcoef_last : _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) *
        (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) (Fin.last m) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ hpL)
      rw [hu_apply, Finset.mul_sum]
      convert h using 2 with j
      have hc : ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a))) j =
          (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j (Fin.last m) *
            _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E) := by
        have hv' : (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a)) =
            Pi.single (Fin.last m) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) := by
          funext a
          by_cases ha : a = Fin.last m
          · subst ha
            simp
          · simp [ha]
        rw [hv']
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hc, map_mul]
      have hs : _root_.Formalism.UG.sigR σ (w.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) =
          _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) := by
        unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE
        simp
      rw [hs]
      ring
    have hd_single : ∀ i, (Pi.single i 1 : Fin (m + 1) → E) ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x _ ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hr, _⟩ := (hL x).1 hx i
      have hc : σ (r : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ r
      rw [hform_one_apply]
      simpa [Pi.single_apply, hr] using hc
    have hq : σ (p : E) ≠ 0 := by
      intro h
      apply hp
      have h' : (p : E) = 0 := σ.injective (h.trans (map_zero σ).symm)
      exact_mod_cast h'
    set e0 : Fin (m + 1) → E := Pi.single (Fin.last m) (σ (p : E))⁻¹ with he0_def
    have he0 : e0 ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x e0 ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hxr, hdiv⟩ := (hL x).1 hx (Fin.last m)
      obtain ⟨c, rfl⟩ := hdiv (by simp)
      rw [hform_one_apply]
      have hc : σ (c : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ c
      have key : σ (x (Fin.last m)) * (σ (p : E))⁻¹ = σ (c : E) := by
        rw [hxr]
        push_cast
        rw [map_mul]
        field_simp
      simpa [he0_def, Pi.single_apply, key] using hc
    let d : Fin (m + 1) → Fin (m + 1) → E := fun i => if i = Fin.last m then e0 else Pi.single i 1
    have hd : ∀ i, d i ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      by_cases h : i = Fin.last m
      · simp only [d, h, if_true]
        exact he0
      · simp only [d, h, if_false]
        exact hd_single i
    let c : Fin (m + 1) → _root_.Formalism.BasicNotions.intV (F := F) E w := fun i =>
      if h : i = Fin.last m then ⟨_, hcoef_last⟩ else ⟨_, hcoef_low i h⟩
    have hsum : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v =
        ∑ i, c i • (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (d i a)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · by_cases hk : k = Fin.last m
        · subst hk
          simp only [c, d, dif_pos, if_pos, Pi.smul_apply, Subring.smul_def, smul_eq_mul, he0_def,
            Pi.single_eq_same]
          rw [mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
        · simp [c, d, hk, Subring.smul_def]
      · intro b _ hb
        by_cases hbl : b = Fin.last m
        · subst hbl
          simp [c, d, he0_def, Pi.single_apply, Ne.symm hb, Subring.smul_def]
        · simp [c, d, hbl, Pi.single_apply, Ne.symm hb, Subring.smul_def]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨d i, Submodule.subset_span (hd i), rfl⟩)

end GlobalTheory.Mem.LevDual
