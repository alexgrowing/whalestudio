import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlace

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
open Formalism.UG.P

namespace GlobalTheory.St.G.InkLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem prV_algebraMap (v : HeightOneSpectrum (𝓞 F)) (c : F) :
    prV (E := E) v (algebraMap F (E ⊗[F] Ad F) c) = algebraMap F (E ⊗[F] v.adicCompletion F) c := (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v)).commutes c

theorem unit_mem (w : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∉ w.asIdeal) :
    algebraMap F (E ⊗[F] w.adicCompletion F) ((g : F)⁻¹) ∈ intV E w := by
  have h2 : w.valuation F (g : F) = 1 := by
    have h3 : algebraMap (𝓞 F) F (g : 𝓞 F) = (g : F) := map_natCast _ g
    rw [← h3, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hg
  have hw : algebraMap F (w.adicCompletion F) ((g : F)⁻¹) ∈ w.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : Valued.v (algebraMap F (w.adicCompletion F) ((g : F)⁻¹)) = w.valuation F ((g : F)⁻¹) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, map_inv₀, h2, inv_one]
  rw [Algebra.TensorProduct.algebraMap_apply']
  exact Subring.subset_closure (Or.inr ⟨⟨_, hw⟩, rfl⟩)

theorem finite_places (d : 𝓞 F) (hd : d ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | d ∈ v.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd)
  refine h.subset fun v hv => ?_
  show v.asIdeal ∣ Ideal.span {d}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

omit [NumberField E] in
theorem prV_sum_IE [DecidableEq (HeightOneSpectrum (𝓞 F))] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ∀ v : HeightOneSpectrum (𝓞 F), E ⊗[F] v.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∈ S) :
    prV (E := E) w (∑ v ∈ S, afsplitIE v (u v)) = u w := by
  rw [map_sum, Finset.sum_eq_single w]
  · exact afsplit_prV_IE w (u w)
  · intro v _ hvw
    exact afsplit_prV_IE_ne v w (Ne.symm hvw) (u v)
  · intro h
    exact absurd hw h

omit [NumberField E] in
theorem prV_sum_IE_not (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ∀ v : HeightOneSpectrum (𝓞 F), E ⊗[F] v.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) :
    prV (E := E) w (∑ v ∈ S, afsplitIE v (u v)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun v hv => afsplit_prV_IE_ne v w (fun h => hw (h ▸ hv)) (u v)

private theorem prV_mem_of_mem_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v := by
  have ha' : a ∈ Subring.closure (Set.range (fun x : intOE E => (x : E) ⊗ₜ[F] (1 : Ad F)) ∪
      Set.range (fun z : intAd F => (1 : E) ⊗ₜ[F] (z : Ad F))) := ha
  have hle : Subring.closure (Set.range (fun x : intOE E => (x : E) ⊗ₜ[F] (1 : Ad F)) ∪
      Set.range (fun z : intAd F => (1 : E) ⊗ₜ[F] (z : Ad F))) ≤ (intV E v).comap (prV (E := E) v) := by
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨z, hz⟩, rfl⟩)
    · show prV (E := E) v ((x : E) ⊗ₜ[F] (1 : Ad F)) ∈ intV E v
      rw [afsplit_prV_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, by rw [afsplit_one_apply]⟩)
    · show prV (E := E) v ((1 : E) ⊗ₜ[F] z) ∈ intV E v
      rw [afsplit_prV_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨z v, hz v⟩, rfl⟩)
  exact hle ha'

theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (b : Fin k → Fin n → E ⊗[F] Ad F) (T : Set (Fin k))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) (b '' T)) :
    prVec v x ∈ Submodule.span (intV E v) ((fun j => prVec v (b j)) '' T) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  | zero =>
    have h0 : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
      funext i
      simp [prVec]
    rw [h0]
    exact Submodule.zero_mem _
  | add z w _ _ hz hw =>
    have h0 : prVec v (z + w) = prVec v z + prVec v w := by
      funext i
      simp [prVec]
    rw [h0]
    exact Submodule.add_mem _ hz hw
  | smul c z _ hz =>
    have h0 : prVec v (c • z) = (⟨prV (E := E) v c, prV_mem_of_mem_OAd v c.2⟩ : intV E v) • prVec v z := by
      funext i
      show prV (E := E) v ((c : E ⊗[F] Ad F) * z i) = prV (E := E) v c * prV (E := E) v (z i)
      exact map_mul _ _ _
    rw [h0]
    exact Submodule.smul_mem _ _ hz

private theorem afsplitIE_mem_OAd' (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ intV E v) : afsplitIE v a ∈ OAd F E := by
  have ha' : a ∈ Subring.closure (Set.range (fun x : intOE E => (x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∪
      Set.range (fun z : (v.adicCompletionIntegers F).toSubring => (1 : E) ⊗ₜ[F] (z : v.adicCompletion F))) := ha
  have hone : afsplitI v (1 : v.adicCompletion F) ∈ intAd F := afsplitI_mem_intAd v 1 (one_mem _)
  clear ha
  induction ha' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨z, hz⟩, rfl⟩
    · show afsplitIE v ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ OAd F E
      rw [afsplitIE_tmul]
      have hsplit : ((x : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F) : E ⊗[F] Ad F) =
          ((x : E) ⊗ₜ[F] (1 : Ad F)) * ((1 : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨_, hone⟩, rfl⟩))
    · show afsplitIE v ((1 : E) ⊗ₜ[F] (z : v.adicCompletion F)) ∈ OAd F E
      rw [afsplitIE_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨_, afsplitI_mem_intAd v z hz⟩, rfl⟩)
  | zero =>
    rw [map_zero]
    exact Subring.zero_mem _
  | one =>
    rw [Algebra.TensorProduct.one_def, afsplitIE_tmul]
    exact Subring.subset_closure (Or.inr ⟨⟨_, hone⟩, rfl⟩)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Subring.add_mem _ hx hy
  | neg x _ hx =>
    rw [map_neg]
    exact Subring.neg_mem _ hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact Subring.mul_mem _ hx hy

theorem IE_span (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (b : Fin k → Fin n → E ⊗[F] Ad F) (T : Set (Fin k))
    {s : Fin n → E ⊗[F] v.adicCompletion F}
    (hs : s ∈ Submodule.span (intV E v) ((fun j => prVec v (b j)) '' T)) :
    (fun i => afsplitIE v (s i)) ∈ Submodule.span (OAd F E) (b '' T) := by
  induction hs using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    have h0 : (fun i => afsplitIE v (prVec v (b j) i)) =
        (⟨afsplitEps E v, afsplitIE_mem_OAd' v (Subring.one_mem _)⟩ : OAd F E) • b j := by
      funext i
      show afsplitIE v (prV (E := E) v (b j i)) = afsplitEps E v * b j i
      exact afsplit_decomp v (b j i)
    show (fun i => afsplitIE v (prVec v (b j) i)) ∈ _
    rw [h0]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  | zero =>
    have h0 : (fun i => afsplitIE v ((0 : Fin n → E ⊗[F] v.adicCompletion F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact Submodule.zero_mem _
  | add z w _ _ hz hw =>
    have h0 : (fun i => afsplitIE v ((z + w) i)) =
        (fun i => afsplitIE v (z i)) + (fun i => afsplitIE v (w i)) := by
      funext i
      simp
    rw [h0]
    exact Submodule.add_mem _ hz hw
  | smul c z _ hz =>
    have h0 : (fun i => afsplitIE v ((c • z) i)) =
        (⟨afsplitIE v c, afsplitIE_mem_OAd' v c.2⟩ : OAd F E) • (fun i => afsplitIE v (z i)) := by
      funext i
      show afsplitIE v ((c : E ⊗[F] v.adicCompletion F) * z i) = afsplitIE v c * afsplitIE v (z i)
      exact map_mul _ _ _
    rw [h0]
    exact Submodule.smul_mem _ _ hz

theorem inv_mul_natCast (R : Type) [CommRing R] [Algebra F R] (g : ℕ) (hg : g ≠ 0) :
    algebraMap F R ((g : F)⁻¹) * (g : R) = 1 := by
  rw [← map_natCast (algebraMap F R) g, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hg), map_one]

theorem hat_glue (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) {k : ℕ} (b : Fin k → Fin n → E ⊗[F] Ad F)
    (T : Set (Fin k)) (g : ℕ) (hg : g ≠ 0) {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ w, w ∉ S → (g : 𝓞 F) ∉ w.asIdeal)
    (h : ∀ v ∈ S, InModL (loc v L) g ((fun j => prVec v (b j)) '' T) (prVec v x)) :
    InModL (hat F L) g (b '' T) x := by
  classical
  simp only [InModL] at h ⊢
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ s : Fin n → E ⊗[F] v.adicCompletion F,
      ∃ z : Fin n → E ⊗[F] v.adicCompletion F, v ∈ S →
        (s ∈ Submodule.span (intV E v) ((fun j => prVec v (b j)) '' T) ∧ z ∈ loc v L ∧
          prVec v x = s + (g : E ⊗[F] v.adicCompletion F) • z) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨s, hs, z, hz, e⟩ := h v hv
      exact ⟨s, z, fun _ => ⟨hs, hz, e⟩⟩
    · exact ⟨0, 0, fun h => absurd h hv⟩
  choose sv zv hsz using h'
  obtain ⟨s, hs_def⟩ : ∃ s : Fin n → E ⊗[F] Ad F, s = ∑ v ∈ S, fun i => afsplitIE v (sv v i) := ⟨_, rfl⟩
  have hs : s ∈ Submodule.span (OAd F E) (b '' T) := by
    rw [hs_def]
    exact Submodule.sum_mem _ fun v hv => IE_span v b T (hsz v hv).1
  have hsw : ∀ w, prVec w s = if w ∈ S then sv w else 0 := by
    intro w
    funext i
    rw [hs_def]
    simp only [prVec, Finset.sum_apply]
    split_ifs with hw
    · exact prV_sum_IE S (fun v => sv v i) w hw
    · exact prV_sum_IE_not S (fun v => sv v i) w hw
  have hxloc := (GlobalTheory.St.G.mem_hat_iff_forall_loc F E n L hL x).mp hx
  refine ⟨s, hs, fun i => algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * (x i - s i), ?_, ?_⟩
  · rw [GlobalTheory.St.G.mem_hat_iff_forall_loc F E n L hL]
    intro w
    have hpz : prVec w (fun i => algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * (x i - s i)) =
        fun i => algebraMap F (E ⊗[F] w.adicCompletion F) ((g : F)⁻¹) * (prVec w x i - prVec w s i) := by
      funext i
      simp only [prVec, map_mul, map_sub, prV_algebraMap]
    rw [hpz, hsw w]
    split_ifs with hw
    · obtain ⟨_, hz, e⟩ := hsz w hw
      have hz' : (fun i => algebraMap F (E ⊗[F] w.adicCompletion F) ((g : F)⁻¹) * (prVec w x i - sv w i)) = zv w := by
        funext i
        have ei := congrFun e i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ei
        rw [ei, add_sub_cancel_left, ← mul_assoc, inv_mul_natCast _ g hg, one_mul]
      rw [hz']
      exact hz
    · have hz' : (fun i => algebraMap F (E ⊗[F] w.adicCompletion F) ((g : F)⁻¹) *
          (prVec w x i - (0 : Fin n → E ⊗[F] w.adicCompletion F) i)) =
          (⟨_, unit_mem w g (hS w hw)⟩ : intV E w) • prVec w x := by
        funext i
        show _ = algebraMap F (E ⊗[F] w.adicCompletion F) ((g : F)⁻¹) * prVec w x i
        rw [Pi.zero_apply, sub_zero]
      rw [hz']
      exact Submodule.smul_mem _ _ (hxloc w)
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm (g : E ⊗[F] Ad F) (algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹)),
      inv_mul_natCast _ g hg, one_mul]
    abel

theorem prVec_sub_one (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F)) (x : Fin n → E ⊗[F] Ad F) :
    ((bc (prV (E := E) v) y).1 - 1) *ᵥ prVec v x = prVec v ((y.1 - 1) *ᵥ x) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, ← Carry.prVec_mulVec]
  funext i
  simp [prVec]

theorem hform_add_right {A : Type} [CommRing A] {ι : Type} [Fintype ι] (τ : A →+* A)
    (J : Matrix ι ι A) (x u w : ι → A) : hform τ J x (u + w) = hform τ J x u + hform τ J x w := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {ι : Type} [Fintype ι] (τ : A →+* A)
    (J : Matrix ι ι A) (a : A) (x u : ι → A) : hform τ J x (a • u) = a * hform τ J x u := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_incl (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hR σ J (Ad F) (fun i => inclE (F := F) (Ad F) (x i)) (fun i => inclE (F := F) (Ad F) (y i)) =
      inclE (F := F) (Ad F) (hform (σ : E →+* E) J x y) := by
  have key : ∀ e : E, sigR σ (Ad F) (inclE (F := F) (Ad F) e) = inclE (F := F) (Ad F) (σ e) := by
    intro e
    simp [sigR, inclE]
  simp only [hR, hform, map_sum, map_mul, Matrix.map_apply, key]
  rfl

private theorem sigR_mem_intAE' (σ : E →ₐ[F] E) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    sigR σ (Ad F) a ∈ OAd F E := by
  have ha' : a ∈ Subring.closure (Set.range (fun x : intOE E => (x : E) ⊗ₜ[F] (1 : Ad F)) ∪
      Set.range (fun z : intAd F => (1 : E) ⊗ₜ[F] (z : Ad F))) := ha
  have hle : Subring.closure (Set.range (fun x : intOE E => (x : E) ⊗ₜ[F] (1 : Ad F)) ∪
      Set.range (fun z : intAd F => (1 : E) ⊗ₜ[F] (z : Ad F))) ≤ (OAd F E).comap (sigR σ (Ad F)) := by
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨z, hz⟩, rfl⟩)
    · obtain ⟨e, rfl⟩ := hx
      show sigR σ (Ad F) ((algebraMap (𝓞 E) E e) ⊗ₜ[F] (1 : Ad F)) ∈ OAd F E
      have hσ : σ (algebraMap (𝓞 E) E e) ∈ intOE E :=
        ⟨NumberField.RingOfIntegers.mapRingHom (σ : E →+* E) e, rfl⟩
      have h1 : sigR σ (Ad F) ((algebraMap (𝓞 E) E e) ⊗ₜ[F] (1 : Ad F)) =
          (σ (algebraMap (𝓞 E) E e)) ⊗ₜ[F] (1 : Ad F) := rfl
      rw [h1]
      exact Subring.subset_closure (Or.inl ⟨⟨_, hσ⟩, rfl⟩)
    · show sigR σ (Ad F) ((1 : E) ⊗ₜ[F] (z : Ad F)) ∈ OAd F E
      have h1 : sigR σ (Ad F) ((1 : E) ⊗ₜ[F] (z : Ad F)) = (σ 1) ⊗ₜ[F] (z : Ad F) := rfl
      rw [h1, map_one]
      exact Subring.subset_closure (Or.inr ⟨⟨z, hz⟩, rfl⟩)
  exact hle ha'

private theorem hform_add_left_flag_measures {A : Type} [CommRing A] {ι : Type} [Fintype ι] (τ : A →+* A)
    (J : Matrix ι ι A) (u w x : ι → A) : hform τ J (u + w) x = hform τ J u x + hform τ J w x := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem hform_smul_left_flag_measures' {A : Type} [CommRing A] {ι : Type} [Fintype ι] (τ : A →+* A)
    (J : Matrix ι ι A) (a : A) (u x : ι → A) : hform τ J (a • u) x = τ a * hform τ J u x := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_mem (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) {a b : Fin n → E ⊗[F] Ad F}
    (ha : a ∈ hat F L) (hb : b ∈ hat F L) : hR σ J (Ad F) a b ∈ OAd F E := by
  induction hb using Submodule.span_induction with
  | mem b' hb' =>
    obtain ⟨y', hy', rfl⟩ := hb'
    induction ha using Submodule.span_induction with
    | mem a' ha' =>
      obtain ⟨x', hx', rfl⟩ := ha'
      show hR σ J (Ad F) (fun i => inclE (F := F) (Ad F) (x' i)) (fun i => inclE (F := F) (Ad F) (y' i)) ∈ OAd F E
      rw [hR_incl]
      exact Subring.subset_closure (Or.inl ⟨⟨_, hint y' hy' x' hx'⟩, rfl⟩)
    | zero =>
      simp only [hR, hform, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact Subring.zero_mem _
    | add a1 a2 _ _ h1 h2 =>
      simp only [hR] at h1 h2 ⊢
      rw [hform_add_left_flag_measures]
      exact Subring.add_mem _ h1 h2
    | smul c a1 _ h1 =>
      simp only [hR] at h1 ⊢
      rw [Subring.smul_def, hform_smul_left_flag_measures']
      exact Subring.mul_mem _ (sigR_mem_intAE' σ c.2) h1
  | zero =>
    simp only [hR, hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact Subring.zero_mem _
  | add b1 b2 _ _ h1 h2 =>
    simp only [hR] at h1 h2 ⊢
    rw [hform_add_right]
    exact Subring.add_mem _ h1 h2
  | smul c b1 _ h1 =>
    simp only [hR] at h1 ⊢
    rw [Subring.smul_def, hform_smul_right]
    exact Subring.mul_mem _ c.2 h1

theorem prV_hR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    prV (E := E) v (hR σ J (Ad F) x y) = hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) := by
  have key : ∀ a, prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
    fun a => RingHom.congr_fun (afsplit_prV_comp_sigR σ v) a
  simp only [hR, hform, map_sum, map_mul, Matrix.map_apply, key, afsplit_prV_inclE, prVec]

theorem prV_supSum (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}
    (b bd : Fin k → Fin n → E ⊗[F] Ad F) (y : GL (Fin n) (E ⊗[F] Ad F)) :
    prV (E := E) v (supSum (hR σ J (Ad F)) b bd y.1) =
      supSum (hR σ J (v.adicCompletion F)) (fun j => prVec v (b j)) (fun j => prVec v (bd j))
        (bc (prV (E := E) v) y).1 := by
  unfold supSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [prV_hR, Carry.prVec_mulVec]
  · exact map_zero _

section Frame

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {gp : Fin 2 → ℕ}
  {L : Submodule (𝓞 E) (Fin n → E)}

theorem mem_prod_iff (v : HeightOneSpectrum (𝓞 F)) :
    ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ ∃ i : Fin 2, (gp i : 𝓞 F) ∈ v.asIdeal := by
  rw [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, Fin.exists_fin_two]

theorem not_both (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) (v : HeightOneSpectrum (𝓞 F))
    (h0 : (gp 0 : 𝓞 F) ∈ v.asIdeal) (h1 : (gp 1 : 𝓞 F) ∈ v.asIdeal) : False := by
  have hc : Nat.Coprime (gp 0) (gp 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  have h := Nat.gcd_eq_gcd_ab (gp 0) (gp 1)
  rw [hc.gcd_eq_one] at h
  have h' := congrArg (Int.cast : ℤ → 𝓞 F) h
  push_cast at h'
  have hone : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [h']
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h0) (v.asIdeal.mul_mem_right _ h1)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem cast_ne_zero' (g : ℕ) (hg : g ≠ 0) : (g : 𝓞 F) ≠ 0 := by
  intro h
  apply hg
  simpa using congrArg (algebraMap (𝓞 F) F) h

theorem cond_local (Fr : AdFrame σ J (hat F L) (gp 0 * gp 1) k) (hp : ∀ i, (gp i).Prime)
    (hL : IsLat L) (y : GL (Fin n) (E ⊗[F] Ad F)) (hy : y ∈ stabGL (hat F L)) :
    (∀ i : Fin k, InModL (hat F L) (gp 0 * gp 1) (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)) ↔
      ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK L v (bc (prV (E := E) v) y) := by
  have hg0 : gp 0 * gp 1 ≠ 0 := Nat.mul_ne_zero (hp 0).ne_zero (hp 1).ne_zero
  constructor
  · intro h i' v _ i
    obtain ⟨s, hs, z, hz, hxz⟩ := h i
    refine ⟨prVec v s, prVec_span v Fr.b _ hs, prVec v z, ?_, ?_⟩
    · exact (GlobalTheory.St.G.mem_hat_iff_forall_loc F E n L hL z).mp hz v
    · rw [prVec_sub_one, hxz]
      funext j
      simp [prVec]
  · intro h i
    have hy' : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F L := hy
    have hbi : (y.1 - 1) *ᵥ Fr.b i ∈ hat F L := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Submodule.sub_mem _ ((hy' (Fr.b i)).mp (Fr.b_mem i)) (Fr.b_mem i)
    have hfin := finite_places (F := F) _ (cast_ne_zero' _ hg0)
    refine hat_glue L hL Fr.b {j | j.1 < i.1} (gp 0 * gp 1) hg0 hbi hfin.toFinset ?_ ?_
    · intro w hw h'
      exact hw (hfin.mem_toFinset.mpr h')
    · intro v hv
      obtain ⟨i', hi'⟩ := (mem_prod_iff v).mp (hfin.mem_toFinset.mp hv)
      have hl := h i' v hi' i
      rwa [prVec_sub_one] at hl

theorem psi_sum (Fr : AdFrame σ J (hat F L) (gp 0 * gp 1) k) {ι : Type} (S : Finset ι)
    (u : ι → E ⊗[F] Ad F) : Fr.psi (∑ v ∈ S, u v) = ∏ v ∈ S, Fr.psi (u v) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simpa using Fr.psi_int 0 (Subring.zero_mem _)
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Fr.psi_add, ih]

theorem chi_local (Fr : AdFrame σ J (hat F L) (gp 0 * gp 1) k) (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1)
    (hint : ∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) (y : GL (Fin n) (E ⊗[F] Ad F))
    (hy : y ∈ stabGL (hat F L)) :
    Fr.chi y = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal),
      Fr.locChi v (bc (prV (E := E) v) y) := by
  classical
  have hg0 : gp 0 * gp 1 ≠ 0 := Nat.mul_ne_zero (hp 0).ne_zero (hp 1).ne_zero
  have hfin := finite_places (F := F) _ (cast_ne_zero' _ hg0)
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S = hfin.toFinset := ⟨_, rfl⟩
  have hmemS : ∀ v, v ∈ S ↔ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    intro v
    rw [hS, hfin.mem_toFinset]
    rfl
  have hy' : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F L := hy
  obtain ⟨a, ha⟩ : ∃ a : E ⊗[F] Ad F, a = algebraMap F (E ⊗[F] Ad F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) *
      supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1 := ⟨_, rfl⟩
  have hloc : ∀ v, Fr.locChi v (bc (prV (E := E) v) y) = Fr.psi (afsplitEps E v * a) := by
    intro v
    rw [AdFrame.locChi, ← prV_supSum σ J v Fr.b Fr.bd y,
      ← prV_algebraMap (E := E) v (((gp 0 * gp 1 : ℕ) : F)⁻¹), ← map_mul, ← ha, afsplit_decomp]
  have hsup : supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1 ∈ OAd F E := by
    unfold supSum
    refine Subring.sum_mem _ fun i _ => ?_
    split_ifs with hi
    · exact hR_mem σ J L hint (Fr.bd_mem i) ((hy' _).mp (Fr.b_mem _))
    · exact Subring.zero_mem _
  have hrest : (1 - ∑ v ∈ S, afsplitEps E v) * a ∈ OAd F E := by
    apply IntAd.mem_of_local
    intro w
    rw [map_mul, map_sub, map_one, map_sum]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hvw => afsplit_prV_eps_ne v w (Ne.symm hvw))
        (fun h => absurd hw h), afsplit_prV_eps, sub_self, zero_mul]
      exact Subring.zero_mem _
    · rw [Finset.sum_eq_zero (fun v hv => afsplit_prV_eps_ne v w (fun h => hw (h ▸ hv))), sub_zero, one_mul,
        ha, map_mul, prV_algebraMap]
      exact Subring.mul_mem _ (unit_mem w _ (fun h => hw ((hmemS w).mpr h))) (prV_mem_of_mem_OAd w hsup)
  have hsplit : a = ∑ v ∈ S, afsplitEps E v * a + (1 - ∑ v ∈ S, afsplitEps E v) * a := by
    rw [← Finset.sum_mul]
    ring
  have hchi : Fr.chi y = ∏ v ∈ S, Fr.locChi v (bc (prV (E := E) v) y) := by
    rw [AdFrame.chi, ← ha, hsplit, Fr.psi_add, psi_sum Fr S (fun v => afsplitEps E v * a),
      Fr.psi_int _ hrest, mul_one]
    exact Finset.prod_congr rfl fun v _ => (hloc v).symm
  have hcond : ∀ i : Fin 2, (∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal),
      Fr.locChi v (bc (prV (E := E) v) y)) =
      ∏ v ∈ S.filter (fun v => (gp i : 𝓞 F) ∈ v.asIdeal), Fr.locChi v (bc (prV (E := E) v) y) := by
    intro i
    apply finprod_cond_eq_prod_of_cond_iff
    intro v _
    rw [Finset.mem_filter, hmemS]
    exact ⟨fun h => ⟨(mem_prod_iff v).mpr ⟨i, h⟩, h⟩, fun h => h.2⟩
  rw [hchi, Fin.prod_univ_two, hcond 0, hcond 1,
    ← Finset.prod_filter_mul_prod_filter_not S (fun v => (gp 0 : 𝓞 F) ∈ v.asIdeal)]
  congr 1
  refine Finset.prod_congr (Finset.filter_congr fun v hv => ?_) fun _ _ => rfl
  have hv' := (mem_prod_iff v).mp ((hmemS v).mp hv)
  rw [Fin.exists_fin_two] at hv'
  constructor
  · intro h0n
    rcases hv' with h0' | h1'
    · exact absurd h0' h0n
    · exact h1'
  · intro h1 h0
    exact not_both hp hne v h0 h1

end Frame

end GlobalTheory.St.G.InkLoc

theorem GlobalTheory.St.G.frame_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k : ℕ) (gp : Fin 2 → ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → IsLat L → (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ y : GL (Fin n) (E ⊗[F] Ad F), y ∈ stabGL (hat F L) → ((∀ i : Fin k, InModL (hat F L) (gp 0 * gp 1) (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)) ↔ ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Fr.LocK L v (bc (prV (E := E) v) y)) ∧ Fr.chi y = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal), Fr.locChi v (bc (prV (E := E) v) y) := by
  intro F E _ _ _ _ _ _ cm n J _ _ k gp L Fr hp hne hL hint y hy
  exact ⟨GlobalTheory.St.G.InkLoc.cond_local Fr hp hL y hy, GlobalTheory.St.G.InkLoc.chi_local Fr hp hne hint y hy⟩
