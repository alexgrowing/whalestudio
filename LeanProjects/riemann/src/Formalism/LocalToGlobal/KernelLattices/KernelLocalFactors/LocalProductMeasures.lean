import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.AbsoluteValueInertPrimes
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.TwistComponentsCompatibleSystem
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.TwistValueAtUniformizer
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.XiProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HeckeCharacterCompatibleSystem
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MlZFacSupport
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HilbertNinetyNormOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.Columns.DetChrJoint

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace Formalism.L2.Ker
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem LocSys.mul' {A : Type} [CommGroup A] {l₁ l₂ : HeightOneSpectrum (𝓞 F) → Eˣ →* A} {R₁ R₂ R : Set (HeightOneSpectrum (𝓞 F))}
    (h₁ : LocSys l₁ R₁) (h₂ : LocSys l₂ R₂) (s₁ : R₁ ⊆ R) (s₂ : R₂ ⊆ R) : LocSys (fun v => l₁ v * l₂ v) R where
  wild v a h := by rw [MonoidHom.mul_apply, h₁.wild v a h, h₂.wild v a h, one_mul]
  trivF v k := by rw [MonoidHom.mul_apply, h₁.trivF v k, h₂.trivF v k, one_mul]
  unr v hv a h := by
    rw [MonoidHom.mul_apply, h₁.unr v (fun h' => hv (s₁ h')) a h, h₂.unr v (fun h' => hv (s₂ h')) a h, one_mul]

theorem LocSys.map' {A B : Type} [CommGroup A] [CommGroup B] {l : HeightOneSpectrum (𝓞 F) → Eˣ →* A} {R : Set (HeightOneSpectrum (𝓞 F))}
    (h : LocSys l R) (f : A →* B) : LocSys (fun v => f.comp (l v)) R where
  wild v a h' := by rw [MonoidHom.comp_apply, h.wild v a h', map_one]
  trivF v k := by rw [MonoidHom.comp_apply, h.trivF v k, map_one]
  unr v hv a h' := by rw [MonoidHom.comp_apply, h.unr v hv a h', map_one]

theorem OneAt.one (P : HeightOneSpectrum (𝓞 E)) : OneAt P (1 : E) := by
  unfold OneAt
  rw [sub_self, map_zero]
  exact zero_lt_one

theorem OneAt.pow {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) (n : ℕ) : OneAt P (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact OneAt.one P
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem OneAt.zpow {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) (n : ℤ) : OneAt P (a ^ n) := by
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact h.pow k
  | negSucc k => rw [zpow_negSucc]; exact (h.pow _).inv

theorem OneAt.of_mem {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (h : b - 1 ∈ P.asIdeal) : OneAt P (b : E) := by
  unfold OneAt
  have := (mh_val_mem (P := P) (b := b - 1)).2 h
  simpa using this

end Sys

section Key

variable {X : Fields}

theorem md_key (hX : X.Ok) {A : Type} [CommGroup A] {lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A} {Rm : Set (HeightOneSpectrum (𝓞 X.F))}
    (hL : LocSys lam Rm) {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (hPv : P.asIdeal.under (𝓞 X.F) = v.asIdeal)
    (hne : conjPrime₂ P ≠ P) (x w c : X.Eˣ) (n : ℤ) (hw : OneAt (conjPrime₂ P) (w : X.E)) (hc : OneAt (conjPrime₂ P) (c : X.E))
    (h : OneAt P ((w : X.E) ^ n * (c : X.E) / ((x : X.E) / star (x : X.E)))) : lam v x = lam v w ^ n * lam v c := by
  have := absolute_value_split_primes X hX A lam Rm hL v P hPv hne x (w ^ n * c)
    (by rw [Units.val_mul, Units.val_zpow_eq_zpow_val]; exact (hw.zpow n).mul hc)
    (by rw [Units.val_mul, Units.val_zpow_eq_zpow_val]; exact h)
  rw [this, map_mul, map_zpow]

theorem md_ordE_zpow {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) (n : ℤ) :
    ordE P (a ^ n) = n * ordE P a := by
  unfold ordE
  rw [map_zpow₀, WithZero.log_zpow]
  simp

theorem md_val_of_ordE {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) (h : ordE P a = 0) :
    P.valuation E a = 1 := by
  unfold ordE at h
  have h0 : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 : WithZero.log (P.valuation E a) = 0 := by omega
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem md_off (hX : X.Ok) {A : Type} [CommGroup A] {lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A} {Rm : Set (HeightOneSpectrum (𝓞 X.F))}
    (hL : LocSys lam Rm) {v : HeightOneSpectrum (𝓞 X.F)} (hv : v ∉ Rm) {P : HeightOneSpectrum (𝓞 X.E)} (hPv : P.asIdeal.under (𝓞 X.F) = v.asIdeal)
    (hne : conjPrime₂ P ≠ P) (x w : X.Eˣ) (hw : OneAt (conjPrime₂ P) (w : X.E)) (hw1 : P.valuation X.E (w : X.E) = WithZero.exp (-1 : ℤ)) :
    lam v x = lam v w ^ ordE P ((x : X.E) / star (x : X.E)) := by
  set z : X.E := (x : X.E) / star (x : X.E) with hz
  have hz0 : z ≠ 0 := div_ne_zero x.ne_zero (star_ne_zero.2 x.ne_zero)
  set n := ordE P z with hn
  have hu0 : z / (w : X.E) ^ n ≠ 0 := div_ne_zero hz0 (zpow_ne_zero _ w.ne_zero)
  obtain ⟨c, hc1, hc2⟩ := ab_reads P (conjPrime₂ P) hne.symm (Units.mk0 _ hu0)
  rw [Units.val_mk0] at hc1
  have hvu : P.valuation X.E (z / (w : X.E) ^ n) = 1 := by
    apply md_val_of_ordE P hu0
    rw [div_eq_mul_inv, ordE_mul P hz0 (inv_ne_zero (zpow_ne_zero _ w.ne_zero)), ← zpow_neg, md_ordE_zpow P,
      mh_ordE_unif (n := 1) hw1]
    omega
  have hcP : P.valuation X.E (c : X.E) = 1 := by
    have := hc1.val_eq_one
    rw [map_div₀, hvu, div_one] at this
    exact this
  have hk := md_key hX hL hPv hne x w c n hw hc2 (by
    have e : (w : X.E) ^ n * (c : X.E) / z = (c : X.E) / (z / (w : X.E) ^ n) := by
      field_simp
    rw [e]; exact hc1)
  rw [hk, hL.unr v hv c (fun P' hP' => by
    rcases local_factor_over_two X hX P P' (hP'.trans hPv.symm) with rfl | rfl
    · exact hcP
    · exact hc2.val_eq_one), mul_one]

end Key

section Conc

open Formalism.L2.Host
open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m)

variable (Pr) in

def RmOf : Set (HeightOneSpectrum (𝓞 X.F)) := {v | ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal}

def muLam (σ₀ : X.K →+* ℂ) (χ : HChar X.E) (ξ : Chr X.F X.E X.K) (v : HeightOneSpectrum (𝓞 X.F)) : X.Eˣ →* ℂˣ :=
  lamH χ v * (Units.map σ₀.toMonoidHom).comp (lamX ξ v)

theorem md_vG_sub (i : Fin 2) {Q : HeightOneSpectrum (𝓞 X.E)} (h : Q ∈ Pr.vG i) : Q ∈ Pr.vGs := by
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

theorem md_g_mem (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} {i : Fin 2} (h : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal) :
    P ∈ Pr.vGs ∨ conjPrime₂ P ∈ Pr.vGs := by
  rw [← hPr.piG_norm i] at h
  rcases P.isPrime.mem_or_mem h with h1 | h1
  · right
    refine md_vG_sub i ((mem_divs (ciConjPiG_ne_zero hPr i) _).2 ?_)
    rw [mem_conjP]
    show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal
    rw [cO_cO]
    exact h1
  · left
    exact md_vG_sub i ((mem_divs (ciConjPiG_ne_zero hPr i) _).2 h1)

theorem md_conj_eq (P : HeightOneSpectrum (𝓞 X.E)) : HeckeExHost.conjPrime₂ P = conjPrime₂ P := HeightOneSpectrum.ext rfl

variable {sel mu}

theorem md_mem_Rm {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : P.asIdeal.under (𝓞 X.F) = v.asIdeal) : v ∈ RmOf Pr sel mu := ⟨P, hP, hv⟩

theorem md_no_g (hX : X.Ok) (hPr : Pr.Ok) {v : HeightOneSpectrum (𝓞 X.F)} (hv : v ∉ RmOf Pr sel mu) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P.asIdeal.under (𝓞 X.F) = v.asIdeal) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  intro h
  rcases md_g_mem hPr h with h1 | h1
  · exact hv (md_mem_Rm (Finset.mem_union_left _ h1) hP)
  · exact hv (md_mem_Rm (Finset.mem_union_left _ h1) ((ab_conjP_under X hX P).trans hP))

theorem md_Q_sub (hsel : IsSel X sel) : Qprime (mu : Chr X.F X.E X.K) ⊆ RmOf Pr sel mu := fun v hv =>
  md_mem_Rm (Finset.mem_union_right _ ((mem_QE sel mu _).2 ⟨v, hv, rfl⟩)) (hsel v)

theorem md_sys (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin R.m} {χ : HChar X.E}
    (hχ : IsMu0 Ch σ₀ e j χ) : LocSys (muLam σ₀ χ (mu : Chr X.F X.E X.K)) (RmOf Pr sel mu) :=
  LocSys.mul' (hecke_character_compatible_system X.F X.E χ (RmOf Pr sel mu) hχ.tame hχ.triv fun _ hv _ hP => hχ.unr _ (md_no_g hX hPr hv hP))
    ((twist_components_compatible_system X.F X.E X.K S mu).map' _) (le_refl _) (md_Q_sub hsel)

theorem md_split (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : conjPrime₂ P ≠ P := by
  rcases Finset.mem_union.1 hP with h | h
  · rw [← md_conj_eq]
    exact (DetChrL.conjP_vGs hX hPr h).1
  · obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).1 h
    obtain ⟨⟨P1, P2, hne, hsp⟩, -, -⟩ := mu.good hv
    intro hc
    have hov : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → Q = sel v := by
      intro Q hQ
      have h1 : v.asIdeal ≤ Q.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := Ideal.map_le_iff_le_comap.1 hQ
      have h2 : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) :=
        v.isMaximal.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) h1
      rcases local_factor_over_two X hX (sel v) Q (h2.symm.trans (hsel v).symm) with h3 | h3
      · exact h3
      · rw [h3, hc]
    exact hne ((hov P1 (hsp ▸ Ideal.mul_le_left)).trans (hov P2 (hsp ▸ Ideal.mul_le_right)).symm)

theorem md_inj (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) {P P' : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ rowSG Pr sel mu) (hP' : P' ∈ rowSG Pr sel mu) (h : P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)) : P' = P := by
  have key : ∀ Q Q' : HeightOneSpectrum (𝓞 X.E), Q ∈ Pr.vGs → Q' ∈ QE sel (mu : Chr X.F X.E X.K) →
      Q'.asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) → False := by
    intro Q Q' hQ hQ' hh
    obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu Q').1 hQ'
    exact hg Q hQ v (hh.symm.trans (hsel v)) hv
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  · rcases local_factor_over_two X hX P P' h with h3 | h3
    · exact h3
    · exfalso
      rw [h3, ← md_conj_eq] at h2
      exact (DetChrL.conjP_vGs hX hPr h1).2 h2
  · exact (key P P' h1 h2 h).elim
  · exact (key P' P h2 h1 h.symm).elim
  · obtain ⟨v, _, rfl⟩ := (mem_QE sel mu P).1 h1
    obtain ⟨v', _, rfl⟩ := (mem_QE sel mu P').1 h2
    rw [hsel v, hsel v'] at h
    rw [HeightOneSpectrum.ext h]

theorem md_coe_ne {E : Type} [Field E] [NumberField E] {b : 𝓞 E} (h : b ≠ 0) : (b : E) ≠ 0 := by
  simpa using h

theorem md_fac_off (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) {σ₀ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta : HChar X.E}
    (hT : Ch.Tied σ₀ e m0 eta) (i : ℕ) (hi : i < R.m) (x : X.Eˣ) {v : HeightOneSpectrum (𝓞 X.F)} (hv : v ∉ RmOf Pr sel mu) :
    σ₀ (zFac sel (rowSG Pr sel mu) (mUof Ch mu i) ((x : X.E) / star (x : X.E)) v) =
      (((muLam σ₀ (m0 ⟨i, hi⟩) (mu : Chr X.F X.E X.K) v x)⁻¹ : ℂˣ) : ℂ) := by
  have hsys := md_sys (Ch := Ch) (sel := sel) (mu := mu) hX.ok hPr hsel (hT.mu0 ⟨i, hi⟩)
  unfold zFac
  rw [if_neg (show ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal from hv)]
  by_cases hc : conjPrime₂ (sel v) = sel v
  · rw [absolute_value_inert_primes X hX.ok ℂˣ _ _ hsys v (sel v) (hsel v) hc hv (hX.unram (sel v)) x]
    have h1 : (sel v).valuation X.E (star (x : X.E)) = (sel v).valuation X.E (x : X.E) := by
      have := ab_val_star (sel v) (x : X.E)
      rwa [hc] at this
    have h2 : ordE (sel v) ((x : X.E) / star (x : X.E)) = 0 := by
      apply mh_ordE_unif
      rw [map_div₀, h1, div_self ((Valuation.ne_zero_iff _).2 x.ne_zero)]
      simp
    rw [h2]
    simp
  · obtain ⟨t, ht1, ht2⟩ := Ideal.exists_mem_pow_notMem_pow_succ (sel v).asIdeal (sel v).ne_bot (sel v).isPrime.ne_top 1
    rw [pow_one] at ht1
    obtain ⟨b, hb0, hb1, hb2⟩ := prime_approximation_holds X.E (sel v) (conjPrime₂ (sel v)) (Ne.symm hc) t
    have hbP : b ∈ (sel v).asIdeal := by
      have := (sel v).asIdeal.add_mem (Ideal.pow_le_self two_ne_zero hb1) ht1
      rwa [sub_add_cancel] at this
    have hbP2 : b ∉ (sel v).asIdeal ^ 2 := by
      intro h
      apply ht2
      have := ((sel v).asIdeal ^ 2).sub_mem h hb1
      rwa [sub_sub_cancel] at this
    have hoth : ∀ P' : HeightOneSpectrum (𝓞 X.E), P' ≠ sel v → P'.asIdeal.under (𝓞 X.F) = v.asIdeal → P' = conjPrime₂ (sel v) := by
      intro P' h1 h2
      rcases local_factor_over_two X hX.ok (sel v) P' (h2.trans (hsel v).symm) with h3 | h3
      · exact absurd h3 h1
      · exact h3
    set w : X.Eˣ := Units.mk0 (b : X.E) (md_coe_ne hb0) with hw
    have hw1 : OneAt (conjPrime₂ (sel v)) (w : X.E) := OneAt.of_mem hb2
    have hw2 : (sel v).valuation X.E (w : X.E) = WithZero.exp (-1 : ℤ) := mh_val_unif hbP hbP2
    rw [md_off hX.ok hsys hv (hsel v) hc x w hw1 hw2]
    have hunr : (m0 ⟨i, hi⟩).UnrAt (sel v) := (hT.mu0 ⟨i, hi⟩).unr _ (md_no_g hX.ok hPr hv (hsel v))
    have e1 : lamH (F := X.F) (m0 ⟨i, hi⟩) v w = (m0 ⟨i, hi⟩).val (sel v) := by
      rw [hecke_character_evaluation X.F X.E _ (hT.mu0 ⟨i, hi⟩).tame v (sel v) (hsel v) w (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hw1)]
      exact (hecke_character_local_behaviour X.E _ (sel v)).2.2 hunr w hw2
    have e2 : lamX (mu : Chr X.F X.E X.K) v w = unifVal (mu : Chr X.F X.E X.K) (sel v) :=
      twist_value_at_uniformizer X.F X.E X.K S mu v (sel v) (hsel v) (fun h => hv (md_Q_sub hsel h)) w b rfl hbP hbP2
        (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hb2)
    have e3 : Units.map σ₀.toMonoidHom (mUof Ch mu i (sel v)) = (muLam σ₀ (m0 ⟨i, hi⟩) (mu : Chr X.F X.E X.K) v w)⁻¹ := by
      unfold muLam mUof
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, e1, e2, dif_pos hi, map_mul, map_inv, map_inv, mul_inv]
      congr 2
      apply Units.ext
      exact hT.muVal ⟨i, hi⟩ (sel v) (md_no_g hX.ok hPr hv (hsel v))
    rw [← inv_zpow, ← e3, ← map_zpow]
    rfl

end Conc

section Bad

open Formalism.L2.Host
open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem md_bad (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin R.m} {χ : HChar X.E}
    (hχ : IsMu0 Ch σ₀ e j χ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu)
    (hq2 : ((Col.qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) {v : HeightOneSpectrum (𝓞 X.F)} (hv : P.asIdeal.under (𝓞 X.F) = v.asIdeal)
    (x qu : X.Eˣ) (hqu : (qu : X.E) = ((Col.qOf P : ℕ) : X.E)) :
    ∃ (c : X.Eˣ) (c₀ : 𝓞 X.E), (c : X.E) = (c₀ : X.E) ∧
      Ideal.Quotient.mk P.asIdeal c₀ = redP P (((x : X.E) / star (x : X.E)) / ((Col.qOf P : ℕ) : X.E) ^ LocE.vP P (Col.qOf P) ((x : X.E) / star (x : X.E))) ∧
      c₀ - 1 ∈ (conjPrime₂ P).asIdeal ∧ P.valuation X.E (c : X.E) = 1 ∧
      muLam σ₀ χ (mu : Chr X.F X.E X.K) v x =
        (χ.locK P qu * Units.map σ₀.toMonoidHom (qVal (mu : Chr X.F X.E X.K) P)) ^ LocE.vP P (Col.qOf P) ((x : X.E) / star (x : X.E)) *
          (χ.locK P c * Units.map σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v c)) := by
  have hsys := md_sys (Ch := Ch) (sel := sel) (mu := mu) hX hPr hsel hχ
  have hne : conjPrime₂ P ≠ P := md_split hX hPr hsel hP
  have hq : ((Col.qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal := ciQ_mem P
  set q : ℕ := Col.qOf P with hqdef
  set z : X.E := (x : X.E) / star (x : X.E) with hz
  have hz0 : z ≠ 0 := div_ne_zero x.ne_zero (star_ne_zero.2 x.ne_zero)
  set n : ℤ := LocE.vP P q z with hn
  have hu : IsUnit (redP P (z / (q : X.E) ^ n)) := isUnit_div_pow_valuation q hq hq2 z hz0
  have hq0 : (q : X.E) ≠ 0 := ciQ_ne_zero hq2
  have hoth : ∀ P' : HeightOneSpectrum (𝓞 X.E), P' ≠ P → P'.asIdeal.under (𝓞 X.F) = v.asIdeal → P' = conjPrime₂ P := by
    intro P' h1 h2
    rcases local_factor_over_two X hX P P' (h2.trans hv.symm) with h3 | h3
    · exact absurd h3 h1
    · exact h3
  obtain ⟨b, hb0, hb1, hb2⟩ := prime_approximation_holds X.E P (conjPrime₂ P) (Ne.symm hne) ((q : ℕ) : 𝓞 X.E)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (redP P (z / (q : X.E) ^ n))
  obtain ⟨c₀, hc0, hc1, hc2⟩ := prime_approximation_holds X.E P (conjPrime₂ P) (Ne.symm hne) t
  have hmk : Ideal.Quotient.mk P.asIdeal c₀ = redP P (z / (q : X.E) ^ n) := by
    rw [← ht]
    exact Ideal.Quotient.eq.2 (Ideal.pow_le_self two_ne_zero hc1)
  set w : X.Eˣ := Units.mk0 (b : X.E) (md_coe_ne hb0) with hw
  set c : X.Eˣ := Units.mk0 (c₀ : X.E) (md_coe_ne hc0) with hc
  have hvq : P.valuation X.E (q : X.E) = WithZero.exp (-1 : ℤ) := by
    have := mh_val_unif hq hq2
    simpa using this
  have hvu : P.valuation X.E (z / (q : X.E) ^ n) = 1 := mh_val_unit hu
  have hIu : IntAt P (z / (q : X.E) ^ n) := intAt_of_redP_ne_zero₂ hu.ne_zero

  have hwq : OneAt P ((w : X.E) / (q : X.E)) := by
    unfold OneAt
    have e1 : (w : X.E) / (q : X.E) - 1 = (((b - ((q : ℕ) : 𝓞 X.E) : 𝓞 X.E)) : X.E) / (q : X.E) := by
      rw [hw, Units.val_mk0]
      push_cast
      field_simp
    rw [e1, map_div₀, hvq]
    refine (div_lt_one₀ (by simp)).2 (lt_of_le_of_lt (mh_val_sq hb1) ?_)
    exact WithZero.exp_lt_exp.2 (by norm_num)

  have hcu : OneAt P ((c : X.E) / (z / (q : X.E) ^ n)) := by
    unfold OneAt
    have hu0 : z / (q : X.E) ^ n ≠ 0 := div_ne_zero hz0 (zpow_ne_zero _ hq0)
    have e1 : (c : X.E) / (z / (q : X.E) ^ n) - 1 = ((c₀ : X.E) - z / (q : X.E) ^ n) / (z / (q : X.E) ^ n) := by
      rw [hc, Units.val_mk0]
      field_simp
    rw [e1, map_div₀, hvu, div_one]
    refine mh_val_lt (ciIntAt_sub (IntAt.coe P c₀) hIu) ?_
    rw [redP_sub (IntAt.coe P c₀) hIu, reduction_coe, hmk, sub_self]
  have hcP : P.valuation X.E (c : X.E) = 1 := by
    have := hcu.val_eq_one
    rwa [map_div₀, hvu, div_one] at this
  have hw1 : OneAt (conjPrime₂ P) (w : X.E) := OneAt.of_mem hb2
  have hc1' : OneAt (conjPrime₂ P) (c : X.E) := OneAt.of_mem hc2
  have hk := md_key hX hsys hv hne x w c n hw1 hc1' (by
    have e : (w : X.E) ^ n * (c : X.E) / z = ((w : X.E) / (q : X.E)) ^ n * ((c : X.E) / (z / (q : X.E) ^ n)) := by
      rw [div_zpow]
      have := zpow_ne_zero n hq0
      field_simp
    rw [e]
    exact (hwq.zpow n).mul hcu)
  refine ⟨c, c₀, rfl, hmk, hc2, hcP, ?_⟩
  rw [hk]
  have e1 : lamH (F := X.F) χ v w = χ.locK P qu := by
    rw [hecke_character_evaluation X.F X.E _ hχ.tame v P hv w (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hw1)]
    have := (hecke_character_local_behaviour X.E χ P).1 (hχ.tame P) (w / qu) (by rw [Units.val_div_eq_div_val, hqu]; exact hwq)
    rw [map_div, div_eq_one] at this
    exact this
  have e2 : lamX (mu : Chr X.F X.E X.K) v w = qVal (mu : Chr X.F X.E X.K) P :=
    twist_value_at_q X.F X.E X.K S mu v P hv hq2 w b rfl hb1 (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hb2)
  have e3 : lamH (F := X.F) χ v c = χ.locK P c :=
    hecke_character_evaluation X.F X.E _ hχ.tame v P hv c (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hc1')
  unfold muLam
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, e1, e2, e3]

end Bad

section Law

open Formalism.L2.Host
open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m}

theorem md_fac_bad (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G)
    (i : ℕ) (hi : i < R.m) (P : rowSG Pr sel mu) {v : HeightOneSpectrum (𝓞 X.F)} (hv : P.1.asIdeal.under (𝓞 X.F) = v.asIdeal) (x : X.Eˣ) :
    G.σ₀ (muAtT Ch sel mu cst i P ((x : X.E) / star (x : X.E))) =
      (((muLam G.σ₀ (G.mu0 ⟨i, hi⟩) (mu : Chr X.F X.E X.K) v x)⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨-, hGt, ⟨eta, hTd⟩, -⟩ := hT
  have hχ := hTd.mu0 ⟨i, hi⟩
  have hq2 := mq_rowSG_unif mu hX hPr hsel P
  have hq : ((Col.qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := ciQ_mem P.1
  have hz0 : (x : X.E) / star (x : X.E) ≠ 0 := div_ne_zero x.ne_zero (star_ne_zero.2 x.ne_zero)
  obtain ⟨c, c₀, hcc, hmk, hc2, hcP, hL⟩ := md_bad hX hPr hsel hχ P.2 hq2 hv x (Units.mk0 ((Col.qOf P.1 : ℕ) : X.E) (ciQ_ne_zero hq2)) rfl
  have hu := isUnit_div_pow_valuation (Col.qOf P.1) hq hq2 _ hz0
  have hoth : ∀ P' : HeightOneSpectrum (𝓞 X.E), P' ≠ P.1 → P'.asIdeal.under (𝓞 X.F) = v.asIdeal → P' = conjPrime₂ P.1 := by
    intro P' h1 h2
    rcases local_factor_over_two X hX P.1 P' (h2.trans hv.symm) with h3 | h3
    · exact absurd h3 h1
    · exact h3
  rw [hL]
  unfold muAtT LocE.locChar LocE.unitV
  rw [dif_pos hu]
  generalize LocE.vP P.1 (Col.qOf P.1) ((x : X.E) / star (x : X.E)) = n at *
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have h1 := hGt i hi P hP (Units.mk0 ((Col.qOf P.1 : ℕ) : X.E) (ciQ_ne_zero hq2)) rfl
    have h2 : lamX (mu : Chr X.F X.E X.K) v c = 1 := (twist_components_compatible_system X.F X.E X.K S mu).unr v (hg P.1 hP v hv) c (fun P' hP' => by
      by_cases h : P' = P.1
      · rw [h]; exact hcP
      · rw [hoth P' h hP', hcc]; exact (OneAt.of_mem hc2).val_eq_one)
    have h3 := hχ.atg ⟨P.1, hP⟩ c c₀ hu.unit hcc (by rw [IsUnit.unit_spec]; exact hmk.symm)
    have h4 : chiP Ch P.1 i = Ch.chi ⟨i, hi⟩ ⟨P.1, hP⟩ := by
      unfold chiP chiAt extChi
      rw [dif_pos hP, dif_pos hi]
    rw [map_mul, map_zpow₀, h1, h4, h2, map_one, mul_one]
    have hb : G.σ₀ (((qVal (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K) = (G.σ₀ ((qVal (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹ := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
    have hd : (((G.mu0 ⟨i, hi⟩).locK P.1 c : ℂˣ) : ℂ) = (G.σ₀ ((Ch.chi ⟨i, hi⟩ ⟨P.1, hP⟩ hu.unit : X.Kˣ) : X.K))⁻¹ :=
      h3.trans (by rw [Units.val_inv_eq_inv_val, map_inv₀])
    rw [Units.val_inv_eq_inv_val (_ * _), Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mul, hb, hd, mul_inv, inv_inv, ← inv_zpow, mul_inv]
    rfl
  · rw [if_neg hP, if_neg hP]
    have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.1 P.2).resolve_left hP
    have hng : ∀ i' : Fin 2, ((Pr.g i' : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
      intro i' h
      rcases md_g_mem hPr h with h1 | h1
      · exact hP h1
      · obtain ⟨v', hv', hs⟩ := (mem_QE sel mu P.1).1 hPQ
        have e : v' = v := HeightOneSpectrum.ext (by rw [← hsel v', hs, hv])
        exact hg _ h1 v ((ab_conjP_under X hX P.1).trans hv) (e ▸ hv')
    have hunr : (G.mu0 ⟨i, hi⟩).UnrAt P.1 := hχ.unr _ hng
    have hvq : P.1.valuation X.E ((Col.qOf P.1 : ℕ) : X.E) = WithZero.exp (-1 : ℤ) := by
      have := mh_val_unif hq hq2
      simpa using this
    have h1 := (hecke_character_local_behaviour X.E (G.mu0 ⟨i, hi⟩) P.1).2.2 hunr (Units.mk0 ((Col.qOf P.1 : ℕ) : X.E) (ciQ_ne_zero hq2)) hvq
    have h2 := hTd.muVal ⟨i, hi⟩ P.1 hng
    have h3 := (hecke_character_local_behaviour X.E (G.mu0 ⟨i, hi⟩) P.1).2.1 hunr c hcP
    have h4 : lamX (mu : Chr X.F X.E X.K) v c = resChar (mu : Chr X.F X.E X.K) P.1 hu.unit :=
      twist_residue_character X.F X.E X.K S mu v P.1 hv c c₀ hu.unit hcc (by rw [IsUnit.unit_spec]; exact hmk)
        (fun P' h1 h2 => by rw [hoth P' h1 h2]; exact hc2)
    unfold muqT
    rw [dif_pos hi, h1, h3, h4, one_mul, map_mul, map_zpow₀]
    have hL1 : G.σ₀ ((((Ch.muVal ⟨i, hi⟩ P.1)⁻¹ * (qVal (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K) =
        (((G.mu0 ⟨i, hi⟩).val P.1 : ℂˣ) : ℂ)⁻¹ * (G.σ₀ ((qVal (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, h2]
    have hL2 : G.σ₀ ((((resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ hu.unit : X.Kˣ)) : X.K) =
        (G.σ₀ ((resChar (mu : Chr X.F X.E X.K) P.1 hu.unit : X.Kˣ) : X.K))⁻¹ := by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rw [hL1, hL2, Units.val_inv_eq_inv_val (_ * _), Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mul, mul_inv, ← inv_zpow, mul_inv]
    rfl

theorem md_muAtT_mul (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hT : LawTies W Ch sel mu cst G) (i : ℕ) (hi : i < R.m)
    (P : rowSG Pr sel mu) (a b : X.E) (ha : a ≠ 0) (hb : b ≠ 0) :
    muAtT Ch sel mu cst i P (a * b) = muAtT Ch sel mu cst i P a * muAtT Ch sel mu cst i P b := by
  have hq2 := mq_rowSG_unif mu hX hPr hsel P
  unfold muAtT
  refine ml_locChar_mul _ (ciQ_mem P.1) hq2 _ ?_ _ a b ha hb
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP]
    intro h0
    have h1 := hT.2.1 i hi P hP (Units.mk0 ((Col.qOf P.1 : ℕ) : X.E) (ciQ_ne_zero hq2)) rfl
    rw [h0, map_zero] at h1
    exact mul_ne_zero (inv_ne_zero (Units.ne_zero _)) ((map_ne_zero G.σ₀).2 (Units.ne_zero _)) h1.symm
  · rw [if_neg hP]
    exact Units.ne_zero _

theorem md_prod (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G)
    (i : ℕ) (hi : i < R.m) (x : X.Eˣ) :
    G.σ₀ ((∏ᶠ v, zFac sel (rowSG Pr sel mu) (mUof Ch mu i) ((x : X.E) / star (x : X.E)) v) *
      ∏ P : rowSG Pr sel mu, muAtT Ch sel mu cst i P ((x : X.E) / star (x : X.E))) = (((G.mu0 ⟨i, hi⟩).inf x : ℂˣ) : ℂ) := by
  obtain ⟨eta, hTd⟩ := hT.2.2.1
  have hχ := hTd.mu0 ⟨i, hi⟩
  have hz0 : (x : X.E) / star (x : X.E) ≠ 0 := div_ne_zero x.ne_zero (star_ne_zero.2 x.ne_zero)
  have ha0 : ((Pr.g 0 * Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (hPr.g_prime 0).ne_zero (hPr.g_prime 1).ne_zero
  have hH := hecke_character_product_formula X.F X.E (G.mu0 ⟨i, hi⟩) (divs ((Pr.g 0 * Pr.g 1 : ℕ) : 𝓞 X.E)) (fun P hP => hχ.unr P (fun i' h => hP ((mem_divs ha0 P).2 (by
    push_cast
    fin_cases i'
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h)))) x
  have hXi := twist_product_formula X.F X.E X.K S mu x
  set f : HeightOneSpectrum (𝓞 X.F) → ℂˣ := fun v => (muLam G.σ₀ (G.mu0 ⟨i, hi⟩) (mu : Chr X.F X.E X.K) v x)⁻¹ with hf
  have hXi' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 X.F) => Units.map G.σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v x)).Finite := by
    refine hXi.1.subset fun v hv h => hv ?_
    show Units.map G.σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v x) = 1
    rw [show lamX (mu : Chr X.F X.E X.K) v x = 1 from h, map_one]
  have hftot : ∏ᶠ v, f v = (G.mu0 ⟨i, hi⟩).inf x := by
    rw [hf, finprod_inv_distrib]
    have : (fun v => muLam G.σ₀ (G.mu0 ⟨i, hi⟩) (mu : Chr X.F X.E X.K) v x) =
        fun v => lamH (F := X.F) (G.mu0 ⟨i, hi⟩) v x * Units.map G.σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v x) := rfl
    rw [this, finprod_mul_distrib hH.1 hXi', hH.2, ← MonoidHom.map_finprod _ hXi.1, hXi.2, map_one, mul_one, inv_inv]
  have hfs : (Function.mulSupport f).Finite := by
    refine (hH.1.union hXi').subset fun v hv => ?_
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    apply hv
    have h1 : lamH (F := X.F) (G.mu0 ⟨i, hi⟩) v x = 1 := by
      by_contra h; exact hc.1 h
    have h2 : Units.map G.σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v x) = 1 := by
      by_contra h; exact hc.2 h
    show (lamH (F := X.F) (G.mu0 ⟨i, hi⟩) v x * Units.map G.σ₀.toMonoidHom (lamX (mu : Chr X.F X.E X.K) v x))⁻¹ = 1
    rw [h1, h2, one_mul, inv_one]
  set g : HeightOneSpectrum (𝓞 X.F) → ℂˣ := fun v => if v ∈ RmOf Pr sel mu then 1 else f v with hgd
  set h : HeightOneSpectrum (𝓞 X.F) → ℂˣ := fun v => if v ∈ RmOf Pr sel mu then f v else 1 with hhd
  have hgs : (Function.mulSupport g).Finite := hfs.subset fun v hv hc => hv (by
    show (if v ∈ RmOf Pr sel mu then 1 else f v) = 1
    rw [show f v = 1 from hc, ite_self])
  have hhs : (Function.mulSupport h).Finite := hfs.subset fun v hv hc => hv (by
    show (if v ∈ RmOf Pr sel mu then f v else 1) = 1
    rw [show f v = 1 from hc, ite_self])
  have hsplit : ∏ᶠ v, f v = (∏ᶠ v, g v) * ∏ᶠ v, h v := by
    rw [← finprod_mul_distrib hgs hhs]
    refine finprod_congr fun v => ?_
    show f v = (if v ∈ RmOf Pr sel mu then 1 else f v) * (if v ∈ RmOf Pr sel mu then f v else 1)
    by_cases hv : v ∈ RmOf Pr sel mu
    · rw [if_pos hv, if_pos hv, one_mul]
    · rw [if_neg hv, if_neg hv, mul_one]
  have e1 : G.σ₀ (∏ᶠ v, zFac sel (rowSG Pr sel mu) (mUof Ch mu i) ((x : X.E) / star (x : X.E)) v) = ((∏ᶠ v, g v : ℂˣ) : ℂ) := by
    have a1 := MonoidHom.map_finprod (G.σ₀ : X.K →* ℂ) (ml_zFac_support hsel (rowSG Pr sel mu) (mUof Ch mu i) _ hz0)
    have a2 := MonoidHom.map_finprod (Units.coeHom ℂ) hgs
    refine a1.trans (Eq.trans ?_ a2.symm)
    refine finprod_congr fun v => ?_
    show G.σ₀ (zFac sel (rowSG Pr sel mu) (mUof Ch mu i) ((x : X.E) / star (x : X.E)) v) = (((if v ∈ RmOf Pr sel mu then 1 else f v : ℂˣ)) : ℂ)
    by_cases hv : v ∈ RmOf Pr sel mu
    · rw [if_pos hv]
      unfold zFac
      rw [if_pos (show ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal from hv), map_one, Units.val_one]
    · rw [if_neg hv]
      exact md_fac_off Ch hX hPr hsel hTd i hi x hv
  have e2 : G.σ₀ (∏ P : rowSG Pr sel mu, muAtT Ch sel mu cst i P ((x : X.E) / star (x : X.E))) = ((∏ᶠ v, h v : ℂˣ) : ℂ) := by
    have hsub : Function.mulSupport h ⊆ ↑((rowSG Pr sel mu).image fun P => P.under (𝓞 X.F)) := by
      intro v hv
      by_contra hc
      apply hv
      show (if v ∈ RmOf Pr sel mu then f v else 1) = 1
      rw [if_neg]
      rintro ⟨P, hP, hPv⟩
      apply hc
      rw [Finset.coe_image]
      exact ⟨P, hP, HeightOneSpectrum.ext hPv⟩
    have ecs := Finset.prod_coe_sort (rowSG Pr sel mu) (fun P => h (P.under (𝓞 X.F)))
    rw [finprod_eq_prod_of_mulSupport_subset h hsub, Finset.prod_image (fun P hP P' hP' hh =>
      (md_inj hX.ok hPr hsel hg hP' hP (congrArg HeightOneSpectrum.asIdeal hh))), ← ecs, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun P _ => ?_
    show _ = (((if P.1.under (𝓞 X.F) ∈ RmOf Pr sel mu then f (P.1.under (𝓞 X.F)) else 1 : ℂˣ)) : ℂ)
    rw [if_pos (md_mem_Rm P.2 rfl)]
    exact md_fac_bad hX.ok hPr hsel hg hT i hi P rfl x
  rw [map_mul, e1, e2, ← Units.val_mul, ← hsplit, hftot]

theorem muProdLaw_of (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G)
    (i : ℕ) (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩) (n : ℕ) :
    MuProdLaw n sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e := by
  intro γ N fr hN
  obtain ⟨x, hx⟩ := hilbert_ninety_norm_one X hX.ok _ (mh_det_norm γ)
  rw [ml_ratio hsel _ _ _ (md_muAtT_mul hX.ok hPr hsel hT i hi) γ N hN fr]
  congr 1
  apply G.σ₀.injective
  rw [hx, md_prod hX hPr hsel hg hT i hi x]
  obtain ⟨eta, hTd⟩ := hT.2.2.1
  obtain ⟨m, hm1, hm2⟩ := (hTd.mu0 ⟨i, hi⟩).inf
  rw [hecke_character_infinity_type X hX.ok G.σ₀ _ m e hm2 (fun τ => by
    have : (m τ : ℚ) = 2 * -(W.row τ).e ⟨i, hi⟩ := hm1 τ
    rw [← he τ] at this
    exact_mod_cast this) x, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀]

end Law

section More

open Formalism.L2.Host Formalism.EigenvalueLevelCeiling
open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m}

theorem muProdLaw_muAt (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G)
    (i : ℕ) (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩) (n : ℕ) :
    MuProdLaw n sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) e := by
  rw [muAt_eq_muAtT Ch sel mu cst hT.1 i hi]
  exact muProdLaw_of hX hPr hsel hg hT i hi e he n

theorem xiOffG_of_mem (hPr : Pr.Ok) (hS : ∀ i, Pr.g i ∈ S) : XiOffG Pr (mu : Chr X.F X.E X.K) := by
  intro P hP v hv hQ
  obtain ⟨i, hi⟩ := ciVGs_cases hP
  have hgP : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]
    exact Ideal.mul_mem_left _ _ ((mem_divs (ciConjPiG_ne_zero hPr i) _).1 hi)
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hv]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ P.asIdeal
    rw [map_natCast]
    exact hgP
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hPr.g_prime i)).mp h2
  exact (mu.good hQ).2.2 (h3 ▸ hS i)

theorem test_not_oneAt_zero {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : ¬ OneAt P (0 : E) := by
  unfold OneAt
  rw [zero_sub, Valuation.map_neg, map_one]
  exact lt_irrefl _

theorem test_not_oneAt_unif {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {a : E}
    (h : P.valuation E a = WithZero.exp (-1 : ℤ)) : ¬ OneAt P a := by
  intro h1
  rw [h1.val_eq_one] at h
  exact absurd h (by simp)

theorem test_locId_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) :
    Formalism.UG.prV (E := E) v ((locId E v a : (AfE F E)ˣ) : AfE F E) = (a : E) ⊗ₜ[F] (1 : v.adicCompletion F) := by
  show (Algebra.TensorProduct.map (AlgHom.id F E) (Formalism.UG.evalV F v))
    ((a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) = _
  rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_sub, Formalism.L2.G.sgl_apply_same, map_one (Formalism.UG.evalV F v), sub_self,
    TensorProduct.tmul_zero, add_zero]
  rfl

theorem test_locId_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (a : Eˣ) :
    Formalism.UG.prV (E := E) v' ((locId E v a : (AfE F E)ˣ) : AfE F E) = 1 := by
  show (Algebra.TensorProduct.map (AlgHom.id F E) (Formalism.UG.evalV F v'))
    ((a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) = _
  rw [map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_sub, Formalism.L2.G.sgl_apply_ne F v 1 h, map_one (Formalism.UG.evalV F v'), sub_zero,
    TensorProduct.tmul_zero, zero_add]
  rfl

end More

end Formalism.L2.Ker
