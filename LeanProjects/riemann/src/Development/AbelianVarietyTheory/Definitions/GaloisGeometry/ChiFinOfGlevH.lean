import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR

noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_of_root {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    (x : K) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : ∃ o : Oˣ, algebraMap O K (o : O) * x = 1 := by
  have hint : IsIntegral O x :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hx]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hy1 : y ^ k * y = 1 := by
    apply IsFractionRing.injective O K
    rw [← pow_succ, map_pow, hy, hx, map_one]
  refine ⟨⟨y ^ k, y, hy1, by rw [mul_comm]; exact hy1⟩, ?_⟩
  show algebraMap O K (y ^ k) * x = 1
  rw [← hy, ← map_mul, hy1, map_one]

theorem exists_char {G₀ LL O K : Type} [Group G₀] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (emb : LL →+* ℂ) (e : LL →+* K) (χ : G₀ →* ℂˣ) (hrat : ∀ a, ∃ r : LL, emb r = (χ a : ℂ))
    (hfin : ∃ n : ℕ, 0 < n ∧ ∀ a, χ a ^ n = 1) :
    ∃ ψ : G₀ →* Oˣ, ∀ a (r : LL), emb r = (χ a : ℂ) → algebraMap O K (ψ a : O) * e r = 1 := by
  have ex : ∀ a : G₀, ∃ o : Oˣ, ∀ r : LL, emb r = (χ a : ℂ) → algebraMap O K (o : O) * e r = 1 := by
    intro a
    obtain ⟨r, hr⟩ := hrat a
    obtain ⟨n, hn, hc⟩ := hfin
    have hrn : r ^ n = 1 := emb.injective (by
      rw [map_pow, hr, map_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one])
    obtain ⟨o, ho⟩ := unit_of_root (O := O) (e r) n hn (by rw [← map_pow, hrn, map_one])
    exact ⟨o, fun r' hr' => by rw [emb.injective (hr'.trans hr.symm)]; exact ho⟩
  choose f hf using ex
  refine ⟨MonoidHom.mk' f ?_, fun a r hr => hf a r hr⟩
  intro a b
  obtain ⟨ra, hra⟩ := hrat a
  obtain ⟨rb, hrb⟩ := hrat b
  have h1 := hf (a * b) (ra * rb) (by rw [map_mul, hra, hrb, map_mul, Units.val_mul])
  have h2 := hf a ra hra
  have h3 := hf b rb hrb
  have h4 : algebraMap O K ((f a * f b : Oˣ) : O) * e (ra * rb) = 1 := by
    rw [Units.val_mul, map_mul, map_mul]
    calc _ = (algebraMap O K (f a : O) * e ra) * (algebraMap O K (f b : O) * e rb) := by ring
      _ = 1 := by rw [h2, h3, one_mul]
  have hne : e (ra * rb) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact Units.ext (IsFractionRing.injective O K (mul_right_cancel₀ hne (h1.trans h4.symm)))

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 4000000 in

def kap (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) :
    awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p →* (Fo.K β).lev.U :=
  ((glue (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E)).comp
    (((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _).toMonoidHom.comp
      (awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p).subtype).prod 1)).codRestrict (Fo.K β).lev.U (by
    intro a
    have ha := (mem_awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p a.1).1 a.2
    refine ((Fo.K β).lev.U_eq _).2 ⟨glue_mem_UJ (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E) _
      (epsP_sig D.host.F p D.host.E (sigD D)) _
      (reGL_mem_UPts (rankN D (i + 1) hi) (sigD D) (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi) _ a.1 ha.1)
      (Subgroup.one_mem _), fun v => ?_⟩
    by_cases hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) ∈ _
      rw [bc_reGL]
      exact ha.2 v hv)

theorem kap_over (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kap Fo β p a).1 = 1 := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = 1
  rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
  exact map_one _

theorem kap_off (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kap Fo β p a).1 =
      bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = _
  rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
  rfl

set_option maxHeartbeats 4000000 in

theorem chi_kap (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p)
    (κ : (Fo.K β).lev.U)
    (hκp : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → bc (prV (E := D.host.E) v) κ.1 = 1)
    (hκo : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((p : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
      bc (prV (E := D.host.E) w') κ.1 = bc (prV (E := D.host.E) w') (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1)) :
    (Fo.K β).lev.chi κ = (Fo.K β).lev.chi (kap Fo β p a) := by
  have h1 : (Fo.K β).lev.chi (κ * (kap Fo β p a)⁻¹) = 1 := by
    refine (Fo.K β).lev.chi_triv _ fun v _ => ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · rw [hκp v hv, kap_over Fo β p a v hv, inv_one, one_mul]
    · rw [hκo v hv, kap_off Fo β p a v hv, mul_inv_cancel]
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

set_option maxHeartbeats 4000000 in

theorem psiEx_of (Fo : FormsIn M (i + 1) hi) (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hrat : ∀ β, ChiRatAll (Fo.K β).lev D.what₂.embLL)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (Fo.K β).lev.chi κ ^ n = 1) : PsiEx Fo e := by
  intro β
  obtain ⟨n, hn, hc⟩ := hfin β
  obtain ⟨ψ, hψ⟩ := exists_char (O := (D.gat u w hg).O) D.what₂.embLL e
    ((Fo.K β).lev.chi.comp (kap Fo β (D.what₂.places.resChar w))) (fun a => hrat β _) ⟨n, hn, fun a => hc _⟩
  refine ⟨ψ, fun a κ hκp hκo => ?_⟩
  obtain ⟨r, hr⟩ := hrat β κ
  exact ⟨r, hr, hψ a r (hr.trans (congrArg (fun z : ℂˣ => (z : ℂ)) (chi_kap Fo β _ a κ hκp hκo)))⟩

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem finite_glk (v : HeightOneSpectrum (𝓞 F)) : Finite (GL (Fin n) (kv F v)) := by
  have : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  have : Finite (Matrix (Fin n) (Fin n) (kv F v)) := inferInstanceAs (Finite (Fin n → Fin n → kv F v))
  exact Finite.of_injective (fun u : GL (Fin n) (kv F v) => (u : Matrix (Fin n) (Fin n) (kv F v))) (fun _ _ h => Units.ext h)

open Classical in

theorem chi_fin_of_glevH {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp}
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (L : GLevH S G H lam) (hgp : ∀ a, gp a ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ κ, S.chi κ ^ m = 1 := by
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite :=
    fun a => Formalism.L2.G.finite_setOf_mem_asIdeal (Nat.cast_ne_zero.2 (hgp a))
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Nat.card (GL (Fin n) (kv F v)) := fun v =>
    haveI := finite_glk (n := n) v
    Nat.card_pos
  refine ⟨∏ a : Fin 2, ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)),
    Finset.prod_pos fun a _ => Finset.prod_pos fun v _ => hN v, fun κ => ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, L.chi_eq κ, Units.val_one, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun a _ => ?_
  have hsup : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ∏ᶠ (h : (gp a : 𝓞 F) ∈ v.asIdeal),
      (((lam a v h (L.red a v h κ) : ℂˣ) : ℂ))⁻¹) ⊆ ((hfin a).toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    rw [Function.mem_mulSupport, finprod_eq_dif] at hv
    by_cases h : (gp a : 𝓞 F) ∈ v.asIdeal
    · exact Finset.mem_coe.2 ((Set.Finite.mem_toFinset (hfin a)).2 h)
    · rw [dif_neg h] at hv
      exact absurd rfl hv
  rw [finprod_eq_prod_of_mulSupport_subset _ hsup, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun v hv => ?_
  have h : (gp a : 𝓞 F) ∈ v.asIdeal := (Set.Finite.mem_toFinset (hfin a)).1 hv
  rw [finprod_eq_dif, dif_pos h]
  have hd : Nat.card (GL (Fin n) (kv F v)) ∣ ∏ a : Fin 2, ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)) :=
    (Finset.dvd_prod_of_mem _ hv).trans (Finset.dvd_prod_of_mem (fun a : Fin 2 => ∏ v ∈ (hfin a).toFinset, Nat.card (GL (Fin n) (kv F v)))
      (Finset.mem_univ a))
  obtain ⟨q, hq⟩ := hd
  have h1 : (L.red a v h κ) ^ Nat.card (GL (Fin n) (kv F v)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have := finite_glk (n := n) v
    exact pow_card_eq_one'
  have h2 : ((lam a v h (L.red a v h κ) : ℂˣ) : ℂ) ^ Nat.card (GL (Fin n) (kv F v)) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  rw [hq, inv_pow, pow_mul, h2, one_pow, inv_one]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem chi_fin_top (F : FormsTiedSym D u Ch chOf) (j : ℕ) (hj : j ≤ D.R.m) (h : j = D.R.m) :
    ∃ m : ℕ, 0 < m ∧ ∀ κ, (F.cls j hj (Or.inr h)).lev.chi κ ^ m = 1 := by
  subst h
  exact chi_fin_of_glevH F.glevM fun a => (D.host.g_prime a).ne_zero

set_option maxHeartbeats 2000000 in

theorem finMem_of (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β, ∃ m : ℕ, 0 < m ∧ ∀ κ, ((formsInMem F dt i hi).K β).lev.chi κ ^ m = 1 := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    intro β
    exact chi_fin_top F (i + 1) hi h
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β
    exact chi_fin_of_glevH (F.glevC (i + 1) _ _ β) fun a => (D.host.g_prime a).ne_zero

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.L2.G.Cmp
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ} {LL : Type} [Field LL]

theorem chiRat_of_glevH {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp}
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (L : GLevH S G H lam) (emb : LL →+* ℂ)
    (hl : ∀ a v h (M : H a v h), ∃ k : LL, emb k = ((lam a v h M : ℂˣ) : ℂ)) : ChiRatAll S emb := by
  intro κ
  have h : (S.chi κ : ℂ) ∈ emb.fieldRange := by
    rw [L.chi_eq κ]
    refine prod_mem fun a _ => ?_
    refine finprod_induction (fun z : ℂ => z ∈ emb.fieldRange) (one_mem _) (fun x y hx hy => mul_mem hx hy) fun v => ?_
    refine finprod_induction (fun z : ℂ => z ∈ emb.fieldRange) (one_mem _) (fun x y hx hy => mul_mem hx hy) fun hv => ?_
    obtain ⟨k, hk⟩ := hl a v hv (L.red a v hv κ)
    exact inv_mem (RingHom.mem_fieldRange.2 ⟨k, hk⟩)
  exact RingHom.mem_fieldRange.1 h

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def LamCRat (F : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ i β a v h (M : F.H i β a v h), ∃ k : D.what₂.LL, D.what₂.embLL k = ((F.lamC i β a v h M : ℂˣ) : ℂ)

def LamMRat (F : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ a v h (M : HSym D (D.R.N D.R.m) true v), ∃ k : D.what₂.LL, D.what₂.embLL k = ((F.lamM a v h M : ℂˣ) : ℂ)

theorem chiRat_top (F : FormsTiedSym D u Ch chOf) (hM : LamMRat F) (j : ℕ) (hj : j ≤ D.R.m) (h : j = D.R.m) :
    ChiRatAll (F.cls j hj (Or.inr h)).lev D.what₂.embLL := by
  subst h
  exact chiRat_of_glevH F.glevM D.what₂.embLL hM

set_option maxHeartbeats 2000000 in

theorem ratMem_of (F : FormsTiedSym D u Ch chOf) (hC : LamCRat F) (hM : LamMRat F) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β, ChiRatAll ((formsInMem F dt i hi).K β).lev D.what₂.embLL := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    intro β
    exact chiRat_top F hM (i + 1) hi h
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β
    exact chiRat_of_glevH (F.glevC (i + 1) _ _ β) D.what₂.embLL (hC (i + 1) β)

end GlobalTheory.Port

end

end
