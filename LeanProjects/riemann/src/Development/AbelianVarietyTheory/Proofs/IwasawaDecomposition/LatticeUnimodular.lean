import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AlgebraMapGFEqGval
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions IsDedekindDomain
open Formalism.MainNotions.S (FlagG XS ddS FrameOK)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS XLam IsFixedConv FixedHyp)
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm.Conv

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_local_gen {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c : E, c ≠ 0 ∧ c ∈ I ∧ ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  have int {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹) : ∃ o : 𝓞 E, (o : E) = a * b := by
    have := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  obtain ⟨a, ha, b, hb, s, hs, e⟩ : ∃ a ∈ I, ∃ b ∈ I⁻¹, ∃ s : 𝓞 E, s ∉ P ∧ (s : E) = a * b := by
    by_contra h
    have h1 : (1 : E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
    obtain ⟨s, hs, e⟩ := FractionalIdeal.mul_induction_on (C := fun x => ∃ s ∈ P, (s : E) = x) h1
      (fun a ha b hb => by
        obtain ⟨o, e⟩ := int ha hb
        exact ⟨o, by_contra fun k => h ⟨a, ha, b, hb, o, k, e⟩, e⟩)
      (fun _ _ ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨s + t, add_mem hs ht, by rw [← e, ← f]; simp⟩)
    obtain rfl : s = 1 := RingOfIntegers.ext e
    exact hP ((Ideal.eq_top_iff_one _).2 hs)
  refine ⟨a, fun h => hs ?_, ha, fun x hx => ⟨s, hs, ?_⟩⟩
  · obtain rfl : s = 0 := RingOfIntegers.ext (by rw [e, h, zero_mul]; rfl)
    exact zero_mem _
  · obtain ⟨o, f⟩ := int hx hb
    exact ⟨o, by rw [e, f]; ring⟩

theorem exists_gen_dInv (j : ℕ) (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    ∃ c : E, c ≠ 0 ∧ c ∈ dInv E j ∧ (¬ P ∣ differentIdeal ℤ (𝓞 E) → c = 1) ∧
      ∀ x ∈ dInv E j, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  by_cases h : P ∣ differentIdeal ℤ (𝓞 E)
  · obtain ⟨c, h1, h2, h3⟩ := exists_local_gen (I := dInv E j)
      (fun e => by simpa [e] using Iota.one_mem_dInv (E := E) j) hP.ne_top
    exact ⟨c, h1, h2, fun k => absurd h k, h3⟩
  · obtain ⟨s, hs, hn⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.dvd_iff_le.2 h)
    refine ⟨1, one_ne_zero, Iota.one_mem_dInv j, fun _ => rfl, fun x hx =>
      ⟨s ^ j, fun k => hn (hP.mem_of_pow_mem j k), ?_⟩⟩
    have h0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
    have := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) (Ideal.pow_mem_pow hs j)) hx
    rw [FractionalIdeal.coeIdeal_pow, dInv, ← mul_pow, mul_inv_cancel₀ h0, one_pow] at this
    obtain ⟨o, e⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨o, by rw [mul_one]; exact e.symm⟩

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have e : HeightOneSpectrum.asIdeal '' placesOver E p = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := v.isPrime
      exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa [placesOver] using hv)⟩
    · rintro ⟨h1, h2⟩
      have k : (p : 𝓞 E) ∈ Q := by simpa using (Ideal.liesOver_span_iff h1.ne_top hp').1 h2
      exact ⟨⟨Q, h1, fun e => hp.ne_zero (by simpa [e] using k)⟩, k, rfl⟩
  have hd := GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E (by
    rw [← e, Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw, h])
  exact not_dvd_differentIdeal_iff.2 ((not_dvd_discr_iff_forall_mem E (𝓞 E) hp').1 hd P hP (by simpa using hm))

end Ideals

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) (Fin S.rank → E)} {F : LFlag S r T}

theorem lattice_unimodular (h : SelfDual (starRingEnd E) S.gram Λ) :
    Submodule.IsLattice E (latV S Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT (latV S Λ) := by
  have hd (x : S.V) : x ∈ latV S Λ ↔ ∀ y ∈ latV S Λ, S.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    rw [mem_latV, h.2, co_surjective.forall]
    simp only [← B_eq, mem_latV, Submodule.mem_one, RingHom.mem_range, GlobalTheory.SA.ofHSpace_B]
  refine ⟨⟨?_, (isUnimod_latV h).1.2⟩, Submodule.ext fun x => ?_⟩
  · rw [latV, Submodule.comap_equiv_eq_map_symm]; exact h.1.map _
  · rw [hd]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]

variable (h : IntFrame (starRingEnd E) S.gram T Λ (coMat S (Formalism.MainNotions.S.Lat.frame F)))
include h

theorem sum_mem_iff (k : Fin r → E) (c : E) : ∑ a, k a • F.fl.e a + c • F.fl.z ∈ latV S Λ ↔
    (∀ a : Fin r, k a ∈ dInv E (r - a)) ∧ c ∈ dInv E 0 := by
  have e : co S (∑ a, k a • F.fl.e a + c • F.fl.z) = coMat S (Formalism.MainNotions.S.Lat.frame F) *ᵥ Fin.snoc k c := by
    rw [coMat_mulVec, Fin.sum_univ_castSucc]
    simp [Formalism.MainNotions.S.Lat.frame, FlagG.fvec]
  have f : (∀ b : Fin (r + 1), (Fin.snoc k c : Fin (r + 1) → E) b ∈ dInv E (r - b)) ↔
      (∀ a : Fin r, k a ∈ dInv E (r - a)) ∧ c ∈ dInv E 0 := by
    rw [Fin.forall_fin_succ']; simp
  rw [mem_latV, e, ← f]
  refine ⟨fun h1 => ?_, fun h1 => h.2.1 ((Iota.mem_frameLat _ _).2 ⟨_, h1, rfl⟩)⟩
  obtain ⟨a, ha, e1⟩ := (Iota.mem_frameLat _ _).1 (h.2.2 _ h1 ((Iota.mem_span_frameLat _ _).2 ⟨_, rfl⟩))
  obtain ⟨L, hL⟩ := h.1.1
  obtain rfl : a = Fin.snoc k c := by simpa [Matrix.mulVec_mulVec, hL] using congrArg (L *ᵥ ·) e1
  exact ha

theorem mem_xLam (x : S.V) : x ∈ XLam (latV S Λ) F ↔
    ∃ k : Fin r → E, (∀ a : Fin r, k a ∈ dInv E (r - a)) ∧ ∑ a, k a • F.fl.e a = x := by
  have e (k : Fin r → E) : ∑ a, k a • F.fl.e a ∈ latV S Λ ↔ ∀ a : Fin r, k a ∈ dInv E (r - a) := by
    simpa [FractionalIdeal.zero_mem] using sum_mem_iff h k 0
  refine ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h2
    exact ⟨k, (e k).1 h1, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(e k).2 hk, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨k, rfl⟩⟩

theorem xLam_eq_span : XLam (latV S Λ) F =
    Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ dInv E (r - a) ∧ y = x • F.fl.e a} := by
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨k, hk, rfl⟩ := (mem_xLam h x).1 hx
    exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, _, hk a, rfl⟩
  · rintro _ ⟨a, x, hx, rfl⟩
    refine (mem_xLam h _).2 ⟨Pi.single a x, fun b => ?_, by simp [Pi.single_apply]⟩
    rcases eq_or_ne b a with rfl | hb
    · simpa using hx
    · simp [hb, FractionalIdeal.zero_mem]

theorem isFixedConv {g : ℕ}
    (hg : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E)) :
    IsFixedConv (latV S Λ) g F := by
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · have := P.isPrime
    choose c h1 h2 h3 h4 using fun a : Fin r => exists_gen_dInv (E := E) (r - a) P.asIdeal
    refine ⟨c, h1, fun k a => h3 a (hg P k), le_antisymm ?_ ?_⟩
    · rintro x ⟨s, hs, hx⟩
      have k : XLam (latV S Λ) F ≤
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)) := by
        rw [xLam_eq_span h, Submodule.span_le]
        rintro _ ⟨a, y, hy, rfl⟩
        obtain ⟨t, ht, o, e⟩ := h4 a y hy
        refine ⟨t, ht, ?_⟩
        have : t • y • F.fl.e a = o • c a • F.fl.e a := by
          rw [← algebraMap_smul E t, ← algebraMap_smul E o, smul_smul, smul_smul]
          exact congrArg (· • F.fl.e a) e
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      obtain ⟨t, ht, hx'⟩ := k hx
      exact ⟨t * s, mul_mem ht hs, by rwa [mul_smul]⟩
    · rintro x ⟨s, hs, hx⟩
      refine ⟨s, hs, (?_ : _ ≤ XLam (latV S Λ) F) hx⟩
      rw [xLam_eq_span h, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, _, h2 a, rfl⟩
  · obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hc.1
    obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : l = ∑ a, (-k a) • F.fl.e a + c • F.fl.z := by
      rw [← e]; simp
    have k := ((sum_mem_iff h _ c).1 (this ▸ hl.1)).2
    rw [dInv, pow_zero] at k
    exact (FractionalIdeal.mem_one_iff _).1 k

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddS_eq : ddS D = (differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) := by
  rw [ddS, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.F) (𝓞 D.host.E),
    GlobalTheory.CMDiscrSq.differentIdeal_eq_top D.sp.cm, Ideal.top_mul]

theorem level_not_dvd (P : HeightOneSpectrum (𝓞 D.host.E)) (h : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.E) := by
  have := P.isPrime
  rw [gS, Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact not_dvd_different (D.host.g_prime 0) (D.nd.g_split 0) _ h
  · exact not_dvd_different (D.host.g_prime 1) (D.nd.g_split 1) _ h

variable {D}

theorem frameOK {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin (hS D).rank → D.host.E)}
    {F : LFlag (hS D) D.R.rS T}
    (h : IntFrame (starRingEnd D.host.E) (hS D).gram T Λ (coMat (hS D) (Formalism.MainNotions.S.Lat.frame F))) :
    FrameOK D (latV (hS D) Λ) F := by
  refine ⟨isFixedConv h (level_not_dvd D), ?_⟩
  have e (a : Fin D.R.rS) : ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) = dInv D.host.E (D.R.rS - a) := by
    rw [ddS_eq, dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast, inv_pow]
  rw [xLam_eq_span h, XS]
  simp only [e]

theorem conventions : ∀ (D : D7) (u u' : D.what₂.Word) (t : RecTerm D u u'),
    Formalism.MainNotions.S.Lat.FixedHyp D t.abelian₂ t.fl ∧ Formalism.MainNotions.S.Lat.IsFixedConv t.abelian₂ (Formalism.MainNotions.S.Lat.gS D) t.fl' ∧
      Formalism.MainNotions.S.FrameOK D t.abelian₂ t.fl' ∧ Formalism.MainNotions.S.Lat.XLam t.abelian₂ t.fl = Formalism.MainNotions.S.XS D t.fl.fl := by
  intro D u u' t
  have h1 : FrameOK D t.abelian₂ t.fl := frameOK (by rw [t.coMat_fl]; exact ⟨isFrame_recFrame D u, t.lat_mem.2⟩)
  have h2 : FrameOK D t.abelian₂ t.fl' := frameOK (by rw [t.coMat_fl']; exact t.adm.1)
  have h3 := lattice_unimodular (S := hS D) t.lat_mem.1
  exact ⟨⟨h3.1, h3.2, t.isLift_fl, h1.1⟩, h2.1, h2, h1.2⟩

end Record

end GlobalTheory.IntTerm.Conv
