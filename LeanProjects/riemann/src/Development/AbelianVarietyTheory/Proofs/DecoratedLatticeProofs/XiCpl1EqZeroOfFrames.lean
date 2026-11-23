import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FullOfSpanEqTop
open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

noncomputable section

namespace GlobalTheory.CplDead

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem full_finset_inf {W ι : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset ι) (M : ι → Submodule (𝓞 E) W)
    (hM : ∀ i, Full (M i)) : Full (S.inf M) := by
  induction S using Finset.induction_on with
  | empty => intro x; exact ⟨1, one_pos, by simp⟩
  | insert i S hi ih => rw [Finset.inf_insert]; exact (hM i).inf ih

theorem exists_approx_family {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) W) (hM : ∀ P, Full (M P)) (x : HeightOneSpectrum (𝓞 E) → W) :
    ∃ t : W, ∀ P ∈ S, t - x P ∈ localization₂ P.asIdeal (M P) := by
  have h := fun P => (full_finset_inf S M hM).approx {P} (x P)
  choose t h1 h2 using h
  refine ⟨∑ P ∈ S, t P, fun P hP => localization_mono P (Finset.inf_le hP) ?_⟩
  rw [← Finset.add_sum_erase S t hP, add_sub_right_comm]
  refine Submodule.add_mem _ (h1 P P (Finset.mem_singleton_self P)) (Submodule.sum_mem _ fun Q hQ => h2 Q P ?_)
  rw [Finset.mem_singleton]
  exact (Finset.ne_of_mem_erase hQ).symm

theorem full_of_span {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.span E (N : Set (Sp E n)) = ⊤) : Full N := by
  first
  | exact @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | (apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top ..)

theorem full_stdLat (n : ℕ) : Full (stdLat E n) := by
  refine full_of_span _ (top_le_iff.1 fun x _ => ?_)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun j _ => ?_)
  by_cases h : i = j
  · simp only [if_pos h]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · simp only [if_neg h]; exact Submodule.zero_mem _

theorem intAt_of_mem_stdAt {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) :
    IntAt P (x i) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i (Set.mem_univ i))
  exact ⟨r, s, hs, by rw [hr]; rfl⟩

variable {a b : ℕ}

def homInto (S₀ : Set (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {z | ∀ y ∈ S₀, g (z y) ∈ N}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {z z'} hz hz' y hy => by
    rw [LinearMap.add_apply, map_add]; exact N.add_mem (hz y hy) (hz' y hy)
  smul_mem' := fun c z hz y hy => by
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]; exact N.smul_mem _ (hz y hy)

theorem full_homInto (S₀ : Finset (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) {N : Submodule (𝓞 E) (Sp E b)} (hN : Full N) :
    Full (homInto (S₀ : Set (Sp E a)) g N) := by
  intro z
  choose n hn hz using fun y => hN (g (z y))
  refine ⟨∏ y ∈ S₀, n y, Finset.prod_pos fun y _ => hn y, fun y hy => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, ← Finset.prod_erase_mul S₀ n hy, Nat.cast_mul, mul_smul]
  exact N.smul_mem _ (hz y)

theorem apply_mem_of_mem_locP {S₀ : Set (Sp E a)} {g : Sp E b →ₗ[E] Sp E b} {N : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} {z : HomE E a b} (hz : z ∈ localization₂ P.asIdeal (homInto S₀ g N)) {y : Sp E a}
    (hy : y ∈ localization₂ P.asIdeal (Submodule.span (𝓞 E) S₀)) : g (z y) ∈ localization₂ P.asIdeal N := by
  obtain ⟨s, hs, hz⟩ := hz
  obtain ⟨t, ht, hy⟩ := hy
  have h : ∀ w ∈ Submodule.span (𝓞 E) S₀, g ((s • z) w) ∈ N := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hz w hw
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, map_add]; exact N.add_mem hu hv
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; exact N.smul_mem _ hu
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have := h _ hy
  rwa [LinearMap.smul_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    smul_smul] at this

variable [StarRing E]

theorem phiT_add (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG)
    {d' : Deco E b ST SG'} (hd' : d'.Ok) (x z : HomE E a b)
    (hz : ∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ x z : HomE E a b, (∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + z) y ∈ d'.at P.1 ∧ d'.f P ((x + z) y) = d.f P y := by
    intro x z hz hx P y hy
    have hq : (qOf P.1 : E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := by rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
      exact_mod_cast this
    have e : z y = (qOf P.1 : 𝓞 E) • ((qOf P.1 : E))⁻¹ • z y := by
      rw [← algebraMap_smul E (qOf P.1 : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hq, one_smul]
    have h1 : z y ∈ d'.at P.1 := by rw [e]; exact Submodule.smul_mem _ _ (hz P y hy)
    have h2 : d'.f P (z y) = 0 := by
      rw [e, hd'.f_smul P _ _ (hz P y hy), Ideal.Quotient.eq_zero_iff_mem.2
        (show (qOf P.1 : 𝓞 E) ∈ P.1.asIdeal from Ideal.absNorm_mem _), zero_mul]
    rw [LinearMap.add_apply]
    exact ⟨Submodule.add_mem _ (hx P y hy).1 h1, by rw [hd'.f_add P _ (hx P y hy).1 _ h1, h2, add_zero, (hx P y hy).2]⟩
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun P y hy => by
    rw [LinearMap.neg_apply, smul_neg]; exact Submodule.neg_mem _ (hz P y hy)) h
  rwa [add_neg_cancel_right] at this

theorem exists_transport (K : Type) [Field K] {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} (hdis : Disjoint ST SB)
    {d : Deco E a ST SG} (hd : d.Ok) {d' : Deco E b ST SG'} (hd' : d'.Ok) (f₀ : Frs E a SB) (f f' : Frs E b SB)
    (c : SB → E) (x : HomE E a b) :
    ∃ x' : HomE E a b, phiT K d d' x' = phiT K d d' x ∧
      ∀ (P : SB) s l, IntAt P.1 (c P * (inFr (f₀ P) (f P) x' - inFr (f₀ P) (f' P) x) (Pi.single s 1) l) := by
  obtain ⟨S₀, hS₀⟩ := hd.lat.fg
  obtain ⟨t, ht⟩ := exists_approx_family (W := HomE E a b) (ST ∪ SB)
    (fun P => if h : P ∈ SB then
        homInto ((Finset.univ.image fun s : Fin a => f₀ ⟨P, h⟩ (Pi.single s 1) : Finset (Sp E a)) : Set (Sp E a))
          (c ⟨P, h⟩ • (f ⟨P, h⟩).symm.toLinearMap) (stdLat E b)
      else homInto (S₀ : Set (Sp E a)) (((qOf P : E))⁻¹ • LinearMap.id) d'.N)
    (fun P => by
      by_cases h : P ∈ SB
      · simp only [dif_pos h]; exact full_homInto _ _ (full_stdLat b)
      · simp only [dif_neg h]; exact full_homInto _ _ (full_of_span _ hd'.lat.span_eq_top))
    (fun P => if h : P ∈ SB then (f ⟨P, h⟩).toLinearMap ∘ₗ (f' ⟨P, h⟩).symm.toLinearMap ∘ₗ x else x)
  refine ⟨t, ?_, fun P s l => ?_⟩
  · rw [← add_sub_cancel x t]
    refine phiT_add K d hd' x _ fun P y hy => ?_
    have h : P.1 ∉ SB := Finset.disjoint_left.1 hdis P.2
    have h1 := ht P.1 (Finset.mem_union_left _ P.2)
    simp only [dif_neg h] at h1
    exact apply_mem_of_mem_locP h1 (by rw [hS₀]; exact hy)
  · have h1 := ht P.1 (Finset.mem_union_right _ P.2)
    simp only [dif_pos P.2] at h1
    have h2 := apply_mem_of_mem_locP h1 (y := f₀ P (Pi.single s 1))
      (mem_localization_of_mem _ (Submodule.subset_span (by simp)))
    have h3 := intAt_of_mem_stdAt h2 l
    convert h3 using 1
    simp [inFr]

end Gen

theorem xiCpl1_eq_zero_of_frames : ∀ {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word), Disjoint (Pr.vT u) (rowSG Pr sel mu) → ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p p' : ChPt (R := R) sel mu u (m2 + 1)) (Y Y' : Set (Sp X.E (R.N (m2 + 1)))), p'.deco = p.deco → (∀ P : rowSG Pr sel mu, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) ∈ stdAt X.E (R.N (m2 + 1)) P.1) → (∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p Y x = 0) → ∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p' Y' x = 0 := by
  intro X Pr R Ch sel S mu cst L G m2 hL u hdis al p₀ p p' Y Y' hdeco hY h0 x
  obtain ⟨x', h1, h2⟩ := exists_transport X.K hdis p₀.deco.2 p.deco.2 (frsF sel mu p₀) (frsF sel mu p) (frsF sel mu p')
    (fun P => ((qOf P.1 : X.E) ^ cst.B)⁻¹) x
  rw [← h0 x']
  unfold XiCpl1
  rw [hdeco, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 := hL.psiInvX al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) _ ((frsF sel mu p P).symm (repY Y)) (h2 P)
  have e2 := hL.psiInv al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))
    ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) (fun i => intAt_of_mem_stdAt (hY P) i)
  rw [add_sub_cancel] at e1 e2
  rw [e1, e2]

end GlobalTheory.CplDead
