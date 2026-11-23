import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexStabilizerEqLocalRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexLevelUnipotentCoprimePrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.PsiCmp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eig_unique {F : GAf L n → V} (hF : F ≠ 0) {κ : GAf L n} {c d : ℂ} (h1 : Eig F κ c) (h2 : Eig F κ d) : c = d := by
  obtain ⟨g, hg⟩ : ∃ g, F g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF (funext h)
  have : c • F g = d • F g := by rw [← h1 g, ← h2 g]
  exact smul_left_injective ℂ hg this

theorem eig_mul {F : GAf L n → V} {a b : GAf L n} {c d : ℂ} (h1 : Eig F a c) (h2 : Eig F b d) : Eig F (a * b) (c * d) := by
  intro g
  rw [← mul_assoc, h2, h1, smul_smul, mul_comm]

theorem eig_ne_zero {F : GAf L n → V} (hF : F ≠ 0) {a : GAf L n} {c : ℂ} (h : Eig F a c) : c ≠ 0 := by
  rintro rfl
  apply hF
  funext g
  have := h (g * a⁻¹)
  simpa using this

theorem eig_inv {F : GAf L n → V} {a : GAf L n} {c : ℂ} (h : Eig F a c) (hc : c ≠ 0) : Eig F a⁻¹ c⁻¹ := by
  intro g
  have := h (g * a⁻¹)
  rw [inv_mul_cancel_right] at this
  rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem eig_one (F : GAf L n → V) : Eig F 1 1 := by
  intro g
  simp

def eigSub (F : GAf L n → V) (hF : F ≠ 0) : Subgroup (GAf L n) where
  carrier := {κ | ∃ c, Eig F κ c}
  mul_mem' := fun ⟨_, hc⟩ ⟨_, hd⟩ => ⟨_, eig_mul hc hd⟩
  one_mem' := ⟨1, eig_one F⟩
  inv_mem' := fun ⟨_, hc⟩ => ⟨_, eig_inv hc (eig_ne_zero hF hc)⟩

def eigChar (F : GAf L n → V) (hF : F ≠ 0) : eigSub F hF →* ℂˣ where
  toFun κ := Units.mk0 (Classical.choose κ.2) (eig_ne_zero hF (Classical.choose_spec κ.2))
  map_one' := Units.ext (eig_unique hF (Classical.choose_spec (1 : eigSub F hF).2) (eig_one F))
  map_mul' a b := Units.ext (eig_unique hF (Classical.choose_spec (a * b).2)
    (eig_mul (Classical.choose_spec a.2) (Classical.choose_spec b.2)))

theorem eigChar_spec {F : GAf L n → V} (hF : F ≠ 0) {κ : GAf L n} (h : κ ∈ eigSub F hF) {c : ℂ} (hc : Eig F κ c) :
    ((eigChar F hF ⟨κ, h⟩ : ℂˣ) : ℂ) = c :=
  eig_unique hF (Classical.choose_spec h) hc

end GlobalTheory.PsiCmp

noncomputable section
namespace GlobalTheory.PsiCmp

theorem tv_apply {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R) (a b : Fin n) :
    Matrix.transvection i j c a b = (if a = b then 1 else 0) + (if a = i ∧ b = j then c else 0) := by
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.transvection, Matrix.one_apply]
  · have h' : ¬(i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨rfl, rfl⟩
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, h', h]

def tvGL {n : ℕ} {R : Type} [CommRing R] {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    by
      have := Matrix.transvection_mul_transvection_same i j hij c (-c)
      rw [add_neg_cancel, Matrix.transvection_zero] at this
      exact this,
    by
      have := Matrix.transvection_mul_transvection_same i j hij (-c) c
      rw [neg_add_cancel, Matrix.transvection_zero] at this
      exact this⟩

theorem tvGL_val {n : ℕ} {R : Type} [CommRing R] {i j : Fin n} (hij : i ≠ j) (c : R) :
    ((tvGL hij c : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c := rfl

theorem tvGL_inv {n : ℕ} {R : Type} [CommRing R] {i j : Fin n} (hij : i ≠ j) (c : R) :
    (((tvGL hij c)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j (-c) := rfl

end GlobalTheory.PsiCmp

noncomputable section
namespace GlobalTheory.PsiCmp

def trivSub {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    Subgroup (GAf L n) where
  carrier := {κ | TrivOutside {v} κ}
  mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
  one_mem' := GlobalTheory.HeckeScalarSph.triv_one
  inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx

theorem idx {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (r p : ℕ) (J : Subgroup (GAf L n))
    (hp : p.Prime) (hsp : s.Above p) (hrn : r ≤ n)
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s r (s.loc n κ))) :
    Nat.Coprime (J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v)) p := by
  obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  set H := (J ⊓ trivSub n s.v).map (s.loc n) with hH
  have hmemH : ∀ g, g ∈ H ↔ NG.UniRT s r g := by
    intro g
    constructor
    · rintro ⟨κ, ⟨hκJ, hκT⟩, rfl⟩
      exact (hJ κ hκT).1 hκJ
    · intro hg
      obtain ⟨κ, ⟨hκT, hκ⟩, -⟩ := hlift g
      subst hκ
      exact ⟨κ, ⟨(hJ κ hκT).2 hg, hκT⟩, rfl⟩
  have hJH : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H) := by
    intro κ hκT
    constructor
    · intro hκJ
      exact ⟨κ, ⟨hκJ, hκT⟩, rfl⟩
    · rintro ⟨κ', ⟨hκ'J, hκ'T⟩, he⟩
      have : κ' = κ := (hlift (s.loc n κ)).unique ⟨hκ'T, he⟩ ⟨hκT, rfl⟩
      exact this ▸ hκ'J
  rw [GlobalTheory.T.relIndex_stabilizer_eq_local_relIndex L n s J H hJH]
  exact GlobalTheory.T.relIndex_levelUnipotent_coprime_prime L n s r p H hp hsp hrn hmemH

end GlobalTheory.PsiCmp

noncomputable section
namespace GlobalTheory.PsiCmp

theorem vle {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {α : Type} [DecidableEq α] (P : Prop) [Decidable P] (a b : α)
    {c : K} (hc : Valued.v c ≤ 1) : Valued.v ((if a = b then (1 : K) else 0) + (if P then c else 0)) ≤ 1 := by
  apply Valuation.map_add_le
  · split_ifs <;> simp
  · split_ifs <;> simp [hc]

theorem fractionFieldToGenericStalk_algebraMap_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (p m : ℕ) (θ : GAf L n ≃* GAf L n) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (F : GAf L n → V) (F' : GAf L n → V') (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (ψ₀ ψ₀' : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), p.Prime → s.Above p → m.Coprime p → 2 ≤ r → r ≤ n → FrameAut θ → F ≠ 0 → F' ≠ 0 → NG.IsPsi0 s ψ₀ → NG.IsPsi0 s ψ₀' → NG.LevelUni J χ s r ψ₀ ξ → NG.LevelUni J' χ' s r ψ₀' ξ' → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ : J', Eig F' κ (χ' κ : ℂˣ)) → (∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → ∃ c c' : ℂ, Eig F (θ κ) c ∧ Eig F' (θ κ) c' ∧ c ^ m = c' ^ m) → ∀ y, Valued.v y ≤ 1 → ψ₀ y = ψ₀' y := by
  intro L _ _ _ n r s p m θ V V' _ _ _ _ F F' J J' χ χ' ψ₀ ψ₀' ξ ξ' hp hsp hm h2r hrn hθ hF hF' hψ hψ' hJ hJ' hχ hχ' hH y hy
  classical
  set K := GlobalTheory.HeckeScalarSph.locK (L := L) n s.v with hKdef
  have memK : ∀ κ, κ ∈ K ↔ κ ∈ Umax L n ∧ TrivOutside {s.v} κ := fun κ => Iff.rfl
  have hθK : ∀ κ, θ κ ∈ K ↔ κ ∈ K := fun κ => by rw [memK, memK, hθ.1 κ, hθ.2 s.v κ]
  have hUK : ∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → κ ∈ K := fun κ hT hU =>
    ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hT).1 hU.1.1, hT⟩
  set Hs : Subgroup (GAf L n) := eigSub F hF ⊓ eigSub F' hF' ⊓ K with hHs
  have le1 : Hs ≤ eigSub F hF := le_trans inf_le_left inf_le_left
  have le2 : Hs ≤ eigSub F' hF' := le_trans inf_le_left inf_le_right
  let η : Hs →* ℂˣ := (powMonoidHom m).comp
    ((eigChar F hF).comp (Subgroup.inclusion le1) / (eigChar F' hF').comp (Subgroup.inclusion le2))
  have hη : ∀ (κ : GAf L n) (h : κ ∈ Hs) (c c' : ℂ), Eig F κ c → Eig F' κ c' → ((η ⟨κ, h⟩ : ℂˣ) : ℂ) = (c / c') ^ m := by
    intro κ h c c' hc hc'
    have e1 : ((eigChar F hF (Subgroup.inclusion le1 ⟨κ, h⟩) : ℂˣ) : ℂ) = c := eigChar_spec hF (le1 h) hc
    have e2 : ((eigChar F' hF' (Subgroup.inclusion le2 ⟨κ, h⟩) : ℂˣ) : ℂ) = c' := eigChar_spec hF' (le2 h) hc'
    simp only [η, MonoidHom.comp_apply, powMonoidHom_apply, MonoidHom.div_apply, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val]
    rw [e1, e2]
  have hUH : (J ⊓ K).map θ.toMonoidHom ≤ Hs := by
    rintro _ ⟨κ, ⟨hκJ, hκK⟩, rfl⟩
    obtain ⟨c, c', hc, hc', -⟩ := hH κ hκK.2 ((hJ.mem κ hκK.2).1 hκJ)
    exact ⟨⟨⟨c, hc⟩, ⟨c', hc'⟩⟩, (hθK κ).2 hκK⟩
  have hker : ((J ⊓ K).map θ.toMonoidHom).subgroupOf Hs ≤ η.ker := by
    rintro ⟨h, hmem⟩ hh
    rw [Subgroup.mem_subgroupOf] at hh
    obtain ⟨κ, ⟨hκJ, hκK⟩, hκ⟩ := hh
    rw [MonoidHom.mem_ker]
    obtain ⟨c, c', hc, hc', hcm⟩ := hH κ hκK.2 ((hJ.mem κ hκK.2).1 hκJ)
    apply Units.ext
    subst hκ
    rw [hη _ hmem c c' hc hc', div_pow, hcm, div_self (pow_ne_zero _ (eig_ne_zero hF' hc')), Units.val_one]
  have hidx : Nat.Coprime η.ker.index p := by
    have h1 : η.ker.index ∣ ((J ⊓ K).map θ.toMonoidHom).relIndex Hs := Subgroup.index_dvd_of_le hker
    have h2 : ((J ⊓ K).map θ.toMonoidHom).relIndex Hs ∣ ((J ⊓ K).map θ.toMonoidHom).relIndex K :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hUH inf_le_right)
    have hKθ : K.map θ.toMonoidHom = K := by
      ext κ
      rw [Subgroup.mem_map_equiv, ← hθK, MulEquiv.apply_symm_apply]
    have h3 : ((J ⊓ K).map θ.toMonoidHom).relIndex K = J.relIndex K := by
      have e := Subgroup.relIndex_map_map_of_injective (f := θ.toMonoidHom) (J ⊓ K) K θ.injective
      rw [hKθ, Subgroup.inf_relIndex_right] at e
      exact e
    exact Nat.Coprime.coprime_dvd_left (h3 ▸ (h1.trans h2)) (idx s r p J hp hsp hrn hJ.mem)
  have hn : 2 ≤ n := le_trans h2r hrn
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨x, ⟨hxT, hxA⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 (tvGL hne y)
  have hent : ∀ a b, ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b =
      (if a = b then 1 else 0) + (if a = i0 ∧ b = i1 then y else 0) := by
    intro a b
    rw [hxA, tvGL_val, tv_apply]
  have hentI : ∀ a b, (((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b =
      (if a = b then 1 else 0) + (if a = i0 ∧ b = i1 then -y else 0) := by
    intro a b
    rw [hxA, tvGL_inv, tv_apply]
  have hGL : s.loc n x ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · show _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hent]
      exact vle _ a b hy
    · show _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hentI]
      exact vle _ a b (by rw [Valuation.map_neg]; exact hy)
  have hUni : NG.UniRT s r (s.loc n x) := by
    refine ⟨⟨hGL, fun a b ha hb => ?_⟩, fun a b ha hb => ⟨fun hba => ?_, fun hab => ?_⟩⟩
    · have h1 : a ≠ b := by
        rintro rfl
        omega
      have h2 : ¬(a = i0 ∧ b = i1) := by
        rintro ⟨rfl, -⟩
        simp [i0] at ha
        omega
      rw [hent, if_neg h1, if_neg h2, add_zero, map_zero]
      exact zero_lt_one
    · have h1 : a ≠ b := by
        rintro rfl
        omega
      have h2 : ¬(a = i0 ∧ b = i1) := by
        rintro ⟨rfl, -⟩
        simp [i0] at hba
      rw [hent, if_neg h1, if_neg h2, add_zero, map_zero]
      exact zero_lt_one
    · subst hab
      have h2 : ¬(a = i0 ∧ a = i1) := by
        rintro ⟨h3, h4⟩
        exact hne (h3.symm.trans h4)
      rw [hent, if_pos rfl, if_neg h2, add_zero, sub_self, map_zero]
      exact zero_lt_one
  have hdet : NG.detDD s r (s.loc n x) = 1 := by
    unfold NG.detDD
    have : (Matrix.of fun a b : {z : Fin n // r ≤ z.val} =>
        ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
          Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
      ext a b
      have h2 : ¬(a.1 = i0 ∧ b.1 = i1) := by
        rintro ⟨h3, -⟩
        have := a.2
        rw [h3] at this
        simp [i0] at this
        omega
      rw [Matrix.of_apply, hent, if_neg h2, add_zero, Matrix.one_apply]
      simp only [Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hsup : NG.supDiag s r (s.loc n x) = y := by
    unfold NG.supDiag
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single i1]
    · rw [if_pos ⟨rfl, by simp [i1]; omega⟩, hent, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · intro b _ hb
      split_ifs with h
      · rw [hent, if_neg (fun h' => by simp [i0, Fin.ext_iff] at h'; omega), if_neg (fun h' => hb h'.2), add_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with h
      · rw [hent, if_neg (fun h' => by simp [Fin.ext_iff] at h'; omega), if_neg (fun h' => ha h'.1), add_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hxJ : x ∈ J := (hJ.mem x hxT).2 hUni
  have hxJ' : x ∈ J' := (hJ'.mem x hxT).2 hUni
  have hχx : ((χ ⟨x, hxJ⟩ : ℂˣ) : ℂ) = ψ₀ y := by
    rw [hJ.chr x hxJ hxT 1 (by rw [hdet, Units.val_one]), hsup, map_one, Units.val_one, mul_one]
  have hχx' : ((χ' ⟨x, hxJ'⟩ : ℂˣ) : ℂ) = ψ₀' y := by
    rw [hJ'.chr x hxJ' hxT 1 (by rw [hdet, Units.val_one]), hsup, map_one, Units.val_one, mul_one]
  have hxH : x ∈ Hs := ⟨⟨⟨_, hχ ⟨x, hxJ⟩⟩, ⟨_, hχ' ⟨x, hxJ'⟩⟩⟩, hUK x hxT hUni⟩
  have hηx := hη x hxH _ _ (hχ ⟨x, hxJ⟩) (hχ' ⟨x, hxJ'⟩)
  rw [hχx, hχx'] at hηx
  have hpow : ((η ⟨x, hxH⟩ : ℂˣ) : ℂ) ^ η.ker.index = 1 := by
    have := Subgroup.pow_index_mem η.ker ⟨x, hxH⟩
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hz1 : (ψ₀ y / ψ₀' y) ^ (m * η.ker.index) = 1 := by rw [pow_mul, ← hηx, hpow]
  have hvp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    have e1 : ((p : s.v.adicCompletion (maximalRealSubfield L))) =
        algebraMap (𝓞 (maximalRealSubfield L)) (s.v.adicCompletion (maximalRealSubfield L)) (p : 𝓞 (maximalRealSubfield L)) :=
      (map_natCast _ p).symm
    rw [e1]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := maximalRealSubfield L) s.v
      (p : 𝓞 (maximalRealSubfield L))).trans_lt ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hsp)
  have hpy : Valued.v (p • y) < 1 := by
    rw [nsmul_eq_mul, map_mul]
    calc Valued.v (p : s.v.adicCompletion (maximalRealSubfield L)) * Valued.v y
        ≤ Valued.v (p : s.v.adicCompletion (maximalRealSubfield L)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hvp
  have hψp : ψ₀ y ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, hψ.1 _ hpy]
  have hψp' : ψ₀' y ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, hψ'.1 _ hpy]
  have hne0 : ψ₀' y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hψp'
    exact zero_ne_one hψp'
  have hzp : (ψ₀ y / ψ₀' y) ^ p = 1 := by rw [div_pow, hψp, hψp', div_one]
  have hz : ψ₀ y / ψ₀' y = 1 := by
    have : (ψ₀ y / ψ₀' y) ^ (Nat.gcd (m * η.ker.index) p) = 1 := pow_gcd_eq_one.2 ⟨hz1, hzp⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.mul hm hidx), pow_one] at this
  exact (div_eq_one_iff_eq hne0).1 hz

end GlobalTheory.PsiCmp
