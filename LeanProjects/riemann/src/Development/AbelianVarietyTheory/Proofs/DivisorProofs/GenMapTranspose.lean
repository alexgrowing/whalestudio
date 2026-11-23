import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.LatOf

open GlobalTheory.LatVac

variable {D : D7}

def aMul {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Λ, w = a • v}

theorem smul_mem_aMul {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {v : Fin n → D.host.E} (hv : v ∈ Λ) : a • v ∈ aMul Λ :=
  Submodule.subset_span ⟨a, ha, v, hv, rfl⟩

theorem aMul_induction {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {p : (Fin n → D.host.E) → Prop}
    (mem : ∀ a ∈ D.host.AA, ∀ v ∈ Λ, p (a • v)) (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    {w : Fin n → D.host.E} (hw : w ∈ aMul Λ) : p w := by
  have key : ∀ c : 𝓞 D.host.E, p (c • w) := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hw
      intro c
      rw [smul_comm]
      exact mem a ha _ (Λ.smul_mem c hv)
    | zero => intro c; rw [smul_zero]; exact zero
    | add x y _ _ hx hy => intro c; rw [smul_add]; exact add _ _ (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  have := key 1
  rwa [one_smul] at this

theorem aMul_fg {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) : (aMul Λ).FG := by
  have hA : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    (isNoetherian_submodule.1 (FractionalIdeal.isNoetherian D.host.AA)) _ le_rfl
  have := hA.map₂ ((LinearMap.lsmul D.host.E (Fin n → D.host.E)).restrictScalars₁₂ (𝓞 D.host.E) (𝓞 D.host.E)) h
  rw [Submodule.map₂_eq_span_image2] at this
  unfold aMul
  convert this using 2
  ext w
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    exact ⟨a, ha, v, hv, rfl⟩
  · rintro ⟨a, ha, v, hv, rfl⟩
    exact ⟨a, ha, v, hv, rfl⟩

def frm (T : HSp D) (t y : Fin T.rank → D.host.E) : D.host.E := ∑ c, ∑ d, star (t c) * T.gram c d * y d

theorem frm_add_left (T : HSp D) (t t' y : Fin T.rank → D.host.E) : frm T (t + t') y = frm T t y + frm T t' y := by
  simp only [frm, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem frm_add_right (T : HSp D) (t y y' : Fin T.rank → D.host.E) : frm T t (y + y') = frm T t y + frm T t y' := by
  simp only [frm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frm_smul_left (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    frm T (e • t) y = star e * frm T t y := by
  simp only [frm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, star_mul']
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frm_smul_right (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    frm T t (e • y) = e * frm T t y := RatDual.form_smul T e t y

theorem aMul_selfDual (T : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T Λ)
    (x : Fin T.rank → D.host.E) :
    x ∈ aMul Λ ↔ ∀ y ∈ aMul Λ, ∃ k : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * frm T y x) = k := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := Formalism.L2.Pj.AA_ne_zero hP D
  constructor
  · intro hx y hy
    refine Formalism.L2.Pj.trace_int_of_mem hP D ?_
    refine aMul_induction (p := fun x => frm T y x ∈ Formalism.L2.Pj.NAA D) ?_ ?_ ?_ hx
    · intro a' ha' t' ht'
      refine aMul_induction (p := fun y => frm T y (a' • t') ∈ Formalism.L2.Pj.NAA D) ?_ ?_ ?_ hy
      · intro a ha t ht
        obtain ⟨q, hq⟩ := (hT.2 t').1 ht' t ht
        have hq' : frm T t t' = q := hq.symm
        have hs : star a = D.host.conj a := bridge_star_holds D.R D.host a
        have e : frm T (a • t) (a' • t') = q • (a' * D.host.conj a) := by
          rw [frm_smul_left, frm_smul_right, hq', hs, Algebra.smul_def]
          change _ = (q : D.host.E) * _
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha' (Formalism.L2.Pj.conj_mem_AAbar D ha))
      · simp [frm]
      · intro u v hu hv; rw [frm_add_left]; exact add_mem hu hv
    · simp [frm]
    · intro u v hu hv; rw [frm_add_right]; exact add_mem hu hv
  · intro h
    have h5 : ∀ t ∈ Λ, frm T t x ∈ D.host.AA := fun t ht =>
      RatDual.mem_AA_of_trace D _ fun a ha => by
        rw [← frm_smul_left]; exact h _ (smul_mem_aMul ha ht)
    have h6 : ∀ b ∈ D.host.AA⁻¹, b • x ∈ Λ := by
      intro b hb
      refine (hT.2 _).2 fun t ht => ?_
      rw [RatDual.form_smul]
      have := FractionalIdeal.mul_mem_mul hb (h5 t ht)
      rw [inv_mul_cancel₀ hAA, FractionalIdeal.mem_one_iff] at this
      exact this
    have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • x ∈ aMul Λ := by
      intro e he
      refine FractionalIdeal.mul_induction_on (C := fun e => e • x ∈ aMul Λ) he (fun a ha c hc => ?_)
        (fun u w hu hw => ?_)
      · show (a * c) • x ∈ aMul Λ
        rw [mul_smul]; exact smul_mem_aMul ha (h6 c hc)
      · show (u + w) • x ∈ aMul Λ
        rw [add_smul]; exact add_mem hu hw
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    rwa [one_smul] at this

theorem EF_eq (T : HSp D) (X : Data D.host.E T.rank) (hX : IsMod T rfl X) (x y : Fin T.rank → D.host.E) :
    EF X x y = -Algebra.trace ℚ D.host.E (D.host.xi0 * frm T y x) := by
  rw [EF_def, hX.kap, hX.model.1, ← map_neg]
  congr 1
  have : herm (-(Matrix.reindex (finCongr (rfl : T.rank = T.rank)) (finCongr rfl) T.gram).transpose) x y
      = -frm T y x := by
    unfold herm frm
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    change x b * -(T.gram a b) * star (y a) = _
    ring
  rw [this]
  ring

theorem selfD_aMul (T : HSp D) (X : Data D.host.E T.rank) (hX : IsMod T rfl X)
    {Λ : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T Λ) : SelfD X (aMul Λ) := by
  refine ⟨aMul_fg hT.1.fg, fun x => (aMul_selfDual T hT x).trans
    (forall_congr' fun y => forall_congr' fun _ => ?_)⟩
  rw [EF_eq T X hX]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨-k, by rw [hk, Int.cast_neg]⟩
  · rintro ⟨k, hk⟩; exact ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩

theorem fg_of_star {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (hs : ∀ v, v ∈ Λ' ↔ star v ∈ Λ) : Λ'.FG := by
  obtain ⟨s, hfin, rfl⟩ := Submodule.fg_def.1 h
  refine Submodule.fg_def.2 ⟨star '' s, hfin.image _, le_antisymm (Submodule.span_le.2 ?_) fun v hv => ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (hs _).2 (by rw [star_star]; exact Submodule.subset_span hw)
  · have key : ∀ w ∈ Submodule.span (𝓞 D.host.E) s, star w ∈ Submodule.span (𝓞 D.host.E) (star '' s) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
      | zero => rw [star_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
      | smul c x _ hx =>
        have e : star (c • x) = Formalism.L2.Pj.barE D c • star x := by
          funext i
          change star ((c : D.host.E) * x i) = ((Formalism.L2.Pj.barE D c : 𝓞 D.host.E) : D.host.E) * star (x i)
          rw [star_mul', Formalism.L2.Pj.barE_eq_star]
        rw [e]
        exact Submodule.smul_mem _ _ hx
    have := key _ ((hs v).1 hv)
    rwa [star_star] at this

theorem unimod_of_star (S : HSp D) (hS : S.gram = 1) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (h : IsSelfDualC S Λ) (hs : ∀ v, v ∈ Λ' ↔ star v ∈ Λ) :
    (⟨Λ'⟩ : Formalism.L2.Pj.GenLat D.host.E S.rank).Unimod := by
  intro v
  change v ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j
  have e : ∀ x : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * S.gram i j * (star v) j = ∑ j, star (v j) * (star x) j := by
    intro x
    simp [hS, Matrix.one_apply, mul_comm]
  rw [hs, h.2]
  simp only [e]
  constructor
  · intro H w hw
    have := H _ ((hs w).1 hw)
    rwa [star_star] at this
  · intro H x hx
    exact H _ ((hs _).2 (by rwa [star_star]))

theorem genMap_transpose (S T : HSp D) (hS : S.gram = 1) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) : (genMap S T a s t)ᵀ = vecMulVec (star s) (a • t) := by
  ext j i
  simp [genMap, hS, Matrix.one_apply, vecMulVec_apply, mul_comm]

theorem mem_latRat_iff (S T : HSp D) (hS : S.gram = 1) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hs : ∀ v, v ∈ Λ' ↔ star v ∈ Λ)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    γ ∈ latRat S T (Λ : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      γᵀ ∈ tens Λ' (aMul ΛT) := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs', t, ht, rfl⟩ := hw
      rw [genMap_transpose S T hS]
      exact AddSubgroup.subset_closure ⟨_, (hs _).2 (by rwa [star_star]), _, smul_mem_aMul ha ht, rfl⟩
    | zero => rw [transpose_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [transpose_add]; exact add_mem hx hy
    | neg x _ hx => rw [transpose_neg]; exact neg_mem hx
  · intro h
    have key : ∀ y ∈ tens Λ' (aMul ΛT),
        yᵀ ∈ latRat S T (Λ : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro y h
      induction h using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨v, hv, u, hu, rfl⟩ := hw
        refine aMul_induction (p := fun u => (vecMulVec v u)ᵀ ∈
          latRat S T (Λ : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) ?_ ?_ ?_ hu
        · intro a ha t ht
          have e := genMap_transpose S T hS a (star v) t
          rw [star_star] at e
          rw [← e, transpose_transpose]
          exact AddSubgroup.subset_closure ⟨a, ha, _, (hs v).1 hv, t, ht, rfl⟩
        · have e : (vecMulVec v (0 : Fin T.rank → D.host.E))ᵀ = 0 := Matrix.ext fun _ _ => mul_zero _
          rw [e]; exact zero_mem _
        · intro x y hx hy
          rw [vecMulVec_add, transpose_add]; exact add_mem hx hy
      | zero => rw [transpose_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [transpose_add]; exact add_mem hx hy
      | neg x _ hx => rw [transpose_neg]; exact neg_mem hx
    exact key _ h

theorem eq_of_parts {m n : ℕ} {u u' : Formalism.IndefR.Datum.Mx D m n} (h1 : u.map (infPart D) = u'.map (infPart D))
    (h2 : u.map (finPart D) = u'.map (finPart D)) : u = u' := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem finTens_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finTens 1 M ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  refine ⟨fun h => ?_, finTens_mem_latO (one_mem_intAf _)⟩
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have h1 := char_sympl_eq_one hψ hS hT h (finTens_mem_latO (one_mem_intAf _) hℓ)
  rw [symplO_finTens, one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem isLatOf_tens : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → IsLatOf V W hr (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) (tens Λ' L) ∧ SelfD X L ∧ (⟨Λ'⟩ : Formalism.L2.Pj.GenLat D.host.E V.rank).Unimod ∧ Λ'.FG := by
  intro D ψ θ V W r g hr X bas idx hψ _ hV _ hX _ ΛV ΛW Λ' L hΛV hΛW hs hL
  subst hr
  have hL' : L = aMul ΛW := by
    rw [hL (aMul ΛW) rfl]
    exact Submodule.map_id _
  subst hL'
  have hinf : ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True,
      u.map (infPart D) = 0 := fun u hu => Matrix.ext fun i j => infPart_of_mem hu i j
  refine ⟨⟨hinf, ⟨_, GlobalTheory.LatOpen.isOpen_nsmul_latO D V W ΛV ΛW hΛV hΛW 1 one_pos, fun u hu => ⟨fun h => ?_, ?_⟩⟩,
    fun γ u hu => ?_⟩, selfD_aMul W X hX hΛW, unimod_of_star V hV hΛV hs, fg_of_star hΛV.1.fg hs⟩
  · refine ⟨u, h, ?_⟩
    rw [one_smul, sub_self]
    exact Matrix.ext fun _ _ => RingHom.map_zero (finPart D)
  · rintro ⟨l, hl, h⟩
    have : u = l := by
      refine eq_of_parts (hu.trans (hinf l hl).symm) (Matrix.ext fun i j => ?_)
      have h1 : finPart D (u i j - l i j) = 0 := by
        have := congrFun (congrFun h i) j
        rwa [one_smul] at this
      rw [RingHom.map_sub, sub_eq_zero] at h1
      exact h1
    rwa [this]
  · have : u = finTens 1 γ :=
      eq_of_parts (hu.1.trans (Matrix.ext fun i j => (infPart_pair _ _).symm)) (hu.2.trans rfl)
    rw [this, finTens_mem_iff hψ hΛV hΛW]
    exact mem_latRat_iff V W hV ΛW hs γ

end GlobalTheory.AdTh.LatOf

end
