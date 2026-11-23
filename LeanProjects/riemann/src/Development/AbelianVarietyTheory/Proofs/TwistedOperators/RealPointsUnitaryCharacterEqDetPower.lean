import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIsotropicOrOneClass
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UCharDet
open GlobalTheory.UTrans
open scoped ComplexOrder

theorem hf_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x y = starRingEnd ℂ (star x ⬝ᵥ (H *ᵥ y)) := by
  simp only [hf, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem exists_aniso {n : ℕ} (hn : 0 < n) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    ∃ v : Fin n → ℂ, star v ⬝ᵥ (H *ᵥ v) ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  have e := hH.mulVec_eigenvectorBasis i
  have hl : hH.eigenvalues i ≠ 0 := by
    intro h0
    apply hd
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0]; simp)
  have hv : (hH.eigenvectorBasis i).ofLp ≠ 0 := by
    intro h0
    have := hH.eigenvectorBasis.orthonormal.ne_zero i
    apply this
    rw [← WithLp.ofLp_eq_zero]
    exact h0
  refine ⟨(hH.eigenvectorBasis i).ofLp, ?_⟩
  rw [e, dotProduct_smul]
  intro h0
  rcases smul_eq_zero.1 h0 with h | h
  · exact hl h
  · exact hv (dotProduct_star_self_eq_zero.1 h)

theorem isU_iff {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) :
    IsU (starRingEnd ℂ) (H.map (starRingEnd ℂ)) g ↔ g ∈ Formalism.QuantumDeterminants.UH H := by
  have key : ∀ x y : Fin n → ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (g *ᵥ x) (g *ᵥ y) =
      starRingEnd ℂ (star x ⬝ᵥ ((gᴴ * H * g) *ᵥ y)) := fun x y => by
    rw [hf_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  constructor
  · intro h
    show gᴴ * H * g = H
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, hf_eq] at this
    have := congrArg (starRingEnd ℂ) this
    simpa [Matrix.mulVec_single, Pi.single_apply] using this
  · intro h x y
    have h' : gᴴ * H * g = H := h
    rw [key, h', hf_eq]

theorem isHerm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    IsHerm (starRingEnd ℂ) (H.map (starRingEnd ℂ)) where
  invol a := Complex.conj_conj a
  ne_id := ⟨Complex.I, by
    intro h
    have := congrArg Complex.im h
    norm_num at this⟩
  herm a b := by
    simp only [Matrix.map_apply, Complex.conj_conj]
    have := congrFun (congrFun hH b) a
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    rw [← this, Complex.conj_conj]
  det_ne := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hd

theorem iso_or_one_class {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) :
    (∃ z : Fin n → ℂ, z ≠ 0 ∧ hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) z z = 0) ∨
      ∀ x y : Fin n → ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x x ≠ 0 →
        hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) y y ≠ 0 →
        ∃ a : ℂ, hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) y y =
          starRingEnd ℂ a * a * hf (starRingEnd ℂ) (H.map (starRingEnd ℂ)) x x :=
  GlobalTheory.UTrans.real_isotropic_or_one_class ℝ ℂ (starRingEnd ℂ) Complex.I
    (fun a => by simp) Complex.I_ne_zero (by simp)
    (fun x => ⟨x.re, x.im, by simp [Complex.re_add_im]⟩) ⟨RingEquiv.refl ℝ⟩ n _
    (isHerm H hH hd).herm

theorem mul_mem {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem one_mem {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem kill {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0) (c : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ g' ∈ Formalism.QuantumDeterminants.UH H, c (g * g') = c g * c g')
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ‖c g‖ = 1) (γ : Matrix (Fin n) (Fin n) ℂ) (hγ : γ ∈ Formalism.QuantumDeterminants.UH H)
    (hdet : γ.det = 1) : c γ = 1 := by
  have hne : ∀ g ∈ Formalism.QuantumDeterminants.UH H, c g ≠ 0 := fun g hg h0 => by
    have := h1 g hg
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  let X : Matrix (Fin n) (Fin n) ℂ → ℂˣ := fun g => if h : c g = 0 then 1 else Units.mk0 (c g) h
  have hX : ∀ g ∈ Formalism.QuantumDeterminants.UH H, (X g : ℂ) = c g := fun g hg => by
    simp only [X, dif_neg (hne g hg), Units.val_mk0]
  have key := GlobalTheory.UTrans.char_eq_one_of_det_eq_one ℂ n (starRingEnd ℂ) (H.map (starRingEnd ℂ)) (isHerm H hH hd)
    (iso_or_one_class H hH hd) ℂˣ X (fun a b ha hb => by
      rw [isU_iff] at ha hb
      apply Units.ext
      rw [Units.val_mul, hX _ ha, hX _ hb, hX _ (mul_mem ha hb), hm _ ha _ hb])
    γ ((isU_iff H γ).2 hγ) hdet
  rw [← hX γ hγ, key, Units.val_one]

theorem norm_det {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hd : H.det ≠ 0) (hg : g ∈ Formalism.QuantumDeterminants.UH H) :
    ‖g.det‖ = 1 := by
  have hg' : gᴴ * H * g = H := hg
  have e := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at e
  have e2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hd
    linear_combination e
  have e3 : Complex.normSq g.det = 1 := by
    have := Complex.mul_conj g.det
    rw [mul_comm] at this
    exact_mod_cast (this.symm.trans e2)
  rw [Complex.normSq_eq_norm_sq] at e3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e3

theorem char_eq_det_zpow {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hd : H.det ≠ 0)
    (c : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ g' ∈ Formalism.QuantumDeterminants.UH H, c (g * g') = c g * c g')
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.UH H, ‖c g‖ = 1) (hc : ContinuousOn c (Formalism.QuantumDeterminants.UH H)) :
    ∃ m : ℤ, ∀ g ∈ Formalism.QuantumDeterminants.UH H, c g = g.det ^ m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun g hg => by rw [zpow_zero]; exact kill H hH hd c hm h1 g hg (Matrix.det_isEmpty)⟩
  obtain ⟨v, hv⟩ := exists_aniso hn H hH hd
  set σ := starRingEnd ℂ
  set G := H.map σ
  have hG := isHerm H hH hd
  have hx : hf σ G v v ≠ 0 := by
    rw [hf_eq]
    exact (map_ne_zero _).2 hv
  let refl : Circle → Matrix (Fin n) (Fin n) ℂ := fun t => tv σ G v (((t : ℂ) - 1) / hf σ G v v)
  have hu : ∀ t : Circle, (t : ℂ) * σ t = 1 := fun t => by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hU : ∀ t, refl t ∈ Formalism.QuantumDeterminants.UH H := fun t => (isU_iff H _).1 (CharDet.isU_refl hG hx (hu t))
  have hcont : Continuous refl := by
    simp only [refl, tv]
    fun_prop
  have c1 : c 1 = 1 := kill H hH hd c hm h1 1 (one_mem H) Matrix.det_one
  let ψ : Circle →* Circle :=
    { toFun := fun t => ⟨c (refl t), by simpa [Submonoid.unitSphere] using h1 _ (hU t)⟩
      map_one' := by
        apply Subtype.ext
        show c (refl 1) = 1
        simp only [refl, Circle.coe_one]
        rw [CharDet.refl_one, c1]
      map_mul' := fun s t => by
        apply Subtype.ext
        show c (refl (s * t)) = c (refl s) * c (refl t)
        rw [← hm _ (hU s) _ (hU t)]
        simp only [refl, Circle.coe_mul]
        rw [CharDet.refl_mul _ _ hx] }
  have hψ : Continuous ψ := Continuous.subtype_mk (hc.comp_continuous hcont hU) _
  obtain ⟨m, hm'⟩ := GlobalTheory.circle_hom_eq_zpow ψ hψ
  have hr : ∀ t : Circle, c (refl t) = (t : ℂ) ^ m := fun t => by
    have := congrArg (fun s : Circle => (s : ℂ)) (hm' t)
    rw [Circle.coe_zpow] at this
    exact this
  refine ⟨m, fun g hg => ?_⟩
  let e : Circle := ⟨g.det, by simpa [Submonoid.unitSphere] using norm_det hd hg⟩
  have hd0 : g.det ≠ 0 := fun h0 => by
    have := norm_det hd hg
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have k := kill H hH hd c hm h1 _ (mul_mem (hU e⁻¹) hg) (by
    rw [Matrix.det_mul]
    simp only [refl]
    rw [CharDet.refl_det _ hx, Circle.coe_inv]
    exact inv_mul_cancel₀ hd0)
  rw [hm _ (hU _) _ hg, hr, Circle.coe_inv] at k
  have k2 := eq_inv_of_mul_eq_one_right k
  rw [k2, _root_.inv_zpow, inv_inv]

end GlobalTheory.UCharDet

namespace GlobalTheory.AdSpan

theorem char_eq_detPow : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → V.SigOK → ∀ z : GA D V → ℂ, (∀ a ∈ GinfC V, ∀ a' ∈ GinfC V, z (a * a') = z a * z a') → (∀ a ∈ GinfC V, ‖z a‖ = 1) → ContinuousOn z (GinfC V : Set (GA D V)) → ∃ m : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, z a = detPow θ V m a := by
  intro D θ V hθ _ z hz hz1 hzc
  obtain ⟨L, hL1, hLmul, hLc, hLarch, hLinv, -, -, -, hHd⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hsing : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
    intro τ g hg ρ
    by_cases h : ρ = τ
    · subst h
      rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h]
      exact GlobalTheory.UCharDet.one_mem _
  have hc : ∀ τ, ∃ m : ℤ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), z (L (Pi.mulSingle τ g)) = g.det ^ m := by
    intro τ
    refine GlobalTheory.UCharDet.char_eq_det_zpow (gramAt D V τ) (hHd τ).1 (hHd τ).2 (fun g => z (L (Pi.mulSingle τ g)))
      (fun g hg g' hg' => ?_) (fun g hg => hz1 _ (hL1 _ (hsing τ g hg)).1) ?_
    · show z (L (Pi.mulSingle τ (g * g'))) = z (L (Pi.mulSingle τ g)) * z (L (Pi.mulSingle τ g'))
      rw [Pi.mulSingle_mul, hLmul _ (hsing τ g hg) _ (hsing τ g' hg'),
        hz _ (hL1 _ (hsing τ g hg)).1 _ (hL1 _ (hsing τ g' hg')).1]
    · have hcs : Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
          (Pi.mulSingle τ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
        refine continuous_pi fun ρ => ?_
        by_cases h : ρ = τ
        · subst h
          simp only [Pi.mulSingle_eq_same]
          exact continuous_id
        · simp only [Pi.mulSingle_eq_of_ne h]
          exact continuous_const
      exact hzc.comp (hLc.comp hcs.continuousOn fun g hg => hsing τ g hg) fun g hg => (hL1 _ (hsing τ g hg)).1
  choose m hm using hc
  refine ⟨m, fun a ha => ?_⟩
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => Formalism.L2.Pj.archM V (θ τ) a with hu_def
  have hu : u ∈ GlobalTheory.HolDict.UG (gramAt D V) := hLarch a
  have hz0 : ∀ b ∈ GinfC V, z b ≠ 0 := fun b hb h0 => by
    have := hz1 b hb
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hone : (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D V) :=
    fun τ => GlobalTheory.UCharDet.one_mem _
  have zL1 : z (L 1) = 1 := by
    have e1 : L 1 = L 1 * L 1 := by simpa using hLmul 1 hone 1 hone
    have m1 := (hL1 _ hone).1
    have e2 := hz _ m1 _ m1
    rw [← e1] at e2
    exact (mul_eq_left₀ (hz0 _ m1)).1 e2.symm
  let fam : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun s τ => if τ ∈ s then u τ else 1
  have hfam : ∀ s, fam s ∈ GlobalTheory.HolDict.UG (gramAt D V) := fun s τ => by
    simp only [fam]
    split_ifs
    · exact hu τ
    · exact GlobalTheory.UCharDet.one_mem _
  have key : ∀ s : Finset D.what₂.Tau, z (L (fam s)) = ∏ τ ∈ s, (u τ).det ^ m τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : fam ∅ = 1 := funext fun τ => by simp [fam]
      rw [this, Finset.prod_empty]
      exact zL1
    | insert b s hb ih =>
      have e : fam (insert b s) = Pi.mulSingle b (u b) * fam s := funext fun τ => by
        by_cases h : τ = b
        · subst h
          simp [fam, hb]
        · simp [fam, h]
      rw [e, hLmul _ (hsing b _ (hu b)) _ (hfam s), hz _ (hL1 _ (hsing b _ (hu b))).1 _ (hL1 _ (hfam s)).1,
        hm b _ (hu b), ih, Finset.prod_insert hb]
  have hall : fam Finset.univ = u := funext fun τ => by simp [fam]
  have := key Finset.univ
  rw [hall, hLinv a ha] at this
  rw [this]
  rfl

end GlobalTheory.AdSpan
