import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.CrPer

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem eq_const_add_X_mul (bk : BK K) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1)
    (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ) (hκ : IsDiscMap (C : Wq l bk.a →+* bk.S) κ) (x : bk.DS ρ) :
    ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul l K bk ρ h0 h1 κ hκ x

theorem isDiscMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'} {u'' : A''}
    {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {F' : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap f F) (hF' : IsDiscMap f' F') :
    IsDiscMap (f'.comp f) (F'.comp F) :=
  ⟨fun a => by simp [hF.ext, hF'.ext], fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem dvd_gal_sub (bk : BK K) (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (Per.σA (g : GQ l)) G)
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hi : IsDiscMap bk.ev i) (x : bk.DS bk.ρ₀) :
    bk.iS X ∣ G (i x) - i x := by
  obtain ⟨hmap, -, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨κ, hκ⟩ := hmap (Wq l bk.a) bk.S C 0 X 1 bk.ρ₀ 0 hρ0 (by simp) (by simp)
  obtain ⟨c, x₁, rfl⟩ := eq_const_add_X_mul bk bk.ρ₀ hρ0 hρ1 κ hκ x
  have hc : G (i (κ c)) = i (κ c) := by
    have h1 : IsDiscMap ((Per.σA (g : GQ l)).comp (bk.ev.comp C)) ((G.comp i).comp κ) :=
      isDiscMap_comp hκ (isDiscMap_comp hi hG)
    have h2 : IsDiscMap (bk.ev.comp C) (i.comp κ) := isDiscMap_comp hκ hi
    have e : (Per.σA (g : GQ l)).comp (bk.ev.comp C) = bk.ev.comp C :=
      RingHom.ext fun w => by simp [bk.ev_C, bk.gal_w]
    rw [e] at h1
    exact RingHom.congr_fun (h1.unique h2) c
  obtain ⟨w, hw⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  have hX : i (toDisc l (X : bk.S) bk.ρ₀ X) = bk.iS X := hi.ext X
  have hGX : G (bk.iS X) = bk.iS X * bk.iA w := by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)) = _
    rw [hG.ext, hw, map_mul]; rfl
  rw [map_add i, map_mul i, hX, map_add G, map_mul G, hc, hGX]
  exact ⟨bk.iA w * G (i x₁) - i x₁, by ring⟩

end GlobalTheory.BKLim.CrPer

open GlobalTheory.BKLim.CrPer in

theorem GlobalTheory.BKLim.Frame.isCr_of_wSeed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  intro l _ K bk τ _ d ρ _ s N F Y Z _ hZ _ hG hκ g i j
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨Gm, hGm⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
  obtain ⟨im, him⟩ := hmap bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by simp) (by simp)
  have key := hG g Gm im hGm him
  rw [hκ g, one_mul] at key
  set q := Ideal.Quotient.mk (Ideal.span {bk.iS X}) with hqdef
  have hq : ∀ x, q (Gm (im x)) = q (im x) := fun x =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (dvd_gal_sub bk _ Gm hGm im him x))
  have hqS : ∀ a : bk.S, q (Gm (bk.iS a)) = q (bk.iS a) := fun a => by
    have h := hq (toDisc l (X : bk.S) bk.ρ₀ a)
    rwa [him.ext] at h
  have hl : IsUnit ((l : bk.DA bk.ρ₀)) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hu0 : q (bk.iS X) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hE : IsUnit (q (bk.iS bk.E)) := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have e1 : bk.E = X * PowerSeries.mk (fun p => coeff (p + 1) bk.E) + C ((l : Wq l bk.a) * w) := by
      conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
      rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
    rw [e1]
    simp only [map_add, map_mul, map_natCast, hu0, zero_mul, zero_add]
    exact (hl.map q).mul ((w.isUnit.map (C : Wq l bk.a →+* bk.S)).map (q.comp bk.iS))
  have hsm : ∀ (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), (c • M).map q = q c • M.map q :=
    fun c M => by ext a b; simp
  set P := s.X.map bk.iS * Z.map im with hPdef
  have hPG : (P.map Gm).map q = P.map q := by
    ext a b
    simp only [hPdef, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, hq, hqS]
  have hPu : IsUnit (P.map q) := by
    rw [hPdef, Matrix.map_mul]
    refine IsUnit.mul ?_ ?_
    · have e : (s.X.map bk.iS).map q = (q.comp bk.iS).mapMatrix s.X := by ext; rfl
      rw [e, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
      have hd := congrArg Matrix.det s.X_mul
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
      have h2 : IsUnit ((q.comp bk.iS) (s.X.det * s.X'.det)) := by
        rw [hd]
        simp only [map_pow, map_mul, map_natCast, RingHom.comp_apply]
        exact ((((hl.map q).pow _).mul (hE.pow _)).pow _)
      rw [map_mul] at h2
      exact isUnit_of_mul_isUnit_left h2
    · have e : (Z.map im).map q = (q.comp im).mapMatrix Z := by ext; rfl
      rw [e]
      exact hZ.map _
  have k2 := congrArg (fun M => Matrix.map M q) key
  simp only [hsm, Matrix.map_mul, hqS] at k2
  rw [hPG] at k2
  simp only [map_pow, hqS] at k2
  have k3 : q (bk.iS bk.E) ^ s.N • (P.map q * (((F.ε g).map bk.iA).map q - 1)) = 0 := by
    rw [mul_sub, mul_one, smul_sub, k2, sub_self]
  rw [(hE.pow _).smul_eq_zero, hPu.mul_right_eq_zero, sub_eq_zero] at k3
  have k5 : q (bk.iA ((F.ε g - 1) i j)) = 0 := by
    have h := congrFun (congrFun k3 i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> simp [h]
  exact (GlobalTheory.T.ainf_dvd_of_closed_disc_dvd_eisenstein_pow l K bk _).2 (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 k5))
