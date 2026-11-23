import Formalism.LocalToGlobal.Columns.ChainTopLaw
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def CtlPhiLaw : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS t j n' n : ℕ),
    ((q : ℕ) : 𝓞 E) ∈ P.asIdeal → ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → 1 ≤ j → 0 < t →
    n' = k₀ + 2 * rS + 1 + (j - 1) * t → n = k₀ + 2 * rS + 1 + j * t →
    ∀ (γ : Sp E n ≃ₗ[E] Sp E n) (κ : Sp E n' ≃ₗ[E] Sp E n'),
      γ ∈ LocE.JGsym P q k₀ rS (k₀ + 2 * rS + 1) t n 0 → κ ∈ LocE.JGsym P q k₀ rS (k₀ + 2 * rS + 1) t n' 0 →
      ∀ x : HomE E (n' + 0) (n + 0),
        LocE.PhiGS (P := P) q ψ₀ χ k₀ rS (k₀ + 2 * rS + 1) t j 0 n' 0 n (γ.symm.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
          LocE.lamGBS q ψ₀ χ k₀ (k₀ + 2 * rS + 1) t (j - 1) n' 0 κ.toLinearMap *
            (LocE.unitV (χ (j - 1)) (LinearEquiv.det κ : E))⁻¹ *
            (LocE.lamGBS q ψ₀ χ k₀ (k₀ + 2 * rS + 1) t j n 0 γ.toLinearMap)⁻¹ *
            LocE.unitV (χ (j - 1)) (LinearEquiv.det γ : E) *
            LocE.PhiGS (P := P) q ψ₀ χ k₀ rS (k₀ + 2 * rS + 1) t j 0 n' 0 n x

section Top

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ctl_unitV_ne {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hU : IsUnit (redP P a)) : LocE.unitV χ a ≠ 0 := by
  unfold LocE.unitV
  rw [dif_pos hU]
  exact Units.ne_zero _

theorem ctl_unitV_inv_mul {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (hab : redP P a = redP P b)
    (hU : IsUnit (redP P a)) : LocE.unitV χ⁻¹ a * LocE.unitV χ b = 1 := by
  have hU' : IsUnit (redP P b) := hab ▸ hU
  unfold LocE.unitV
  rw [dif_pos hU, dif_pos hU', MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have : hU.unit = hU'.unit := Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, hab])
  rw [this, inv_mul_cancel₀ (Units.ne_zero _)]

theorem ctl_lamJsym_lamJ {K : Type} [Field K] (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {n k₀ rS t j : ℕ} (ht : 0 < t) (hn : k₀ + 2 * rS + 1 + j * t ≤ n) (h : k₀ + 2 * rS + 1 ≤ n)
    (M : ↥(HJsym (𝓞 E ⧸ P.asIdeal) n k₀ (k₀ + 2 * rS + 1) t j rS h)) :
    letI := resField P
    σ₀ ((lamJsym ψ₀ χ n k₀ (k₀ + 2 * rS + 1) t j rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamJ (glmPsi (RingEquiv.refl (𝓞 E ⧸ P.asIdeal)) σ₀ ψ₀) (fun s => glmChi (RingEquiv.refl (𝓞 E ⧸ P.asIdeal)) σ₀ (χ s))
        (k₀ + 2 * rS + 1) t j k₀ ((M.1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)).map (RingEquiv.refl (𝓞 E ⧸ P.asIdeal))) := by
  letI := resField P
  rw [lamJsym_eq_lamSym (RingEquiv.refl (𝓞 E ⧸ P.asIdeal)) σ₀ ψ₀ χ ht hn h M]
  rfl

end Top

section TopMain

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ctl_top (hlaw : CtlPhiLaw) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {K : Type} [Field K]
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t m n' N c' : ℕ}
    (hc' : c' = 0) (hr0 : r = k₀ + 2 * rS + 1) (hm : 2 ≤ m) (ht : 0 < t) (hn' : n' = r + (m - 1) * t) (hN : N = r + m * t + 1)
    (hrn' : r ≤ n') (hrN : r ≤ N)
    {κ : Sp E n' ≃ₗ[E] Sp E n'} (hκ : κ ∈ GLint E n' P) {H : GL (Fin n') (𝓞 E ⧸ P.asIdeal)}
    (hH : H ∈ HJsym (𝓞 E ⧸ P.asIdeal) n' k₀ r t (m - 1) rS hrn')
    (hred : ∀ x ∈ stdAt E n' P, redV P (κ x) = (H⁻¹).1.mulVec (redV P x))
    {κ' : Sp E N ≃ₗ[E] Sp E N} (hκ' : κ' ∈ GLint E N P) {H' : GL (Fin N) (𝓞 E ⧸ P.asIdeal)}
    (hH' : H' ∈ HXmsym (𝓞 E ⧸ P.asIdeal) N k₀ r t m rS hrN)
    (hred' : ∀ x ∈ stdAt E N P, redV P (κ' x) = (H'⁻¹).1.mulVec (redV P x))
    (y : HomE E n' N) (hy : ∀ j l, IntAt P (y (Pi.single j 1) l)) :
    LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E) * LocE.unitV (χ (m - 1))⁻¹ (LinearEquiv.det κ' : E) *
        LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t m c' n' 0 (N - 1)
          (prXpG E N ∘ₗ (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) =
      ((lamXmsym ψ₀ χ N k₀ r t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) * ((lamJsym ψ₀ χ n' k₀ r t (m - 1) rS hrn' ⟨H, hH⟩ : Kˣ) : K)⁻¹ *
        LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t m c' n' 0 (N - 1) (prXpG E N ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  subst hc' hr0
  have hq0 := ciQ_ne_zero hu
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hN' : N' = k₀ + 2 * rS + 1 + m * t := by omega
  have hinv' : H'⁻¹ ∈ HXmsym (𝓞 E ⧸ P.asIdeal) (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN := Subgroup.inv_mem _ hH'
  have hA : ∀ p : Fin N', (H' : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) (Fin.castSucc p) (Fin.last N') = 0 :=
    ctl_fixCol_zero hH'.2 hN'
  have hA' : ∀ p : Fin N', ((H'⁻¹ : GL (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal))
      (Fin.castSucc p) (Fin.last N') = 0 := ctl_fixCol_zero hinv'.2 hN'
  have hll' : ((H'⁻¹ : GL (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal))
      (Fin.last N') (Fin.last N') = 1 := by
    rw [hinv'.2 (Fin.last N') (Fin.last N') (by rw [Fin.val_last]; exact hN'), Matrix.one_apply_eq]
  obtain ⟨γ, hγ, hγJ, hγr, hgA, hgl⟩ := ctl_tgt (q := q) hq hu hN' hrN (by omega) (by omega) (by omega) ht hκ' hH'.1 hA hA' hred'
  let γ' : Sp E (N' + 1 - 1) ≃ₗ[E] Sp E (N' + 1 - 1) := γ
  have hκJ : κ ∈ LocE.JGsym P q k₀ rS (k₀ + 2 * rS + 1) t n' 0 :=
    ctl_mem_JGsym hq hu (by omega) (by omega) hrn' ht (by omega) hκ (Subgroup.inv_mem _ hH) hred
  have hY : ∀ l s, l < N' + 1 → s < n' → IntAt P (Loc.atN (y (κ (Loc.eN E n' s))) l) := by
    intro l s hl hs
    have hv : κ (Loc.eN E n' s) ∈ stdAt E n' P := (hκ _).2 (by rw [ocbS_eN_single hs]; exact ciSingle_mem _)
    have h1 := xt_map_std y hy hv
    rw [ocbS_atN_of_lt _ hl]
    exact (ciMem_stdAt P _).1 h1 _
  have hcongr := ctl_congr hq hu ψ₀ χ (k₀ := k₀) (rS := rS) (r := k₀ + 2 * rS + 1) (t := t) (j := m) (n' := n') (N := N' + 1)
    (by omega) (by omega) (by omega) (by have : (m - 1) * t ≤ m * t := Nat.mul_le_mul_right t (Nat.sub_le m 1); omega)
    κ'.symm.toLinearMap γ'.symm.toLinearMap y κ.toLinearMap hgA hgl hY
  have hL := hlaw E K P q ψ₀ χ k₀ rS t m n' (N' + 1 - 1) hq hu (by omega) ht (by omega) (by omega) γ' κ hγJ hκJ
    (prXpG E (N' + 1) ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0))
  rw [hcongr, hL]

  letI := resField P
  have hinvJ : ((lamJsym ψ₀ χ n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn' ⟨H⁻¹, Subgroup.inv_mem _ hH⟩ : Kˣ) : K) =
      ((lamJsym ψ₀ χ n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn' ⟨H, hH⟩ : Kˣ) : K)⁻¹ := by
    rw [show (⟨H⁻¹, Subgroup.inv_mem _ hH⟩ : ↥(HJsym (𝓞 E ⧸ P.asIdeal) n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn')) = ⟨H, hH⟩⁻¹ from rfl,
      map_inv, Units.val_inv_eq_inv_val]
  have hκL : LocE.lamGBS q ψ₀ χ k₀ (k₀ + 2 * rS + 1) t (m - 1) n' 0 κ.toLinearMap =
      ((lamJsym ψ₀ χ n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn' ⟨H, hH⟩ : Kˣ) : K)⁻¹ := by
    rw [← hinvJ]
    apply σ₀.injective
    rw [ctl_lamGBS_lamJ (RingEquiv.refl (𝓞 E ⧸ P.asIdeal)) σ₀ ψ₀ χ (by omega) (by omega) hκ hred,
      ctl_lamJsym_lamJ σ₀ ψ₀ χ ht (by omega) hrn']
  set A := ctlTLGL H' hA hA' with hAdef
  have hAmem : A ∈ HJsym (𝓞 E ⧸ P.asIdeal) N' k₀ (k₀ + 2 * rS + 1) t m rS (by omega) := ctl_TL_mem hrN (by omega) hH'.1 hA hA'
  have hXm : ((lamXmsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) =
      ((lamJsym ψ₀ χ N' k₀ (k₀ + 2 * rS + 1) t m rS (by omega) ⟨A, hAmem⟩ : Kˣ) : K) := by
    apply σ₀.injective
    have e1 : ((lamXmsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) =
        ((lamJsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'.1⟩ : Kˣ) : K) := rfl
    rw [e1, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht (by omega) hrN, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht (by omega) (by omega),
      ctl_lamJ_TL _ _ (by omega) (by omega)]
    rfl
  have hγL : (LocE.lamGBS q ψ₀ χ k₀ (k₀ + 2 * rS + 1) t m (N' + 1 - 1) 0 γ'.toLinearMap)⁻¹ =
      ((lamXmsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) := by
    have h1 : LocE.lamGBS q ψ₀ χ k₀ (k₀ + 2 * rS + 1) t m (N' + 1 - 1) 0 γ'.toLinearMap =
        ((lamJsym ψ₀ χ N' k₀ (k₀ + 2 * rS + 1) t m rS (by omega) ⟨A⁻¹, Subgroup.inv_mem _ hAmem⟩ : Kˣ) : K) := by
      apply σ₀.injective
      rw [ctl_lamJsym_lamJ σ₀ ψ₀ χ ht (by omega) (by omega)]
      exact ctl_lamGBS_lamJ (RingEquiv.refl (𝓞 E ⧸ P.asIdeal)) σ₀ ψ₀ χ (k₀ := k₀) (r := k₀ + 2 * rS + 1) (t := t) (j := m)
        (n := N') (by omega) (by omega) hγ hγr
    rw [h1, hXm, show (⟨A⁻¹, Subgroup.inv_mem _ hAmem⟩ : ↥(HJsym (𝓞 E ⧸ P.asIdeal) N' k₀ (k₀ + 2 * rS + 1) t m rS (by omega))) =
      ⟨A, hAmem⟩⁻¹ from rfl, map_inv, Units.val_inv_eq_inv_val, inv_inv]

  have hHu : IsUnit ((H⁻¹ : GL (Fin n') (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n') (Fin n') (𝓞 E ⧸ P.asIdeal)).det :=
    isUnit_iff_exists_inv.2 ⟨(H : Matrix (Fin n') (Fin n') (𝓞 E ⧸ P.asIdeal)).det, by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]⟩
  have hdκ := ctl_det_red hκ hred
  have huS : LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E) ≠ 0 := ctl_unitV_ne _ (by rw [hdκ.2]; exact hHu)
  have hdκ' := ctl_det_red hκ' hred'
  have hdγ := ctl_det_red hγ hγr
  have hH'u : IsUnit ((H'⁻¹ : GL (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)).det :=
    isUnit_iff_exists_inv.2 ⟨(H' : Matrix (Fin (N' + 1)) (Fin (N' + 1)) (𝓞 E ⧸ P.asIdeal)).det, by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]⟩
  have hab : redP P (LinearEquiv.det κ' : E) = redP P (LinearEquiv.det γ' : E) := by
    rw [hdκ'.2]
    show _ = redP P (LinearEquiv.det γ : E)
    rw [hdγ.2, ctl_det_TL _ hA' hll']
    rfl
  have hTγ : LocE.unitV (χ (m - 1))⁻¹ (LinearEquiv.det κ' : E) * LocE.unitV (χ (m - 1)) (LinearEquiv.det γ' : E) = 1 :=
    ctl_unitV_inv_mul (χ (m - 1)) hab (by rw [hdκ'.2]; exact hH'u)
  rw [hκL, hγL]
  calc LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E) * LocE.unitV (χ (m - 1))⁻¹ (LinearEquiv.det κ' : E) *
        (((lamJsym ψ₀ χ n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn' ⟨H, hH⟩ : Kˣ) : K)⁻¹ *
          (LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E))⁻¹ *
          ((lamXmsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) *
          LocE.unitV (χ (m - 1)) (LinearEquiv.det γ' : E) *
          LocE.PhiGS (P := P) q ψ₀ χ k₀ rS (k₀ + 2 * rS + 1) t m 0 n' 0 (N' + 1 - 1)
            (prXpG E (N' + 1) ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)))
      = (LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E) * (LocE.unitV (χ (m - 1)) (LinearEquiv.det κ : E))⁻¹) *
          (LocE.unitV (χ (m - 1))⁻¹ (LinearEquiv.det κ' : E) * LocE.unitV (χ (m - 1)) (LinearEquiv.det γ' : E)) *
          (((lamXmsym ψ₀ χ (N' + 1) k₀ (k₀ + 2 * rS + 1) t m rS hrN ⟨H', hH'⟩ : Kˣ) : K) *
            ((lamJsym ψ₀ χ n' k₀ (k₀ + 2 * rS + 1) t (m - 1) rS hrn' ⟨H, hH⟩ : Kˣ) : K)⁻¹ *
            LocE.PhiGS (P := P) q ψ₀ χ k₀ rS (k₀ + 2 * rS + 1) t m 0 n' 0 (N' + 1 - 1)
              (prXpG E (N' + 1) ∘ₗ y ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ huS, hTγ, one_mul, one_mul]

end TopMain

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ctl_lamXmsym_congr {κ K : Type} [CommRing κ] [Field K] (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k r t m m' rS : ℕ} (h : r ≤ n)
    (e : m = m') {M : GL (Fin n) κ} (h1 : M ∈ HXmsym κ n k r t m rS h) (h2 : M ∈ HXmsym κ n k r t m' rS h) :
    lamXmsym ψ χ n k r t m rS h ⟨M, h1⟩ = lamXmsym ψ χ n k r t m' rS h ⟨M, h2⟩ := by
  subst e
  rfl

theorem topLawG_sym (hlaw : CtlPhiLaw) (hX : X.Ok) (hPr : Pr.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (hsharp : cst.sharp = true) :
    TopLawG Ch sel mu cst (oneIdx (colLevSym Ch) (QE sel (mu : Chr X.F X.E X.K)) m2) m2 (colLevSym Ch (m2 + 1 + 1))
      (oneAl (colLevSym Ch) sel mu m2 (m2 + 1) le_rfl) := by
  intro w hw h h' κ κ' hκ hκ' y hy
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hX hPr hw
  have hj : m2 + 1 + 1 = R.m := by omega
  have hrn' : R.r ≤ R.N (m2 + 1) := r_le_N_of_le (by omega)
  have hrN : R.r ≤ R.N (m2 + 1 + 1) := r_le_N_of_le (by omega)
  have ht : 0 < R.t := by have := R.three_m_lt_t; omega
  have hH : h.1 ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k R.r R.t (m2 + 1 + 1 - 1) R.rS hrn' := by
    have h2 := h.2
    change h.1 ∈ (colLevSym Ch (m2 + 1) ⟨w.1, hw⟩).H at h2
    rw [colLevSym_pred Ch hj] at h2
    exact h2
  have hlamS : ((((oneIdx (colLevSym Ch) (QE sel (mu : Chr X.F X.E X.K)) m2).levG (m2 + 1)
      (oneAl (colLevSym Ch) sel mu m2 (m2 + 1) le_rfl) ⟨w.1, hw⟩).lam h : X.Kˣ) : X.K) =
      ((lamJsym (Ch.psi0 ⟨w.1, hw⟩) (extChi fun s => Ch.chi s ⟨w.1, hw⟩) (R.N (m2 + 1)) R.k R.r R.t (m2 + 1 + 1 - 1) R.rS hrn'
        ⟨h.1, hH⟩ : X.Kˣ) : X.K) := by
    have key : ∀ (l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N (m2 + 1))), l = colLevSym Ch (m2 + 1) ⟨w.1, hw⟩ →
        ∀ (M : ↥l.H) (hM : M.1 ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k R.r R.t (m2 + 1 + 1 - 1) R.rS hrn'),
        ((l.lam M : X.Kˣ) : X.K) = ((lamJsym (Ch.psi0 ⟨w.1, hw⟩) (extChi fun s => Ch.chi s ⟨w.1, hw⟩) (R.N (m2 + 1)) R.k R.r R.t
          (m2 + 1 + 1 - 1) R.rS hrn' ⟨M.1, hM⟩ : X.Kˣ) : X.K) := by
      intro l hl M hM
      rw [colLevSym_pred Ch hj] at hl
      subst hl
      rfl
    exact key _ rfl h hH
  have hH'm : h'.1 ∈ HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1 + 1)) R.k R.r R.t R.m R.rS hrN := by
    have h2 : ∀ M, M ∈ (colLevSym Ch (m2 + 1 + 1) ⟨w.1, hw⟩).H →
        M ∈ HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1 + 1)) R.k R.r R.t R.m R.rS hrN := fun M hM => by
      rw [colLevSym_top_H Ch (by omega) ⟨w.1, hw⟩] at hM
      exact hM
    exact h2 h'.1 h'.2
  have hH' : h'.1 ∈ HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1 + 1)) R.k R.r R.t (m2 + 1 + 1) R.rS hrN := by
    have h3 := hH'm
    rw [show R.m = m2 + 1 + 1 by omega] at h3
    exact h3
  have hlamT : ((((colLevSym Ch (m2 + 1 + 1)) ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) =
      ((lamXmsym (Ch.psi0 ⟨w.1, hw⟩) (extChi fun s => Ch.chi s ⟨w.1, hw⟩) (R.N (m2 + 1 + 1)) R.k R.r R.t (m2 + 1 + 1) R.rS hrN
        ⟨h'.1, hH'⟩ : X.Kˣ) : X.K) := by
    rw [colLevSym_top_lam Ch (by omega) ⟨w.1, hw⟩ h' hH'm]
    exact congrArg (fun z : X.Kˣ => (z : X.K))
      (ctl_lamXmsym_congr (Ch.psi0 ⟨w.1, hw⟩) (extChi fun s => Ch.chi s ⟨w.1, hw⟩) hrN (by omega) hH'm hH')
  unfold rhoS rhoT PhiTopG
  simp only [if_pos hw, hsharp, if_true]
  have e1 : psi0P Ch w.1 = Ch.psi0 ⟨w.1, hw⟩ := by
    unfold psi0P
    rw [dif_pos hw]
  have e2 : chiP Ch w.1 = extChi fun s => Ch.chi s ⟨w.1, hw⟩ := by
    unfold chiP
    rw [dif_pos hw]
    rfl
  rw [Units.val_inv_eq_inv_val, hlamS, hlamT, e1, e2]
  have hn' : R.N (m2 + 1) = R.r + (m2 + 1 + 1 - 1) * R.t := by
    show R.N (m2 + 1) = R.r + (m2 + 1) * R.t
    rw [N_eq_blocks]
    unfold Ranks.r
    omega
  have hN : R.N (m2 + 1 + 1) = R.r + (m2 + 1 + 1) * R.t + 1 := by
    rw [N_eq_blocks]
    unfold Ranks.r
    omega
  exact ctl_top hlaw hq hu σ₀ (Ch.psi0 ⟨w.1, hw⟩) (extChi fun s => Ch.chi s ⟨w.1, hw⟩) (xt_cOf hm) (r_eq_sym R) (by omega) ht hn' hN
    hrn' hrN κ.2 hH hκ κ'.2 hH' hκ' y hy

end Inst

end Formalism.L2.Col
