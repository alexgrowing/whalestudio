import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LiePowRPerp

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.Level

namespace Formalism.L2.SG.NonRelPf

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem fvec_succ (F : FlagG S r T) (a : Fin r) : F.fvec a.succ = nxt F.e F.z a := by
  rfl

theorem nxt_map {V W : Type} (g : V → W) (e : Fin r → V) (z : V) (a : Fin r) :
    g (nxt e z a) = nxt (fun b => g (e b)) (g z) a := by
  simp only [nxt]
  split_ifs <;> rfl

theorem mapFlag_Xa (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : ℕ) :
    (mapFlag γ hγ F).Xa b = (F.Xa b).map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.Xa, FlagG.Xa, Submodule.map_span, Set.image_image]
  rfl

theorem mapFlag_X (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapFlag γ hγ F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.X, FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem mem_map_iff (γ : S.V ≃ₗ[E] S.V) (p : Submodule E S.V) (y : S.V) :
    y ∈ p.map (γ : S.V →ₗ[E] S.V) ↔ γ.symm y ∈ p := by
  exact Submodule.mem_map_equiv p

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Φ (v : InfinitePlace X.B.I.F) (y : D.host.E) : ℂ := X.B.I.φ v (X.ιE.symm y)

theorem Φ_add (v) (a b : D.host.E) : Φ X v (a + b) = Φ X v a + Φ X v b := by
  simp [Φ]
theorem Φ_sum (v) {ι : Type} (s : Finset ι) (f : ι → D.host.E) : Φ X v (∑ i ∈ s, f i) = ∑ i ∈ s, Φ X v (f i) := by
  simp [Φ, map_sum]
theorem Φ_star (v) (a : D.host.E) : Φ X v (star a) = star (Φ X v a) := by
  have hb : star a = D.host.conj a := Formalism.BasicNotions.bridge_star_holds _ _ a
  have h1 : X.ιE.symm (star a) = star (X.ιE.symm a) := by
    apply X.ιE.injective
    rw [RingEquiv.apply_symm_apply, X.ιE_conj, RingEquiv.apply_symm_apply, hb]
  simp only [Φ]
  rw [h1, Formalism.L2.SG.Pf.Level.phi_star]
theorem Φ_rat (v) (q : ℚ) : Φ X v (q : D.host.E) = (q : ℂ) := by
  simp [Φ]

theorem hE_crd (p q : (VS D).V) : hE X (X.crd p) (X.crd q) = X.ιE.symm ((VS D).hT p q) := by
  apply X.ιE.injective
  rw [Formalism.L2.SG.Pf.Level.iota_hE, Formalism.L2.SG.Pf.Level.toV_crd, Formalism.L2.SG.Pf.Level.toV_crd,
    RingEquiv.apply_symm_apply]

theorem hTfe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h : starRingEnd D.host.E ((VS D).hT (X.eX b) (X.fY a)) = (VS D).hT (X.fY a) (X.eX b) := by
    first
      | exact (VS D).herm.eq _ _
      | exact (VS D).herm _ _
  rw [← h, X.ef b a]
  split_ifs <;> simp

theorem psi_rat (w : D.what₂.Word) {x : X.B.I.GA} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m) :
    X.psiInfU w x.1 = ∏ v, Complex.exp (2 * Real.pi * Complex.I *
      ((∑ a : Fin D.R.rS, (Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a))) +
        star (Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a)))))) / (X.B.g : ℂ))) := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  have hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (uMat (x.1 v)) a = Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a))) := by
    intro v a
    unfold rootCoord
    have e1 : nxt (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd (nxt X.eX (X.zu w) a)) := by
      rw [nxt_map (fun y => rv X.B.I v (X.crd y))]; rfl
    rw [e1, h1 v, rv_mulVec X v, ← h3, hJ_rv, HidaSetting.fR, hE_crd]
    rfl
  unfold HidaSetting.psiInfU psiInf psiR
  simp only [hrc]

theorem Φ_sub (X : HidaSetting D) (v) (a b : D.host.E) : Φ X v (a - b) = Φ X v a - Φ X v b := by
  simp [Φ]

theorem star_F (X : HidaSetting D) (y : D.host.E) (hy : y ∈ D.host.F) : star y = y := by
  rw [Formalism.BasicNotions.bridge_star_holds _ _ y]
  exact (D.host.der.mem_F y).mp hy

def sigF (X : HidaSetting D) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun c => by
    show star (c : D.host.E) = c
    exact star_F X c c.2

theorem trace_zero (X : HidaSetting D) {y : D.host.E} (hy : y + star y = 0) : Algebra.trace D.host.F D.host.E y = 0 := by
  have h1 : Algebra.trace D.host.F D.host.E (sigF X y) = Algebra.trace D.host.F D.host.E y :=
    Algebra.trace_eq_of_algEquiv (sigF X) y
  have h2 : sigF X y = star y := rfl
  have h3 : star y = -y := eq_neg_of_add_eq_zero_right hy
  rw [h2, h3, map_neg] at h1
  have h4 : (2 : D.host.F) * Algebra.trace D.host.F D.host.E y = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 two_ne_zero
  · exact h5

open Formalism.L2.SG.TermOp.Vanish in

theorem nonRelCharC_holds : NonRelCharC := by
  intro D X Yf u u' t ht
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hisoF : ∀ a b, (VS D).hT (t.lin a) (t.lin b) = (VS D).hT a b := hiso
  set F' := mapFlag t.lin hiso (X.Fu u') with hF'
  have hfr : t.frame = ⟨F', t.lin (X.Fu u').z⟩ := by
    unfold GTerm.frame mapLF; rw [dif_pos hiso]; rfl
  have hnr : ¬ Relevant D.host.F (X.Fu u) F' := by
    intro h; apply ht
    unfold GTerm.relevant TermDef.Term.relevant TermDef.IsRel
    refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
    rw [hfr]; exact h
  unfold Relevant at hnr
  push Not at hnr
  obtain ⟨Y, ⟨hY1, hY2⟩, hne⟩ := hnr
  set ℓ := (X.Fu u).ell Y with hℓ
  set ℓ' := F'.ell Y with hℓ'
  set δ : D.host.E := (ℓ - ℓ') + star (ℓ - ℓ') with hδ
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hne
    have := trace_zero X h0
    unfold FlagG.dpsi
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hδs : star δ = δ := by rw [hδ, star_add, star_star, add_comm]
  set N := Fintype.card (InfinitePlace X.B.I.F) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hg0 : (X.B.g : ℚ) ≠ 0 := by
    rw [X.g_eq]; push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  set c : ℚ := (X.B.g : ℚ) / (2 * N) with hc
  set s : D.host.E := (c : D.host.E) * δ⁻¹ with hsdef
  have hs : star s = s := by rw [hsdef, star_mul', star_inv₀, hδs, star_ratCast]
  have hsδ : s * δ = c := by rw [hsdef, mul_assoc, inv_mul_cancel₀ hδ0, mul_one]

  set n := nexpE hY1 s with hn
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := nexpE_isom hY1 hs
  have hgtop : ∀ m : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      Formalism.HermitianLatticesTheory.gmap m (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
    intro m; unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 m.surjective
  have horth : ∀ (G : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (y : (VS D).V),
      y ∈ orth (VS D) G.X → ∀ w ∈ G.X, (VS D).hT w y = 0 := by
    intro G y hy w hw
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hy w hw
  have hnN : n ∈ NLam ⊤ (lf D (X.Fu u)) := by
    refine ⟨⟨hnI, hgtop n⟩, fun j x hx => nexp_Xa (s := s) hY1 j hx, fun x hx => nexp_perp (s := s) hY1 ?_⟩
    show ∀ w ∈ (X.Fu u).X, (VS D).hT w x = 0
    intro w hw
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx w hw
  obtain ⟨x, hx⟩ := ratPt_holds D X n hnI
  have hr1 : x.1 ∈ X.NinfU u := nLamNinf_holds D X u ⊤ x n hx hnN
  have hx' : RatLink X (t.pt⁻¹ * x * t.pt) (t.lin⁻¹ * n * t.lin) :=
    Vanish.ratLink_mul X (Vanish.ratLink_mul X (Vanish.ratLink_inv X t.rep.2.1) hx) t.rep.2.1
  set n' := t.lin⁻¹ * n * t.lin with hn'
  have hn'app : ∀ y, n' y = t.lin.symm (n (t.lin y)) := fun y => rfl
  have hsub : ∀ y, n' y - y = t.lin.symm (nexp Y s (t.lin y) - t.lin y) := by
    intro y; rw [hn'app, map_sub, LinearEquiv.symm_apply_apply]; rfl
  have hn'N : n' ∈ NLam ⊤ (lf D (X.Fu u')) := by
    refine ⟨⟨?_, hgtop n'⟩, fun j y hy => ?_, fun y hy => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hiso) hnI) hiso
    · have h1 : t.lin y ∈ F'.Xa (j + 1) := by
        rw [hF', mapFlag_Xa]; exact Submodule.mem_map_of_mem hy
      have h2 := nexp_Xa (s := s) hY2 j h1
      rw [hF', mapFlag_Xa, mem_map_iff] at h2
      rw [hsub]; exact h2
    · have h1 : t.lin y ∈ perpS (VS D) F'.X := by
        show ∀ w ∈ F'.X, (VS D).hT w (t.lin y) = 0
        intro w hw
        rw [hF', mapFlag_X, mem_map_iff] at hw
        have := horth (X.Fu u') y hy _ hw
        rw [← hisoF (t.lin.symm w) y, LinearEquiv.apply_symm_apply] at this
        exact this
      have h2 := nexp_perp (s := s) hY2 h1
      rw [hF', mapFlag_X, mem_map_iff] at h2
      rw [hsub]; exact h2
  have hr2 : (t.pt⁻¹ * x * t.pt).1 ∈ X.NinfU u' := nLamNinf_holds D X u' ⊤ _ n' hx' hn'N
  refine ⟨x.1, ⟨hr1, hr2⟩, ?_⟩
  show X.psiInfU u x.1 ≠ X.psiInfU u' (t.pt⁻¹ * x * t.pt).1
  rw [psi_rat X u hx, psi_rat X u' hx']

  have key : ∀ a, (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a := by
    intro a
    have e : nxt X.eX (X.zu u) a = (X.Fu u).fvec a.succ := by rw [fvec_succ, X.Fu_e, X.flagZVector]
    rw [e]
    exact nexp_root hY1 (X.fY a) a (fun b => by rw [X.Fu_e]; exact hTfe X a b)
      (by rw [X.flagZVector]; exact (X.zu_orth u a).2)
  have key' : ∀ a, (VS D).hT (X.fY a) (n' (nxt X.eX (X.zu u') a)) = s * F'.coefX (Y (F'.fvec a.succ)) a := by
    intro a
    have e : t.lin (nxt X.eX (X.zu u') a) = F'.fvec a.succ := by
      rw [fvec_succ, nxt_map t.lin, hF']
      simp only [mapFlag, X.Fu_e, X.flagZVector]
    rw [hn'app, ← hisoF (X.fY a), LinearEquiv.apply_symm_apply, e]
    exact nexp_root hY2 (t.lin (X.fY a)) a
      (fun b => by
        show (VS D).hT (t.lin (X.fY a)) (t.lin ((X.Fu u').e b)) = _
        rw [hisoF, X.Fu_e]; exact hTfe X a b)
      (by
        show (VS D).hT (t.lin (X.fY a)) (t.lin (X.Fu u').z) = 0
        rw [hisoF, X.flagZVector]; exact (X.zu_orth u' a).2)
  have hsum : ∀ (cf : Fin D.R.rS → D.host.E) (v : InfinitePlace X.B.I.F),
      (∑ a, (Φ X v (s * cf a) + star (Φ X v (s * cf a)))) = Φ X v (s * ((∑ a, cf a) + star (∑ a, cf a))) := by
    intro cf v
    simp_rw [← Φ_star, ← Φ_add]
    rw [← Φ_sum]
    congr 1
    rw [star_sum, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_mul', hs]
  have hA : ∀ v, (∑ a, (Φ X v (s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a) +
      star (Φ X v (s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a)))) = Φ X v (s * (ℓ + star ℓ)) :=
    fun v => hsum (fun a => (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a) v
  have hA' : ∀ v, (∑ a, (Φ X v (s * F'.coefX (Y (F'.fvec a.succ)) a) +
      star (Φ X v (s * F'.coefX (Y (F'.fvec a.succ)) a)))) = Φ X v (s * (ℓ' + star ℓ')) :=
    fun v => hsum (fun a => F'.coefX (Y (F'.fvec a.succ)) a) v
  simp_rw [key, key']
  simp only [hA, hA']
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  intro heq
  have hd : (∑ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ + star ℓ)) / (X.B.g : ℂ))) -
      (∑ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ' + star ℓ')) / (X.B.g : ℂ))) =
      (Real.pi : ℂ) * Complex.I := by
    rw [← Finset.sum_sub_distrib]
    have hv : ∀ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ + star ℓ)) / (X.B.g : ℂ)) -
        2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ' + star ℓ')) / (X.B.g : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * ((c : ℂ) / (X.B.g : ℂ)) := by
      intro v
      have hΦ : Φ X v (s * (ℓ + star ℓ)) - Φ X v (s * (ℓ' + star ℓ')) = (c : ℂ) := by
        rw [← Φ_sub X, ← mul_sub]
        have : (ℓ + star ℓ) - (ℓ' + star ℓ') = δ := by rw [hδ, star_sub]; ring
        rw [this, hsδ, Φ_rat]
      rw [← mul_sub, ← sub_div, hΦ]
    rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, hc]
    have hg0' : (X.B.g : ℂ) ≠ 0 := by exact_mod_cast hg0
    have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  have h1 : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    rw [← hd, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_pi_mul_I] at h1
  norm_num at h1

end Formalism.L2.SG.NonRelPf
