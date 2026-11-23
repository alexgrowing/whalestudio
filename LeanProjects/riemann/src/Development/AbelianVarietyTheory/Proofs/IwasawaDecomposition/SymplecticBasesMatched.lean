import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g g' : ℕ} {X' X : Data E r}

theorem perFr_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (castFr h.psi x) v τ i = perFr X' x v τ i := by
  cases X; cases X'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3
  rfl

noncomputable def renum (q : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃L[ℂ] (Fin g' → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ q).toContinuousLinearEquiv

theorem renum_apply (q : Fin g' ≃ Fin g) (z : Fin g → ℂ) (j : Fin g') : renum q z j = z (q j) := rfl

theorem hx_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas') (hs : IsSympl X bas)
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) (z w : Fin g → ℂ) :
    hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
  have hx1 := h.castFr_mem_dom hxd
  have him' := (hx_laws E r X' g' bas' idx' 0 hs' Even.zero x hxd).2.2.1
  have him := (hx_laws E r X g bas idx 0 hs Even.zero _ hx1).2.2.1
  refine sub_eq_zero.1 (form_eq_zero_of_im
    (fun z w => hx X bas idx (castFr h.psi x) z w - hx X' bas' idx' x (renum q z) (renum q w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) _
    (span_range_pv idx hs hx1) ?_ z w)
  · simp only [hx, map_add, mulVec_add, add_dotProduct]; ring
  · simp only [hx, map_smul, mulVec_smul, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hx, map_add, star_add, mulVec_add, dotProduct_add]; ring
  · have : renum q (c • u) = c • renum q u := rfl
    simp only [hx, this, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [Complex.sub_im, hpv, hpv, him, him', h.EF_eq, sub_self]

theorem denseRange_embR {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (n : ℕ) : DenseRange (Ker.embR X (n := n)) := by
  obtain ⟨L, hL⟩ := Ker.exists_equiv_zR X idx (n := n) hs hx
  have h := L.symm.surjective.denseRange.comp (Ker.denseRange_zR_embR X idx hs hx) L.symm.continuous
  convert h using 1
  funext y
  simp [← hL]

theorem zR_lact (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {n : ℕ} (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (v : Ker.WR X n) :
    Ker.zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = Ker.zR X idx x v := by
  funext k i
  have hm : mat (lact γ x) (idx i).1 =
      (γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1 * mat x (idx i).1 := rfl
  rw [Ker.zR, Ker.zR, hm]
  split_ifs
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map (idx i).1.1.mapMatrix)
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

theorem zR_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas')
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) {n : ℕ} (v : Ker.WR X' n) (k : Fin n) :
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k := by
  refine (denseRange_embR idx' hs' hxd n).induction_on (p := fun v : Ker.WR X' n =>
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k) v
    (isClosed_eq ?_ ?_) (fun y => hpv (y k))
  · have := (Ker.zRLin X idx (castFr h.psi x) (n := n)).continuous_of_finiteDimensional
    have h2 : Continuous fun (v : Ker.WR X' n) (τ : X.Ψ) => v ⟨τ.1, h.psi.ge τ.2⟩ :=
      continuous_pi fun τ => continuous_apply _
    have h3 := (continuous_apply k).comp (this.comp h2)
    exact (renum q).continuous.comp h3
  · exact (continuous_apply k).comp (Ker.zRLin X' idx' x (n := n)).continuous_of_finiteDimensional

end SlopeTestRemainingChoices

theorem anFib_move_renum : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r g g' : ℕ) (X' X : Data D.host.E r) (hX : SameSp X' X) (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g' ≃ X'.Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl X' bas' → IsSympl X bas → Matched c σ X' idx' e' → Matched c σ X idx e → ∀ x ∈ X'.dom, ∀ L : Lt D.host.E r, SelfD X' L → ∀ ga : GL (Fin r) D.host.E, IsUn X ga → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (y : FrPt Xo c ℂ) (A' : AnFib X' bas' idx' e' x L y) (th' : (Fin g' → ℂ) → ℂ), A'.Reads 1 y.s th' → ∃ (A : AnFib X bas idx e (lact ga (castFr hX.psi x)) (mapL ga L) y) (th : (Fin g → ℂ) → ℂ), A.Reads 1 y.s th ∧ (∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), A'.Marked mk → A.Marked (mvMap ga mk)) ∧ ∀ (n : ℕ) (v' : GlobalTheory.Ker.WR X' n) (v : GlobalTheory.Ker.WR X n), (∀ (τ : X'.Ψ) (k : Fin n), v ⟨τ.1, hX.psi ▸ τ.2⟩ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' τ k) → GlobalTheory.Ker.gaussR X bas idx (lact ga (castFr hX.psi x)) (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v) * ∏ b, th (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v b) = GlobalTheory.Ker.gaussR X' bas' idx' x (GlobalTheory.Ker.zR X' idx' x v') * ∏ b, th' (GlobalTheory.Ker.zR X' idx' x v' b) := by
  intro D H Dw l Xo c σ r g g' X' X h bas' idx' e' bas idx e hs' hs hm' hm x hxd L hL ga hga
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y A th' hth
  let q : Fin g' ≃ Fin g := e'.trans e.symm
  have hq (j) : e (q j) = e' j := e.apply_symm_apply _
  have hpv (v) : renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v := by
    funext j
    rw [renum_apply, hm.1, hm'.1, hq, perFr_castFr h]
  have hty (j) : rowType X (idx (q j)) = rowType X' (idx' j) := by rw [hm.2, hm'.2, hq]
  have hx1 := h.castFr_mem_dom hxd
  obtain ⟨-, -, -, -, -, -, -, hinv⟩ := hx_laws _ r X g bas idx 0 hs Even.zero _ hx1
  obtain ⟨hdom, hpv2, -, hhx2⟩ := hinv ga hga
  have hhx (z w) : hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
    rw [hhx2, hx_renum h hs' hs hxd q hpv]
  have hp (v) : renum q (pv X idx (lact ga (castFr h.psi x)) (Lev.lin ga v)) = pv X' idx' x v :=
    (congrArg (renum q) (hpv2 v)).trans (hpv v)
  have hp' (v) : renum q (pv X idx (lact ga (castFr h.psi x)) v) = pv X' idx' x (Lev.lin ga⁻¹ v) := by
    rw [← hp, Lev.lin_inv']
  have hlat (z) : (∃ v ∈ L, renum q z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v :=
    ⟨fun ⟨v, hv, hz⟩ => ⟨Lev.lin ga v, ⟨v, hv, rfl⟩, (renum q).injective (hz.trans (hp v).symm)⟩,
      fun ⟨v, hv, hz⟩ => ⟨_, Lev.mem_mapL.1 hv, (congrArg (renum q) hz).trans (hp' v)⟩⟩
  refine ⟨
    { ex := fun z => A.ex (renum q z)
      ex_add := fun z w => by rw [map_add, A.ex_add]
      ex_onto := A.ex_onto.comp (renum q).surjective
      ex_ker := fun z => (A.ex_ker _).trans (hlat z)
      ex_lin := fun a z => by
        rw [← A.ex_lin]
        congr 1
        funext j
        simp only [renum_apply, hty]
      hol := fun U f => ?_
      der := fun ℓ => ⟨?_, fun U hU f => ?_⟩
      fr := fun j z => A.fr j (renum q z)
      fr_hol := fun j => (A.fr_hol j).comp (renum q).differentiableOn fun z hz => hz
      fr_ne := fun j z => A.fr_ne j _
      fr_g := fun j j' z => A.fr_g j j' _
      fr_0 := fun j => by rw [map_zero]; exact A.fr_0 j
      χ := fun v => A.χ (Lev.lin ga⁻¹ v)
      χ_norm := fun v hv => A.χ_norm _ (Lev.mem_mapL.1 hv)
      fr_per := fun v hv j z hz => by
        rw [hhx, hhx, map_add, hp']; exact A.fr_per _ (Lev.mem_mapL.1 hv) j _ hz },
    fun z => th' (renum q z), fun j z => hth j (renum q z), fun mk hk a ha => ?_, fun n v' v hv => ?_⟩
  · exact ⟨(A.hol U f).1.preimage (renum q).continuous,
      (A.hol U f).2.comp (renum q).differentiableOn fun z hz => hz⟩
  · simpa only [map_zero] using (A.der ℓ).1
  · rw [(A.der ℓ).2 U hU f]
    have h1 := (renum q).comp_right_fderiv (f := fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (A.ex z).left U f) (x := 0)
    have h2 : renum q (Pi.single (e.symm ℓ) 1) = Pi.single (e'.symm ℓ) 1 := by
      funext j
      rw [renum_apply]
      have h3 : q j = e.symm ℓ ↔ j = e'.symm ℓ := by
        rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, hq]
      simp only [Pi.single_apply, h3]
    rw [← h2]
    rw [map_zero] at h1
    exact (congrArg (fun F => F (Pi.single (e.symm ℓ) 1)) h1).symm
  · rw [hk a ha, ← hp]
    change A.ex _ = A.ex _
    congr 3
    rw [Lev.lin_apply, mulVec_smul]
    rfl
  · have hv2 : v = fun τ k => ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' ⟨τ.1, h.psi.ge τ.2⟩ k := by
      funext τ k
      exact hv ⟨τ.1, h.psi.ge τ.2⟩ k
    have hz (k) : renum q (Ker.zR X idx (lact ga (castFr h.psi x)) v k) = Ker.zR X' idx' x v' k := by
      rw [hv2, zR_lact idx _ ga hga (fun τ => v' ⟨τ.1, h.psi.ge τ.2⟩), zR_renum h hs' hxd q hpv]
    simp only [Ker.gaussR, hhx, hz]

end GlobalTheory.OneMapRef
