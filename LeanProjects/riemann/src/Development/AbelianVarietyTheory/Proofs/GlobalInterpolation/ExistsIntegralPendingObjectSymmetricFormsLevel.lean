import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MulLatMulLat
import Formalism.LocalToGlobal.Columns.TiedValBwG
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FnOfMapInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsLocBasisClsP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoMTSOfGaInv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PtCoMemIntSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPtEmbOfCoordInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0Pend

section LocalBases

open Matrix

theorem isLocBasis_of_split {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : n + 1 = N) {p : ℕ} (hp : p.Prime)
    (L : Set (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E) (hB : IsLocBasis p (L' : Set (Fin n → E)) B)
    (B' : GL (Fin N) E)
    (h : ∀ v : Fin N → E, (B' : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ L ↔
      (B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩) ∈ L' ∧
        v ⟨n, by omega⟩ ∈ (algebraMap (𝓞 E) E).range) : IsLocBasis p L B' := by
  intro x
  obtain ⟨v, rfl⟩ : ∃ v, x = (B' : Matrix (Fin N) (Fin N) E) *ᵥ v :=
    ⟨((B'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x, by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  have e1 : ((B'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ ((B' : Matrix (Fin N) (Fin N) E) *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hB1 := hB ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩))
  have e2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ
      ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩)) = fun i : Fin n => v ⟨i, by omega⟩ := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [e2] at hB1
  rw [e1]
  set R := (algebraMap (𝓞 E) E).range
  have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
  have memL : ∀ s : ℕ, (s : E) • ((B' : Matrix (Fin N) (Fin N) E) *ᵥ v) ∈ L ↔
      (s : E) • ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩)) ∈ L' ∧ (s : E) * v ⟨n, by omega⟩ ∈ R := by
    intro s
    rw [← mulVec_smul, h, ← mulVec_smul]
    rfl
  have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
    (hp.dvd_mul.mp h).elim ha hb
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨h1, h2⟩ := (memL s).mp hx
    obtain ⟨s', hs', h3⟩ := hB1.mp ⟨s, hs, h1⟩
    refine ⟨s * s', hnd _ _ hs hs', fun a => ?_⟩
    by_cases ha : (a : ℕ) < n
    · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 ⟨a, ha⟩)
    · have ea : a = ⟨n, by omega⟩ := Fin.ext (by have := a.2; simp only; omega)
      rw [ea, Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
  · rintro ⟨s, hs, h0⟩
    obtain ⟨s', hs', h3⟩ := hB1.mpr ⟨s, hs, fun a => h0 _⟩
    refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
    · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem h3 s
    · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' (h0 _)

theorem cols_mulVec {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (v : Fin N → E) :
    (Matrix.of fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v =
      A *ᵥ (fun i : Fin n => v ⟨i, by omega⟩) + v ⟨n, by omega⟩ • z := by
  subst hN
  funext a
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  rw [mul_comm (z a)]
  rfl

theorem hform_add_left' {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right' {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end LocalBases

section Dual

open Matrix Formalism.L2.GlobalTheoryTheory.Br Formalism.UG

set_option maxHeartbeats 1000000 in

theorem mem_dual_tilde_iff {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (a : Fin (D.R.N D.R.m - 1) → D.host.E) (t : D.host.E) :
    iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0 ∈
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
        ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tf.til.z0}) ↔
      a ∈ Tf.clsP.lat c ∧ t ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  obtain ⟨b, hb⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have o1 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) Tf.til.z0 = 0 := fun x => by
    rw [hb, hform_smul_rightB, hform_iXc_zc, mul_zero]
  have o2 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tf.til.z0 (iXc D x) = 0 := fun x => by
    rw [hb, hform_smul_leftB, hform_zc_iXc, mul_zero]
  have p1 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x)
      (iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0) = hform (sigD D : D.host.E →+* D.host.E) (gramP D) x a := fun x => by
    rw [hform_add_right', hform_smul_rightB, o1, mul_zero, add_zero, hform_iXc]
  have p2 : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tf.til.z0
      (iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0) = t := by
    rw [hform_add_right', hform_smul_rightB, o2, zero_add, hzz, div_mul_cancel₀ _ hT]
  have hSD := (GlobalTheory.ClassLatticeSelfDual.classLattice_selfDual D u Tf.clsP c).2 a
  constructor
  · intro h
    refine ⟨hSD.2 fun x hx => ?_, ?_⟩
    · rw [← p1]
      exact h _ (Submodule.mem_sup_left ⟨x, hx, rfl⟩)
    · rw [← p2]
      exact h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · rintro ⟨ha, ht⟩ y hy
    obtain ⟨_, ⟨x, hx, rfl⟩, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy2
    have er : r • Tf.til.z0 = (r : D.host.E) • Tf.til.z0 := (algebraMap_smul D.host.E r _).symm
    have ex : ((iXc D).restrictScalars (𝓞 D.host.E)) x = iXc D x := rfl
    rw [hform_add_left', er, ex, hform_smul_leftB, p1, p2]
    refine add_mem (hSD.1 ha x hx) (mul_mem ?_ ht)
    exact ⟨⟨_, r.2.map (sigD D : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_isLocBasis_dual (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B) :
    ∃ B' : GL (Fin (D.R.N D.R.m)) D.host.E, (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
      ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        bZg u Tf.til.z0 (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) ∧
      IsLocBasis (D.what₂.places.resChar w)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) B' := by
  have hU := bZg_isUnitS Tf (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (Matrix.isUnits_det_units B)
  obtain ⟨Z, hZ⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hU
  refine ⟨((Tf.til.ga c).1)⁻¹ * Z, by rw [Units.val_mul, hZ], ?_⟩
  refine isLocBasis_of_split (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (D.what₂.places.resChar_prime w) _ (Tf.clsP.lat c) B hB _ fun v => ?_
  have hv : (Z : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ v =
      iXc D ((B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) *ᵥ
        (fun i : Fin (D.R.N D.R.m - 1) => v ⟨i, by have := Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R; omega⟩)) +
      (v ⟨D.R.N D.R.m - 1, by have := Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R; omega⟩ / ((D.mem u).A.T : D.host.E)) • Tf.til.z0 := by
    rw [hZ]
    refine (cols_mulVec (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D * (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E))
      (fun a => Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) v).trans ?_
    rw [← mulVec_mulVec, iXm, LinearMap.toMatrix'_mulVec]
    congr 1
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [← mem_dual_tilde_iff Tf c, ← hv, ← Tf.til.til_lat c, Units.val_mul, ← mulVec_mulVec]
  set y := (Z : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ v
  have hy : (Tf.til.ga c).1.1 *ᵥ (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ y) = y := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  constructor
  · rintro h _ ⟨l, hl, rfl⟩
    have := h l hl
    rw [← ga_herm Tf c, hy] at this
    exact this
  · intro h l hl
    rw [← ga_herm Tf c, hy]
    exact h _ ⟨l, hl, rfl⟩

end Dual

section Localisation

open Formalism.L2.DIV Formalism.L2.Col

theorem mem_localization_delAtr_of_basis {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
    (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
    {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ) (eT : ι → E →+* ℂ)
    (he : embAt s emb = eT) (J : Matrix (Fin n) (Fin n) E)
    (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) (F : VV K lam) (w : Pl.Pl) (B : GL (Fin n) E)
    (hB : IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B)
    (h : Formalism.L2.Forms.fnInv (gramC J eT) (shiftOf lam) (atInf eT (B : Matrix (Fin n) (Fin n) E)⁻¹)
      (fnOf (gramC J eT) (shiftOf lam) 1 (MvPolynomial.map s F.1)) ∈ vlIntSpan s Pl w lam') :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) := by
  subst he
  have e := vl_coord emb s J lam B F
  have e' : fnOf (gramC J (embAt s emb)) (shiftOf lam) 1 (MvPolynomial.map s F.1) = evV emb J lam s F := rfl
  rw [e', e, ← Matrix.coe_units_inv, Formalism.L2.Forms.fnInv_fnOf _ _ (atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) B⁻¹))] at h
  exact (mem_localization_iff_forall_localBasis_of_valuation Pl pw hval emb s w J lam lam' hn (fun _ => M) (fun _ => hM) F (fun _ => B) (fun _ => hB)).2
    ⟨_, h, e⟩

theorem local_of_mem_delAtr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
    (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
    {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ) (eT : ι → E →+* ℂ)
    (he : embAt s emb = eT) (hpw : Function.Surjective pw) (J : Matrix (Fin n) (Fin n) E)
    (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) (F : VV K lam) (hF : F ∈ delAtr emb lam M)
    (w : Pl.Pl) (B : GL (Fin n) E) (hB : IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B) :
    ∃ P ∈ vlIntSpan s Pl w lam',
      fnOf (gramC J eT) (shiftOf lam) 1 (MvPolynomial.map s F.1) =
        fnOf (gramC J eT) (shiftOf lam) (atInf eT (B⁻¹ : GL (Fin n) E).1) P := by
  subst he
  exact (vl_mem_delAtr_iff Pl pw hval emb s hpw J lam lam' hn M hM F).1 hF w B hB

set_option maxHeartbeats 1000000 in

theorem mem_SP_of_coord_integral (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V)
    (h : ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) : y ∈ (D.fm u).SP w := by
  classical
  obtain ⟨val, hval⟩ := GlobalTheory.Core.exists_ptVal D u Tf.clsP Tf.valP
  have hK := fun c => (GlobalTheory.ClassLatticeSelfDual.classLattice_selfDual D u Tf.clsP c).1
  have he : embAt D.what₂.embLL (fun τ : D.what₂.Tau =>
      D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) = embT D := by
    funext τ
    ext y
    exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) y)
  have hc : ∀ c, val y c ∈ Formalism.HermitianLatticesTheory.localization₂ (D.plEq w).asIdeal (delAtr (fun τ : D.what₂.Tau =>
      D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) (sgT u) (Tf.clsP.lat c)) := by
    intro c
    refine mem_localization_delAtr_of_basis D.what₂.places D.plEq D.val_eq _ D.what₂.embLL (embT D) he (gramP D) (sgT u) (D.fm u).sg
      (fun τ => natW_shW _ _) (Tf.clsP.lat c) (hK c) (val y c) w (B w c) (hB w c) ?_
    have := h c
    simp only [Formalism.L2.GlobalTheoryTheory.Br.coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearEquiv.coe_coe] at this
    rw [hval] at this
    exact this
  choose s hs hx using hc
  refine (vl_mem_span_intW_iff D.what₂.places (fun w => D.plEq w) D.val_eq w _ _).2 ⟨∏ c, s c, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, -, hc⟩ := ((D.plEq w).isPrime.prod_mem_iff).1 hmem
    exact hs c hc
  · refine (Tf.valP.lat _).2 fun w' c B' hB' => ?_
    rw [hval]
    refine local_of_mem_delAtr D.what₂.places D.plEq D.val_eq _ D.what₂.embLL (embT D) he D.plEq.surjective (gramP D) (sgT u)
      (D.fm u).sg (fun τ => natW_shW _ _) (Tf.clsP.lat c) (hK c) _ ?_ w' B' hB'
    have e : (∏ c', s c') = (∏ c' ∈ Finset.univ.erase c, s c') * s c := (Finset.prod_erase_mul _ _ (Finset.mem_univ c)).symm
    have key : ∀ r : 𝓞 D.what₂.LL, val (r • y) c = r • val y c := fun r => by
      rw [← algebraMap_smul D.what₂.LL r y, map_smul, Pi.smul_apply, algebraMap_smul]
      rfl
    have hm := Submodule.smul_mem _ (∏ c' ∈ Finset.univ.erase c, s c') (hx c)
    rw [key, e]
    convert hm using 1
    exact mul_smul _ _ _

end Localisation

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem root_mem_intW (D : D7) (w : D.what₂.places.Pl) (r : D.what₂.LL) (n : ℕ) (hn : 0 < n) (h : r ^ n = 1) :
    r ∈ intW D.what₂.places w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w r
  have h1 : D.what₂.places.val w (r ^ n) = 0 := by rw [h, AddValuation.map_one]
  rw [AddValuation.map_pow] at h1
  by_contra hneg
  push_neg at hneg
  have : n • D.what₂.places.val w r < 0 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, D.what₂.places.val w r = k := by
      rcases h2 : D.what₂.places.val w r with _ | k
      · rw [h2] at hneg; exact absurd hneg (not_lt.2 le_top)
      · exact ⟨k, rfl⟩
    rw [hk] at hneg ⊢
    have hk0 : k < 0 := by exact_mod_cast hneg
    have : (n : ℤ) * k < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hn) hk0
    rw [← WithTop.coe_nsmul]
    exact_mod_cast (by simpa [nsmul_eq_mul] using this)
  rw [h1] at this
  exact lt_irrefl _ this

set_option maxHeartbeats 4000000 in

theorem exists_integralPendingObject_symmetricFormsLevel : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → ∃ P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u, Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro D u Ch chOf Tf hMap hBe hχ
  choose B hB using GlobalTheory.ClsPLocBasis.exists_isLocBasis_clsP D u Ch chOf Tf
  obtain ⟨o, ho⟩ := Formalism.L2.GlobalTheoryTheory.Br.exists_onP Tf
  set Bm : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
    fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) with hBm
  have hBu : ∀ w c, IsUnit (Bm w c).det := fun w c => (Matrix.isUnit_iff_isUnit_det _).1 (B w c).isUnit
  have hL : Formalism.L2.GlobalTheoryTheory.Br.LowerSymmetricCompatible Tf := ⟨hBe, hMap⟩
  refine Formalism.L2.GlobalTheoryTheory.Br.brExists_of_rest4S Tf hL Bm hBu (gPof Bm hBu o) ⟨?_, ?_,
    Formalism.L2.GlobalTheoryTheory.Br.ipV_co_ofS Tf Bm hBu o ho, Formalism.L2.GlobalTheoryTheory.Br.weightedInner_self_eq_sum_coords_of_orthonormal' Tf Bm hBu o (fun τ => Or.inl (ho τ))⟩
  · intro w x hx c
    obtain ⟨B', hB'eq, hB'⟩ := exists_isLocBasis_dual D u Ch chOf Tf w c (B w c) (hB w c)
    obtain ⟨n, hn, hχ'⟩ := hχ
    obtain ⟨hpow, r, hr⟩ := hχ' (Tf.tilAd.ka c)
    have hrn : r ^ n = 1 := by
      apply D.what₂.embLL.injective
      rw [map_pow, hr, map_one, hpow]
    have hr0 : r ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hrn; exact zero_ne_one hrn
    have hri : r⁻¹ ∈ intW D.what₂.places w := by
      have : r⁻¹ = r ^ (n - 1) := (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hn.ne', hrn])).symm
      rw [this]; exact pow_mem (root_mem_intW D w r n hn hrn) _
    have hχr : ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) = D.what₂.embLL r⁻¹ := by
      rw [Units.val_inv_eq_inv_val, ← hr, map_inv₀]
    have hx' : x ∈ Submodule.span (intW D.what₂.places w) (((D.fm u).lat D.R.m).L : Set ((D.fm u).lat D.R.m).V) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨P, hP, hPv⟩ := ((Tf.val D.R.m le_rfl (Or.inr rfl)).lat y).1 hy w ((D.fm u).til c) B' hB'
      rw [GlobalTheory.coMTS_of_gaInv D u Ch chOf Tf Bm w c B' (hBu w c) hB'eq _ P hPv, hχr]
      exact intSpan_smul' D w _ _ hri P hP
    | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, Pi.add_apply, map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : a • y = (a : D.what₂.LL) • y := rfl
      rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
      exact intSpan_smul' D w _ (a : D.what₂.LL) a.2 _ hy
  · intro w z hz
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact GlobalTheory.PtCo.ptCo_mem_intSpan D u Ch chOf Tf B hB w y hy c
    · intro h
      obtain ⟨y, rfl⟩ := GlobalTheory.FormsRatOfInt.exists_ptEmb_of_coord_int D u Ch chOf Tf B w z hz h
      exact ⟨y, mem_SP_of_coord_integral D u Ch chOf Tf B hB w y h, rfl⟩

end GlobalTheory.RedPt0Pend
