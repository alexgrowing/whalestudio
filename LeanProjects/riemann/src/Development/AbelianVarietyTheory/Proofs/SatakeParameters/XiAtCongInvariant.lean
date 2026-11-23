import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOverVUnder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
import Formalism.LocalToGlobal.Columns.QthExistsBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.MidIndep

open GlobalTheory.CongLevel GlobalTheory.TopStep GlobalTheory.GO.ChRoot

theorem intAt_of_seam {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) {y : X.E}
    (h : IntAt (seamP s P) (s.iE y)) : IntAt P y := by
  obtain ⟨r, s0, hs0, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE with hf
  refine ⟨f.symm r, f.symm s0, fun hm => hs0 ?_, ?_⟩
  · have := (mem_seamP s P (f.symm s0)).2 hm
    rwa [f.apply_symm_apply] at this
  · apply s.iE.injective
    have e1 : ∀ z : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E z) = algebraMap (𝓞 D.host.E) D.host.E (f z) := fun z => rfl
    rw [map_mul, e1, e1, f.apply_symm_apply, f.apply_symm_apply, e]

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  symm
  refine Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) ?_).toEquiv
  ext z
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective z
  rw [mem_seamP, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem congAt_entry {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (n N : ℕ)
    (k : Sp X.E N ≃ₗ[X.E] Sp X.E N) (h : CongAt (F := D.host.F) (seamP s P) n (ratA D.host.F (seamGL s k))) (a b : Fin N) :
    IntAtA (F := D.host.F) (seamP s P) (iA D.host.F D.host.E (s.iE ((((qOf P : ℕ) : X.E) ^ n)⁻¹ * (k (Pi.single b 1) a - (if a = b then (1 : X.E) else 0))))) := by
  convert h a b using 1
  rw [qOf_seamP, map_mul s.iE, map_inv₀, map_pow, map_natCast, map_mul]
  congr 1
  rw [Matrix.sub_apply, Matrix.one_apply, map_sub, map_sub]
  congr 1
  split_ifs <;> simp

theorem congAt_local {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (n N : ℕ)
    (k : Sp X.E N ≃ₗ[X.E] Sp X.E N) (h : CongAt (F := D.host.F) (seamP s P) n (ratA D.host.F (seamGL s k))) :
    ∀ x ∈ stdAt X.E N P, ((qOf P ^ n : ℕ) : X.E)⁻¹ • (k x - x) ∈ stdAt X.E N P := by
  classical
  obtain ⟨ι, hι⟩ := exists_isAdIso D.host.F D.host.E
  have hent : ∀ a b : Fin N, IntAt P ((((qOf P : ℕ) : X.E) ^ n)⁻¹ *
      (k (Pi.single b 1) a - (if a = b then (1 : X.E) else 0))) := by
    intro a b
    have h1 := hι.val_le (congAt_entry s P n N k h a b)
    rw [show ι (iA D.host.F D.host.E (s.iE ((((qOf P : ℕ) : X.E) ^ n)⁻¹ * (k (Pi.single b 1) a - (if a = b then (1 : X.E) else 0))))) =
      algebraMap D.host.E _ (s.iE ((((qOf P : ℕ) : X.E) ^ n)⁻¹ * (k (Pi.single b 1) a - (if a = b then (1 : X.E) else 0)))) from hι.1 _] at h1
    refine intAt_of_seam s P ((qth_intAt_iff _ _).2 ?_)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact h1
  intro x hx
  rw [mem_stdAt']
  intro l
  have ex : k x - x = ∑ b, x b • (k (Pi.single b 1) - Pi.single b 1) := by
    conv_lhs => rw [show x = ∑ b, x b • (Pi.single b (1 : X.E) : Sp X.E N) by
      funext m; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, smul_sub]
  rw [ex, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum _ fun b _ => ?_
  have e2 : (((qOf P ^ n : ℕ) : X.E))⁻¹ * (x b • (k (Pi.single b 1) - Pi.single b 1) : Sp X.E N) l =
      x b * ((((qOf P : ℕ) : X.E) ^ n)⁻¹ * (k (Pi.single b 1) l - (if l = b then (1 : X.E) else 0))) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
    push_cast
    ring
  rw [e2]
  exact (mem_stdAt'.1 hx b).mul (hent l b)

theorem cong_inv {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (N d : ℕ) (hd : 1 ≤ d)
    (κ : Sp E N ≃ₗ[E] Sp E N) (h : ∀ x ∈ stdAt E N P, ((qOf P ^ d : ℕ) : E)⁻¹ • (κ x - x) ∈ stdAt E N P) :
    ∀ x ∈ stdAt E N P, ((qOf P ^ d : ℕ) : E)⁻¹ • (κ⁻¹ x - x) ∈ stdAt E N P := by
  have hq1 : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hq : ((qOf P ^ d : ℕ) : E) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hq1

  have hk : ∀ x ∈ stdAt E N P, κ x ∈ stdAt E N P := by
    intro x hx
    have := add_mem (GlobalTheory.Mem.LevFin.natCast_smul_mem _ (qOf P ^ d) (h x hx)) hx
    rwa [smul_smul, mul_inv_cancel₀ hq, one_smul, sub_add_cancel] at this
  have hs : ∀ b : Fin N, (Pi.single b (1 : E) : Sp E N) ∈ stdAt E N P := by
    intro b
    rw [mem_stdAt']
    intro l
    rw [Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  set M : Matrix (Fin N) (Fin N) E := LinearMap.toMatrix' κ.toLinearMap with hM
  have hMi : ∀ a b, IntAt P (M a b) := fun a b => by
    rw [hM, LinearMap.toMatrix'_apply]
    exact mem_stdAt'.1 (hk _ (hs b)) a

  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hZ : ∀ a b : Fin N, IntAt P (((qOf P : ℕ) : E)⁻¹ * (M a b - (if a = b then (1 : E) else 0))) := by
    intro a b
    have h1 := (mem_stdAt'.1 (h _ (hs b))) a
    have h2 := (intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P) (qOf P)) e).mul h1
    have e1 : ((qOf P : ℕ) : E)⁻¹ * (M a b - (if a = b then (1 : E) else 0)) =
        ((qOf P : ℕ) : E) ^ e * ((((qOf P ^ (e + 1) : ℕ) : E)⁻¹ • (κ (Pi.single b 1) - Pi.single b 1) : Sp E N) a) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hM, LinearMap.toMatrix'_apply]
      simp only [Pi.single_apply, eq_comm (a := a)]
      push_cast
      field_simp
      ring
    rw [e1]
    exact h2
  have hred : redP P M.det = 1 := by
    have e3 : M = Matrix.of fun a b : Fin N => (if a = b then (1 : E) else 0) +
        ((qOf P : ℕ) : E) * (((qOf P : ℕ) : E)⁻¹ * (M a b - (if a = b then (1 : E) else 0))) := by
      ext a b
      rw [Matrix.of_apply, mul_inv_cancel_left₀ hq1]
      ring
    rw [e3, GlobalTheory.LastSteps.redP_det_add_q (fun a b => ?_) hZ]
    · have e2 : (Matrix.of fun a b : Fin N => if a = b then (1 : E) else 0) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      rw [e2, Matrix.det_one, reduction_one₂]
    · split_ifs
      · exact intAt_one
      · exact intAt_zero
  obtain ⟨hd0, hdi⟩ := GlobalTheory.BlockDecompositionK1.intAt_inv_of_isUnit (det_int hMi).1 (by rw [hred]; exact isUnit_one)

  have hinv : LinearMap.toMatrix' (κ⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = M⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [hM, ← LinearMap.toMatrix'_comp]
    have : (κ⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ κ.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [this, LinearMap.toMatrix'_id]
  have hIi : ∀ a b, IntAt P (M⁻¹ a b) := by
    intro a b
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine hdi.mul ?_
    rw [Matrix.adjugate_apply]
    refine (det_int fun i j => ?_).1
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    · exact hMi i j
  have hki : ∀ x ∈ stdAt E N P, κ⁻¹ x ∈ stdAt E N P := by
    intro x hx
    rw [mem_stdAt']
    intro l
    have e4 : κ⁻¹ x = LinearMap.toMatrix' (κ⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap *ᵥ x := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [e4, hinv, Matrix.mulVec, dotProduct]
    exact intAt_sum _ fun b _ => (hIi l b).mul (mem_stdAt'.1 hx b)
  intro x hx
  have := neg_mem (h _ (hki x hx))
  rwa [show κ (κ⁻¹ x) = x from LinearEquiv.apply_symm_apply κ x, ← smul_neg, neg_sub] at this

theorem muAt_det_cong {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (N d : ℕ) (hd : 1 ≤ d)
    (κ : Sp X.E N ≃ₗ[X.E] Sp X.E N) (h : ∀ x ∈ stdAt X.E N P.1, ((qOf P.1 ^ d : ℕ) : X.E)⁻¹ • (κ x - x) ∈ stdAt X.E N P.1) :
    muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) = 1 := by
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Mem.LevFin.qOf_ne P.1
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hs : ∀ b : Fin N, (Pi.single b (1 : X.E) : Sp X.E N) ∈ stdAt X.E N P.1 := by
    intro b
    rw [mem_stdAt']
    intro l
    rw [Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hZ : ∀ a b : Fin N, IntAt P.1 (((qOf P.1 : ℕ) : X.E)⁻¹ *
      (κ (Pi.single b 1) a - (Pi.single b (1 : X.E) : Sp X.E N) a)) := by
    intro a b
    have h1 := (mem_stdAt'.1 (h _ (hs b))) a
    have h2 := (intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) e).mul h1
    have e1 : ((qOf P.1 : ℕ) : X.E)⁻¹ * (κ (Pi.single b 1) a - (Pi.single b (1 : X.E) : Sp X.E N) a) =
        ((qOf P.1 : ℕ) : X.E) ^ e * ((((qOf P.1 ^ (e + 1) : ℕ) : X.E)⁻¹ • (κ (Pi.single b 1) - Pi.single b 1) : Sp X.E N) a) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [e1]
    exact h2
  have hdet : ((LinearEquiv.det κ : X.Eˣ) : X.E) = Matrix.det (Matrix.of fun a b : Fin N =>
      (if a = b then (1 : X.E) else 0) + ((qOf P.1 : ℕ) : X.E) * (((qOf P.1 : ℕ) : X.E)⁻¹ *
        (κ (Pi.single b 1) a - (Pi.single b (1 : X.E) : Sp X.E N) a))) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
    congr 1
    ext a b
    rw [LinearMap.toMatrix'_apply, Matrix.of_apply, mul_inv_cancel_left₀ hq]
    simp [Pi.single_apply, eq_comm]
  have hred : redP P.1 ((LinearEquiv.det κ : X.Eˣ) : X.E) = 1 := by
    rw [hdet, GlobalTheory.LastSteps.redP_det_add_q (fun a b => ?_) hZ]
    · have e2 : (Matrix.of fun a b : Fin N => if a = b then (1 : X.E) else 0) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      rw [e2, Matrix.det_one, reduction_one₂]
    · split_ifs
      · exact intAt_one
      · exact intAt_zero
  rw [GlobalTheory.CoupledLaw.muAt_unit _ _ (by rw [hred]; exact isUnit_one)]
  unfold rhoS
  rw [GlobalTheory.LastSteps.unitV_congr _ (hred.trans reduction_one₂.symm), GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one]

theorem extE_cong_mem {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : j < R.m) (b : L.β j) (P : rowSG Pr sel mu)
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (h1 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (κ x - x) ∈ stdAt X.E (R.N j) P.1)
    (h2 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (κ⁻¹ x - x) ∈ stdAt X.E (R.N j) P.1) :
    GlobalTheory.CongLevel.extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P) ∧
      chiInv Ch sel mu cst j P (L.h j b P) (GlobalTheory.CongLevel.extE (cOf R j) κ) = 1 := by
  have hq := GlobalTheory.Mem.LevFin.qOf_ne P.1
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P := ⟨_, rfl⟩
  rw [← hh]
  obtain ⟨e, hb, he⟩ : ∃ e : ℕ, (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P.1 ∧
      ((qOf P.1 : X.E) ^ e) • h x ∈ lamYat (Pr := Pr) (R := R) j P.1) ∧ e + 1 ≤ cst.D P := by
    by_cases hP : P.1 ∈ Pr.vGs
    · have hs : h ∈ stabL X.E _ (lamYat (Pr := Pr) j P.1) := hh ▸ hL.stabG j b P hP
      refine ⟨0, fun x hx => ⟨((inv_mem hs) x).2 hx, ?_⟩, by rw [hL.depthG P hP]⟩
      rw [pow_zero, one_smul]
      exact (hs x).2 hx
    · refine ⟨j, hh ▸ hL.boundQ j b P hP, ?_⟩
      have := hL.depthQ' P hP
      omega
  obtain ⟨d, hd⟩ : ∃ d, cst.D P = (e + 1) + d := ⟨cst.D P - (e + 1), by omega⟩
  have mono : ∀ g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j),
      (∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (g x - x) ∈ stdAt X.E (R.N j) P.1) →
      ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ (e + 1) : ℕ) : X.E)⁻¹ • (g x - x) ∈ stdAt X.E (R.N j) P.1 := by
    intro g hg x hx
    have := GlobalTheory.Mem.LevFin.natCast_smul_mem _ (qOf P.1 ^ d) (hg x hx)
    convert this using 1
    rw [smul_smul, hd]
    congr 1
    push_cast
    field_simp
    ring
  have c1 := GlobalTheory.Mem.LevFin.conj_extE_cong hq _ h hb κ (mono κ h1)
  have c2 := GlobalTheory.Mem.LevFin.conj_extE_cong hq _ h hb κ⁻¹ (mono κ⁻¹ h2)
  have e2 : (h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ * h)⁻¹ = h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ⁻¹ * h := by
    rw [← GlobalTheory.CongLevel.extE_inv]
    group
  have hJ : h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ * h ∈ Jat (Pr := Pr) cst.sharp j P.1 :=
    GlobalTheory.Mem.LevFin.mem_Jat _ _ _ _ (GlobalTheory.Mem.LevFin.stab_of_cong hq _ _ c1 (by rw [e2]; exact c2)) c1
  refine ⟨⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩, ?_⟩
  · show (MulAut.conj h⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) κ) ∈ Jat (Pr := Pr) cst.sharp j P.1
    have e : (MulAut.conj h⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) κ) = h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ * h := by simp
    rw [e]
    exact hJ
  · unfold chiInv
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul]
    have eq : ((h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ * h : AutY X R j)).toLinearMap = LinearMap.id + ((qOf P.1 : ℕ) : X.E) •
        (((qOf P.1 : ℕ) : X.E)⁻¹ • (((h⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ * h : AutY X R j)).toLinearMap - LinearMap.id)) := by
      rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
      abel
    rw [eq]
    refine GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong Ch mu cst.sharp j P.1 hj _ fun x hx => ?_
    simpa [lamYat] using c1 x hx

end GlobalTheory.TwU.MidIndep

namespace GlobalTheory.TwU

open GlobalTheory.CongLevel GlobalTheory.TwU.MidIndep

theorem xiAt_cong_invariant : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (i : ℕ) (hi : i + 1 < D.R.m), i < t.m2 → ∀ (β : (St i (Nat.le_of_succ_le hi.le)).Ch) (β' : (St (i + 1) hi.le).Ch) (P : SB t μ)
    (k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i)) (k' : Sp t.X.E (D.R.N (i + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (i + 1))),
    CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam k)) →
    CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam k')) → ∀ w,
    XiAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i (A.ib i (Nat.lt_of_succ_lt hi) β) P) ((t.idx μ).h (i + 1) (A.ib (i + 1) hi β') P) (inFr k k' w) =
      XiAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i (A.ib i (Nat.lt_of_succ_lt hi) β) P) ((t.idx μ).h (i + 1) (A.ib (i + 1) hi β') P) w := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hp _ i hi him β β' P k k' hk hk' w
  have hL := t.idx_ok μ
  have hD1 : 1 ≤ (t.cst μ).D P := hL.cst_ok.D_pos P
  have c1 := congAt_local t.seam P.1 _ _ k hk
  have c2 := congAt_local t.seam P.1 _ _ k' hk'
  have m1 := extE_cong_mem hL i (by omega) (A.ib i (Nat.lt_of_succ_lt hi) β) P k c1 (cong_inv P.1 _ _ hD1 k c1)
  have m2 := extE_cong_mem hL (i + 1) hi (A.ib (i + 1) hi β') P k' c2 (cong_inv P.1 _ _ hD1 k' c2)
  have key := GlobalTheory.UnfoldTwoSided.xiAt_two_sided t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hp.fields t.pr_ok
    hp.ch.ch_ok hp.sel hL i him (A.ib i (Nat.lt_of_succ_lt hi) β) (A.ib (i + 1) hi β') P _ _ k k' m1.1 m2.1
    (GlobalTheory.CongLevel.extE_inX _ k) (GlobalTheory.CongLevel.extE_inX _ k') w
  rw [m1.2, m2.2, muAt_det_cong t.Ch t.sel (t.tup μ) (t.cst μ) i P _ _ hD1 k c1,
    muAt_det_cong t.Ch t.sel (t.tup μ) (t.cst μ) i P _ _ hD1 k' c2] at key
  simpa using key

end GlobalTheory.TwU
