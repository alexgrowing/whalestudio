import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_glint_of_rat [NeZero n] (P : HeightOneSpectrum (𝓞 E)) {z : GL (Fin n) (AfE F E)} (hz : z ∈ St (1 : GL (Fin n) (AfE F E)))
    (hr : ∀ i j, ∃ e : E, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e) :
    ∃ c : GLint E n P, (∀ i j, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (c.1 (Pi.single j 1) i)) ∧
      GlobalTheory.TopStep.redGL n P c = redAt 1 P ⟨z, hz⟩ := by
  classical
  obtain ⟨y, hy, hyr⟩ := St_one_int hz
  obtain ⟨y', hy', -⟩ := St_one_int (inv_mem hz)
  choose A hA using hr
  have hmap : (z : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = (Matrix.of A).map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hA i j
  have hdet : IsUnit (Matrix.of A).det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 := congrArg Matrix.det hmap
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, h0, map_zero] at h1
    have hu : IsUnit (z : Matrix (Fin n) (Fin n) (AfE F E)).det := (Matrix.isUnit_iff_isUnit_det _).1 z.isUnit
    exact (hu.map (adAt F P)).ne_zero h1
  set γ : GL (Fin n) E := Matrix.nonsingInvUnit (Matrix.of A) hdet with hγ
  have hzγ : ∀ r s, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E _ ((γ : Matrix (Fin n) (Fin n) E) r s) :=
    fun r s => hA r s
  have hzγ' := GlobalTheory.Mem.Col2.RatFrPt.adAt_inv hzγ
  have hint : ∀ {x : AfE F E} {e : E}, x ∈ RInt F E → adAt F P x = algebraMap E _ e → IntAt P e := fun {x e} hx he => by
    rw [GlobalTheory.CharValCompare.intAt_iff, ← valued_algebraMap, ← he]
    exact (mem_rInt_iff F E x).1 hx P
  have h1 : ∀ i j, IntAt P ((γ : Matrix (Fin n) (Fin n) E) i j) := fun i j => hint (hy i j ▸ (y i j).2) (hzγ i j)
  have h2 : ∀ i j, IntAt P (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := fun i j => hint (hy' i j ▸ (y' i j).2) (hzγ' i j)
  have hmv : ∀ (N : Matrix (Fin n) (Fin n) E), (∀ i j, IntAt P (N i j)) → ∀ x : Sp E n, x ∈ stdAt E n P → N *ᵥ x ∈ stdAt E n P :=
    fun N hN x hx => GlobalTheory.TopStep.mem_stdAt.2 fun i => by
      show IntAt P (∑ j, N i j * x j)
      exact GlobalTheory.TopStep.intAt_sum _ fun j _ => (hN i j).mul (GlobalTheory.TopStep.mem_stdAt.1 hx j)
  have hc : GlobalTheory.Mem.Col2.RatFrPt.glEquiv γ ∈ GLint E n P := fun x => by
    rw [GlobalTheory.Mem.Col2.RatFrPt.glEquiv_apply]
    refine ⟨fun h => ?_, hmv _ h1 x⟩
    have := hmv _ h2 _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  refine ⟨⟨_, hc⟩, fun i j => ?_, Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [hzγ, GlobalTheory.Mem.Col2.RatFrPt.glEquiv_single]
  · have hR := GlobalTheory.Mem.Col2.LevLiftPt.isRed_of_red P _ hc _ (fun x hx => GlobalTheory.TopStep.redV_apply ⟨_, hc⟩ hx) z
      (fun r s => by rw [LinearMap.toMatrix'_apply, hzγ]; congr 1; exact (GlobalTheory.Mem.Col2.RatFrPt.glEquiv_single γ r s).symm) i j
    refine hR.unique ?_
    rw [hyr P i j, hy i j]
    have := GlobalTheory.Mem.Col2.PtExist.hasRes_redA (F := F) P (y i j).2
    rwa [redA_int P (y i j).2] at this

theorem isPtOf_mul_rat [NeZero n] {hcm : CMData F E} {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g z : GL (Fin n) (AfE F E)}
    {p : DecoF E n ∅ SG Q} (hg : IsPtOf hcm g p) (hzU : z ∈ UAd hcm n) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))) (c : GLQ E n Q)
    (hcz : ∀ (P : Q) i j, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ ((c P).1 (Pi.single j 1) i)) :
    IsPtOf hcm (g * z) (((1, (fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹, c⁻¹) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hInt : ∀ {x : GL (Fin n) (AfE F E)} (hx : x ∈ St (1 : GL (Fin n) (AfE F E))) (i j : Fin n),
      (x : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ∀ w : HeightOneSpectrum (𝓞 E),
        HasRes w (adAt F w ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j))
          (((redAt 1 w ⟨x, hx⟩ : GL (Fin n) (𝓞 E ⧸ w.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)) i j) := by
    intro x hx i j
    obtain ⟨y, hy, hr⟩ := St_one_int hx
    refine ⟨hy i j ▸ (y i j).2, fun w => ?_⟩
    rw [hr w i j, hy i j]
    have := GlobalTheory.Mem.Col2.PtExist.hasRes_redA (F := F) w (y i j).2
    rwa [redA_int w (y i j).2] at this
  have hzi : z⁻¹ ∈ St (1 : GL (Fin n) (AfE F E)) := inv_mem hz
  have hm := GlobalTheory.Mem.Col2.LevLiftPt.isPtOf_mul_fr (m := z⁻¹) hg (inv_mem hzU) (fun i j => (hInt hzi i j).1)
    (fun i j => by rw [inv_inv]; exact (hInt hz i j).1) (fun P hP => absurd hP (Finset.notMem_empty P))
    (h := (fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹) (fun w i j => ?_) c⁻¹ (fun P i j => ?_)
  · rwa [inv_inv] at hm
  · have e : ((fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹ w) = redAt 1 w.1 ⟨z⁻¹, hzi⟩ := by
      rw [Pi.inv_apply, ← map_inv]
      rfl
    rw [e]
    exact (hInt hzi i j).2 w.1
  · rw [inv_inv, Pi.inv_apply, inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    have e : ∀ x, adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i x * (z : Matrix (Fin n) (Fin n) (AfE F E)) x j) =
        algebraMap E (P.1.adicCompletion E) (p.fr P (Pi.single x 1) i * (c P).1 (Pi.single j 1) x) := fun x => by
      rw [map_mul, map_mul, hg.fr P, hcz P]
    rw [Finset.sum_congr rfl fun x _ => e x, ← map_sum]
    refine congrArg (algebraMap E (P.1.adicCompletion E)) ?_
    show _ = (p.fr P) ((c P).1 (Pi.single j 1)) i
    exact (Finset.sum_congr rfl fun k _ => mul_comm _ _).trans (GlobalTheory.TopStep.apply_eq_sum (p.fr P).toLinearMap _ i).symm

theorem glq_free {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {p : DecoF E n ST SG Q} {a b : GLG E n SG} {c d : GLQ E n Q}
    (h : ((1, a, c) : UF E n × GLG E n SG × GLQ E n Q) • p = ((1, b, d) : UF E n × GLG E n SG × GLQ E n Q) • p) : c = d := by
  funext P
  have e := congrArg (fun q : DecoF E n ST SG Q => q.fr P) h
  change (1 : UF E n).1 * p.1.2 P * ((c P)⁻¹).1 = (1 : UF E n).1 * p.1.2 P * ((d P)⁻¹).1 at e
  exact inv_injective (Subtype.ext (mul_left_cancel e))

end Gen

section Blocks

variable {κ : Type} [CommRing κ] {n r b : ℕ}

theorem coarseBlockIndex_eq_twoBlock (hn : n = r + b) : (fun i : Fin n => coarse r [b] i.val) = Formalism.L2.DIV.blk2 r := by
  funext i
  unfold Formalism.L2.DIV.blk2
  by_cases hi : i.val < r
  · rw [if_pos hi, coarse_of_lt hi]
  · rw [if_neg hi, coarse_of_le (Nat.not_lt.mp hi)]
    have : i.val - r < b := by have := i.2; omega
    simp [blkIdx, this]

theorem mem_HQ_iff (hn : n = r + b) (M : GL (Fin n) κ) : M ∈ HQ κ n r b ↔ M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i : Fin n => coarse r [b] i.val) ↔
    (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (Formalism.L2.DIV.blk2 r)
  rw [coarseBlockIndex_eq_twoBlock hn]

theorem blkDet_HQ (hn : n = r + b) (M : GL (Fin n) κ) (h1 : M ∈ HQ κ n r b) (h2 : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    Formalism.L2.Col.blkDet n κ (coarse r [b]) 1 ⟨M, h1⟩ = Formalism.L2.DIV.blkDet (Formalism.L2.DIV.blk2 r) 1 ⟨M, h2⟩ := by
  apply Units.ext
  rw [Formalism.L2.Col.blkDet_val]
  have : ∀ β : Fin n → ℕ, β = Formalism.L2.DIV.blk2 r → ((M : Matrix (Fin n) (Fin n) κ).toSquareBlock β 1).det =
      ((M : Matrix (Fin n) (Fin n) κ).submatrix (Subtype.val : {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} → Fin n) Subtype.val).det := by
    rintro _ rfl
    rfl
  exact this _ (coarseBlockIndex_eq_twoBlock hn)

end Blocks

section Chr

variable {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chr_inv_val (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (emb : X.K →+* ℂ) (h : Λ.grp) (c : Θ.grp) :
    emb ((Λ.chr h⁻¹ * Θ.chr c⁻¹ : X.Kˣ) : X.K) =
      (∏ w, (emb (((Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ : X.Kˣ) : X.K))⁻¹) *
        ∏ P, (emb (((Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ : X.Kˣ) : X.K))⁻¹ := by
  have hc : (Θ.chr c : X.Kˣ) = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ := by
    rw [LevQFam.chr]
    exact piChar_apply _ _ c
  rw [map_inv, map_inv, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀,
    LevFam.chr_apply, hc, Units.coe_prod, map_prod, Finset.prod_inv_distrib, Units.coe_prod, map_prod, Finset.prod_inv_distrib]

variable {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem levQX_lam_inv (emb : X.K →+* ℂ) (hn : R.N R.m - 1 = R.r + R.m * R.t) (P : QE sel (mu : Chr X.F X.E X.K))
    (k : (levQX R sel mu P).H) (hk : GlobalTheory.TopStep.redGL _ P.1 k.1 ∈ blockTri (blk2 R.r)) :
    (emb (((levQX R sel mu P).lam k : X.Kˣ) : X.K))⁻¹ =
      emb ((resChar (mu : Chr X.F X.E X.K) P.1 (Formalism.L2.DIV.blkDet (blk2 R.r) 1 ⟨_, hk⟩) : X.Kˣ) : X.K) := by
  rw [levQX_lam]
  change (emb (((lamQP (mu : Chr X.F X.E X.K) P.1 (R.N R.m - 1) R.r (R.m * R.t))⁻¹ ⟨_, k.2⟩ : X.Kˣ) : X.K))⁻¹ = _
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, lamQP, lamQ_apply]
  exact congrArg (fun d => emb ((resChar (mu : Chr X.F X.E X.K) P.1 d : X.Kˣ) : X.K)) (blkDet_HQ hn _ _ hk)

end Chr

set_option maxHeartbeats 2000000 in
theorem rdLevOn_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  intro B X I hOk hPins l Z a bad S y lat st h c ξ hξ z hzA hz hzU
  have hn : B.R.N B.R.m - 1 = B.R.r + B.R.m * B.R.t := Formalism.L2.Col.rank_X'_eq B.R
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  choose cc hcc hred using fun P : I.Q a => exists_glint_of_rat (F := B.host.F) P.1 hz (hzA P)
  have hpt := isPtOf_mul_rat (h.pt c) hzU hz (cc : GLQ B.fields.E (B.R.N B.R.m - 1) (I.Q a)) hcc
  set hv : GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs := fun w => redAt 1 w.1 ⟨z, hz⟩ with hhv
  have hΘ : ∀ P : I.Q a, cc P ∈ (levQX B.R I.sel (I.tup a) P).H ↔ redAt 1 P.1 ⟨z, hz⟩ ∈ blockTri (blk2 B.R.r) := fun P => by
    show GlobalTheory.TopStep.redGL _ P.1 (cc P) ∈ HQ _ _ B.R.r (B.R.m * B.R.t) ↔ _
    rw [hred P]
    exact mem_HQ_iff hn _
  refine ⟨(h.lev c z _ hpt).trans ⟨?_, ?_⟩, fun hU h1 h2 => ?_⟩
  · rintro ⟨⟨γ, a', c'⟩, hγ, e⟩
    obtain rfl : γ = 1 := Subtype.ext ((toGLm _ _).injective (hγ.trans (map_one _).symm))
    have e1 : a'.1 = hv⁻¹ := glg_free e
    have e2 : c'.1 = cc⁻¹ := glq_free e
    refine ⟨fun w => ?_, fun P => (hΘ P).1 ?_⟩
    · have := a'.2 w (Set.mem_univ w)
      rw [e1] at this
      exact inv_mem_iff.1 this
    · have := c'.2 P (Set.mem_univ P)
      rw [e2] at this
      exact inv_mem_iff.1 this
  · rintro ⟨h1, h2⟩
    exact ⟨(1, (⟨hv, fun w _ => h1 w⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹,
      (⟨cc, fun P _ => (hΘ P).2 (h2 P)⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹), by show ufGL _ _ 1 = 1; exact map_one _, rfl⟩
  · have hΛ : hv ∈ (rowTyG I.Ch I.Ps).grp := fun w _ => h1 w
    have hQ : cc ∈ (levQX B.R I.sel (I.tup a)).grp := fun P _ => (hΘ P).2 (h2 P)
    have key := h.chr c ⟨z, hU⟩ (1, (⟨hv, hΛ⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹, (⟨cc, hQ⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹)
      (by show ufGL _ _ 1 = 1; exact map_one _) hpt
    refine key.trans ?_
    change B.embLL (((rowTyG I.Ch I.Ps).chr (⟨hv, hΛ⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹ *
      (levQX B.R I.sel (I.tup a)).chr (⟨cc, hQ⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹ : B.LLˣ) : B.LL) = _
    refine (chr_inv_val (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) B.embLL ⟨hv, hΛ⟩ ⟨cc, hQ⟩).trans ?_
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun P _ => ?_)
    have hP : GlobalTheory.TopStep.redGL _ P.1 (cc P) ∈ blockTri (blk2 B.R.r) := by rw [hred P]; exact h2 P
    refine (levQX_lam_inv B.embLL hn P ⟨cc P, hQ P (Set.mem_univ P)⟩ hP).trans ((hξ P.1 P.2 _).symm.trans ?_)
    have e : (⟨GlobalTheory.TopStep.redGL _ P.1 (cc P), hP⟩ : blockTri (blk2 B.R.r)) = ⟨redAt 1 P.1 ⟨z, hz⟩, h2 P⟩ := Subtype.ext (hred P)
    exact congrArg (fun M => ((ξ P.1 (Formalism.L2.DIV.blkDet (blk2 B.R.r) 1 M) : ℂˣ) : ℂ)) e

end GlobalTheory.SeeSaw.TwLev
