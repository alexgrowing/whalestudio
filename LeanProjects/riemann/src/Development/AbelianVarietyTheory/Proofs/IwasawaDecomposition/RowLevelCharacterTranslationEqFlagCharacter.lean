import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.Columns.DetChrOf
import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.R3.RowChr

section Blocks
variable {κ K : Type} [CommRing κ] [Field K]

theorem coarse_eq_blkOf {n r t m : ℕ} (hn : n = r + m * t) :
    (fun i : Fin n => Formalism.L2.Col.coarse r (List.replicate m t) i.val) = blkOf r t := by
  funext i
  unfold blkOf
  split_ifs with h
  · exact Formalism.L2.Col.coarse_of_lt h
  · have hi := i.2
    have h1 : i.val - r < m * t := by omega
    have ht : 0 < t := Nat.pos_of_ne_zero fun e => by simp [e] at h1
    rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h), Formalism.L2.Col.blkIdx_replicate ht m _ h1]

theorem coarseBlockIndex_eq_twoBlock {n r b : ℕ} (hn : n = r + b) :
    (fun i : Fin n => Formalism.L2.Col.coarse r [b] i.val) = blk2 r := by
  funext i
  unfold blk2
  split_ifs with h
  · exact Formalism.L2.Col.coarse_of_lt h
  · have hi := i.2
    have h1 : i.val - r < b := by omega
    rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    simp [Formalism.L2.Col.blkIdx, h1]

theorem blockDeterminant_eq_diagonalBlockDet {n : ℕ} {β : ℕ → ℕ} {b : Fin n → ℕ} (e : (fun i : Fin n => β i.val) = b) (c : ℕ)
    (M : Formalism.L2.Col.btG n κ β) : Formalism.L2.Col.blkDet n κ β c M = dBlk b c M.1 := by
  subst e
  apply Units.ext
  rw [diag_block_det_val c (show M.1 ∈ blockTri (fun i : Fin n => β i.val) from M.2)]
  rfl

theorem blkDet_diagEmb {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin r) κ) (s : ℕ) :
    Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r bl) (s + 1) ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT h bl g⟩ = 1 := by
  apply Units.ext
  rw [Formalism.L2.Col.blkDet_val, Units.val_one]
  refine (congrArg Matrix.det (a₂ := 1) ?_).trans Matrix.det_one
  ext i j
  have hi : ¬ i.1.val < r := fun hi => by
    have h1 := i.2
    rw [Formalism.L2.Col.coarse_of_lt hi] at h1
    omega
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
  rw [Formalism.L2.Col.diagEmb_val, Formalism.L2.Col.diagMat_of_not_left _ _ hi]
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem reindex_refl {n : ℕ} (R : GL (Fin n) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ (finCongr (rfl : n = n))).toMonoidHom R = R := by
  apply Units.ext
  ext i j
  rfl

theorem lamKJ_inv {a n r t m : ℕ} (e : a = n) (hn : n = r + m * t) (hr : r ≤ n) (χ : ℕ → κˣ →* Kˣ)
    (R : GL (Fin a) κ) (g : GL (Fin r) κ) (u : GL (Fin n) κ)
    (hu : u = (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr e)).toMonoidHom R)⁻¹ * Formalism.L2.Col.diagEmb κ hr g)
    (hm : u ∈ Formalism.L2.Col.HKJ κ n r t m) :
    (Formalism.L2.Col.lamKJ χ n r t m)⁻¹ ⟨u, hm⟩ = ∏ s ∈ Finset.range m, χ s (dBlk (blkOf r t) (s + 1) R) := by
  subst e
  rw [reindex_refl] at hu
  have hd := Formalism.L2.Col.diagEmb_mem_blockUT hr (List.replicate m t) g
  have hb := Formalism.L2.Col.HK_le_blockUT _ _ _ _ hm
  have hR : R ∈ Formalism.L2.Col.blockUT a κ r (List.replicate m t) := by
    have : R = Formalism.L2.Col.diagEmb κ hr g * u⁻¹ := by rw [hu]; group
    rw [this]
    exact mul_mem hd (inv_mem hb)
  have e1 : (Subgroup.inclusion (Formalism.L2.Col.HK_le_blockUT a κ r (List.replicate m t)) ⟨u, hm⟩) = (⟨R, hR⟩ : Formalism.L2.Col.blockUT a κ r (List.replicate m t))⁻¹ * ⟨_, hd⟩ :=
    Subtype.ext hu
  rw [MonoidHom.inv_apply, Formalism.L2.Col.lamKJ, Formalism.L2.Col.lamK, MonoidHom.comp_apply, e1, map_mul, map_inv,
    Formalism.L2.Col.detChar_apply, Formalism.L2.Col.detChar_apply, List.length_replicate]
  simp only [blkDet_diagEmb, map_one, Finset.prod_const_one, mul_one, inv_inv]
  exact Finset.prod_congr rfl fun s _ => by rw [blockDeterminant_eq_diagonalBlockDet (coarse_eq_blkOf hn)]

theorem lamQ_inv {a n r b : ℕ} (e : a = n) (hn : n = r + b) (ξ : κˣ →* Kˣ)
    (R : GL (Fin a) κ) (u : GL (Fin n) κ)
    (hu : u = (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr e)).toMonoidHom R)⁻¹ * 1)
    (hm : u ∈ Formalism.L2.Col.HQ κ n r b) :
    (Formalism.L2.Col.lamQ ξ n r b)⁻¹⁻¹ ⟨u, hm⟩ = (ξ (dBlk (blk2 r) 1 R))⁻¹ := by
  subst e
  rw [reindex_refl, mul_one] at hu
  have hR : R ∈ Formalism.L2.Col.HQ κ a r b := by
    have : R = u⁻¹ := by rw [hu, inv_inv]
    rw [this]
    exact inv_mem hm
  have e1 : (⟨u, hm⟩ : Formalism.L2.Col.HQ κ a r b) = (⟨R, hR⟩ : Formalism.L2.Col.HQ κ a r b)⁻¹ := Subtype.ext hu
  rw [inv_inv, e1, map_inv, Formalism.L2.Col.lamQ_apply, blockDeterminant_eq_diagonalBlockDet (coarseBlockIndex_eq_twoBlock hn)]

end Blocks

theorem embLL_chi : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (w : Pl X.B.fields.E) (hw : w ∈ (X.B.primes px).vGs) (s : Fin X.B.R.m) (c : (kP w)ˣ),
      X.toD7.what₂.embLL ((I.Ch.chi s ⟨w, hw⟩ c : X.B.fields.Kˣ) : X.B.fields.K) = ((L.chi ((s : ℕ) + 1) w c : ℂˣ) : ℂ) := by
  intro X px I U L hI hL w hw s c
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : kP w)
  have hy0 : (y : X.B.fields.E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    rw [this, map_zero] at hy
    haveI : Nontrivial (kP w) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
    exact c.ne_zero hy.symm
  have h1 := (hI.ch_tied.mu0 s).atg ⟨w, hw⟩ (Units.mk0 _ hy0) y c rfl hy.symm
  have h2 := hL.is.chi s w (hL.Pg ▸ hw) y (Units.mk0 _ hy0) c rfl hy.symm
  have h3 : L.C.mu0 s = I.C.mu0 s := by rw [hL.C]; rfl
  rw [h3] at h2
  have h4 : (((L.chi ((s : ℕ) + 1) w c)⁻¹ : ℂˣ) : ℂ) = X.B.embLL (((I.Ch.chi s ⟨w, hw⟩ c)⁻¹ : X.B.fields.Kˣ) : X.B.fields.K) :=
    (congrArg Units.val h2).trans h1
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, _root_.inv_inj] at h4
  exact h4.symm

theorem embLL_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (P : Pl X.B.fields.E), P ∈ L.Q t → ∀ (c : (kP P)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) P c : X.B.fields.Kˣ) : X.B.fields.K) =
        ((L.xiR t P c : ℂˣ) : ℂ) := by
  intro X px I U L hI hL t P hP c
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : kP P)
  have hy0 : (y : X.B.fields.E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    rw [this, map_zero] at hy
    haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
    exact c.ne_zero hy.symm
  have hr := hI.xi_reads (ixOf I U t)
  rw [tup_ixOf, ← hL.xiH t] at hr
  have h1 := GlobalTheory.NormOneUnit.resChar_eq hr (hL.is.xi_tame t) P c y (Units.mk0 _ hy0) rfl hy
  have h2 := hL.is.xiR t P hP y (Units.mk0 _ hy0) c rfl hy.symm
  exact h1.trans (congrArg Units.val h2).symm

theorem notMem_vGs : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (P : Pl X.B.fields.E), P ∈ L.Q t → P ∉ (X.B.primes px).vGs := by
  intro X px I U L hI hL t P hP hw
  obtain ⟨k, hk⟩ := (hL.is.Pg P).1 (hL.Pg ▸ hw)
  obtain ⟨⟨p, hp, hc, -, hne⟩, -⟩ := hL.is.Q_pl t P hP
  have h1 : ((X.toD7.host.g k : ℕ) : 𝓞 X.B.fields.E) ∈ P.asIdeal := by
    have h0 := L.C.P.pb_over k
    rw [← show _ = L.C.P.pb k from hk] at h0
    have h2 := Ideal.mem_comap.1 h0
    rwa [map_natCast] at h2
  have h2 : ((p : ℕ) : 𝓞 X.B.fields.E) ∈ P.asIdeal := by
    have h0 := Ideal.absNorm_mem P.asIdeal
    rwa [show Ideal.absNorm P.asIdeal = p from hc] at h0
  have h3 : IsCoprime ((p : ℕ) : 𝓞 X.B.fields.E) ((X.toD7.host.g k : ℕ) : 𝓞 X.B.fields.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp (X.toD7.host.g_prime k)).2 (hne k))
  obtain ⟨a, b, hab⟩ := h3
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)))

theorem prod_uSG {E : Type} [Field E] [NumberField E] {M : Type} [CommMonoid M] {A B : Finset (HeightOneSpectrum (𝓞 E))}
    (hd : ∀ P ∈ B, P ∉ A) (f : Formalism.L2.Col.uSG A B → M) (a b : HeightOneSpectrum (𝓞 E) → M)
    (ha : ∀ w : Formalism.L2.Col.uSG A B, w.1 ∈ A → f w = a w.1) (hb : ∀ w : Formalism.L2.Col.uSG A B, w.1 ∉ A → w.1 ∈ B → f w = b w.1) :
    ∏ w, f w = (∏ w ∈ A, a w) * ∏ w ∈ B, b w := by
  classical
  have h1 : ∏ w, f w = ∏ w : Formalism.L2.Col.uSG A B, (fun P => if P ∈ A then a P else b P) w.1 := by
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases h : w.1 ∈ A
    · simp only [h, if_true]; exact ha w h
    · simp only [h, if_false]; exact hb w h ((Finset.mem_union.mp w.2).resolve_left h)
  rw [h1, Finset.prod_coe_sort (Formalism.L2.Col.uSG A B) (fun P => if P ∈ A then a P else b P)]
  have h2 : Disjoint A B := Finset.disjoint_right.2 fun P hP => hd P hP
  rw [Finset.prod_union h2]
  congr 1
  · exact Finset.prod_congr rfl fun P hP => if_pos hP
  · exact Finset.prod_congr rfl fun P hP => if_neg (hd P hP)

theorem lam_congr {κ K : Type} [CommRing κ] [Field K] {n : ℕ} {l l' : Formalism.L2.Col.Lev κ K n} (e : l = l') (u : GL (Fin n) κ)
    (h : u ∈ l.inv.H) : l.inv.lam ⟨u, h⟩ = l'.lam⁻¹ ⟨u, e ▸ h⟩ := by
  subst e
  rfl

theorem levFn_flagL {D : D7} {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (t : T) (x : GL (Fin D.sp.X'.rank) (Lev.EAf D)) :
    levFn L.βX (flagL (L.datXt t)) x =
      (∏ PP ∈ L.Pg, ∏ c ∈ Finset.range D.R.m, L.chi (c + 1) PP (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn L.βX PP x))) *
        ∏ PP ∈ L.Q t, (L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn L.βX PP x)))⁻¹ := by
  have h2 : ext1 (flagL (L.datXt t)).P.H (flagL (L.datXt t)).P.chi (rTup L.βX (flagL (L.datXt t)) x) = 1 := by
    refine (extendOne_of_mem _ (Subgroup.mem_top _)).trans ?_
    rfl
  unfold levFn
  rw [h2, one_mul]
  rfl

theorem chr_inv_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (hd : ∀ P ∈ Formalism.L2.Col.QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K), P ∉ Pr.vGs)
    {a : ℕ} (e : a = R.N R.m - 1) (M : ∀ P : Pl X.E, GL (Fin a) (kP P)) (g : Formalism.L2.Col.G0 X.E Pr.vGs R.r)
    (z : Formalism.L2.Col.GLG X.E (R.N R.m - 1) (Formalism.L2.Col.rowSG Pr sel mu))
    (hz : ∀ w, z w = Units.map (Matrix.reindexAlgEquiv (kP w.1) (kP w.1) (finCongr e)).toMonoidHom (M w.1))
    (hu : z⁻¹ * Formalism.L2.Col.unipotentGroupBlockEmbedding Pr sel mu (Formalism.L2.Col.r_le_X' R) g ∈ ((Formalism.L2.Col.rowTyKK Ch sel mu).inv).grp)
    (σ : X.Kˣ →* ℂˣ) (χ : ℕ → ∀ P : Pl X.E, (kP P)ˣ →* ℂˣ) (ξ : ∀ P : Pl X.E, (kP P)ˣ →* ℂˣ)
    (hχ : ∀ w (hw : w ∈ Pr.vGs) (s : Fin R.m) c, σ (Ch.chi s ⟨w, hw⟩ c) = χ ((s : ℕ) + 1) w c)
    (hξ : ∀ P ∈ Formalism.L2.Col.QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K), ∀ c,
      σ (resChar (mu : Formalism.L2.DIV.Chr X.F X.E X.K) P c) = ξ P c) :
    σ ((Formalism.L2.Col.rowTyKK Ch sel mu).inv.chr ⟨_, hu⟩) =
      (∏ PP ∈ Pr.vGs, ∏ c ∈ Finset.range R.m, χ (c + 1) PP (dBlk (blkOf R.r R.t) (c + 1) (M PP))) *
        ∏ PP ∈ Formalism.L2.Col.QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K), (ξ PP (dBlk (blk2 R.r) 1 (M PP)))⁻¹ := by
  have hn := Formalism.L2.Col.rank_X'_eq R
  rw [Formalism.L2.Col.LevFam.chr_apply, map_prod]
  refine prod_uSG hd _ _ _ (fun w hw => ?_) (fun w hw hw' => ?_)
  · have e' := Formalism.L2.Col.LevFam.glue_of_mem (Formalism.L2.Col.rowTyK (R := R) Ch)
      (Formalism.L2.Col.rowTyQ R (mu : Formalism.L2.DIV.Chr X.F X.E X.K) _) w hw
    refine (congrArg σ ((lam_congr e' _ _).trans (lamKJ_inv e hn (Formalism.L2.Col.r_le_X' R) _
      (M w.1) (g ⟨w.1, hw⟩) _ ?_ _))).trans ?_
    · show (z w)⁻¹ * Formalism.L2.Col.extGLG _ _ w = _
      rw [Formalism.L2.Col.extGLG_of_mem _ w hw, hz w]
      rfl
    · rw [map_prod]
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' := Finset.mem_range.1 hs
      rw [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi, dif_pos hs']
      exact hχ w.1 hw ⟨s, hs'⟩ _
  · have e' := Formalism.L2.Col.LevFam.glue_of_not (Formalism.L2.Col.rowTyK (R := R) Ch)
      (Formalism.L2.Col.rowTyQ R (mu : Formalism.L2.DIV.Chr X.F X.E X.K) _) w hw
    refine (congrArg σ ((lam_congr e' _ _).trans (lamQ_inv e hn _ (M w.1) _ ?_ _))).trans ?_
    · show (z w)⁻¹ * Formalism.L2.Col.extGLG _ _ w = _
      rw [Formalism.L2.Col.extGLG_of_not _ w hw, hz w]
    · rw [map_inv, hξ w.1 hw']

theorem ch_eq {D : D7} {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (t : T) (q : (levEnv D.sp.X' L.βX (L.datXt t)).Q)
    {A B : Finset (Pl D.host.E)} (hA : L.Pg = A) (hB : L.Q t = B) :
    (levEnv D.sp.X' L.βX (L.datXt t)).ch q =
      (∏ PP ∈ A, ∏ c ∈ Finset.range D.R.m, L.chi (c + 1) PP (dBlk (blkOf D.R.r D.R.t) (c + 1)
        (redFn L.βX PP (Formalism.UG.bc (swapAE D) q.1.1)))) *
        ∏ PP ∈ B, (L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn L.βX PP (Formalism.UG.bc (swapAE D) q.1.1))))⁻¹ := by
  subst hA hB
  exact levFn_flagL L t _

theorem emb_of_map (X : Stages) {x : X.B.fields.Kˣ} {y : ℂˣ}
    (h : Units.map (X.B.embLL : X.B.fields.K →+* ℂ).toMonoidHom x = y) :
    X.toD7.what₂.embLL (x : X.B.fields.K) = (y : ℂ) := congrArg Units.val h

theorem chr_eq_ch : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
      (hu : (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp),
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr ⟨_, hu⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG t q hz hu
  have hQ : L.Q t = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
    rw [hL.Q t, ColIn.Q, tup_ixOf]
  have h1 := chr_inv_eq I.Ch I.sel t.1 (fun P hP => notMem_vGs X px I U L hI hL t P (hQ ▸ hP)) (RowAd.rank_X' X)
    (fun P => redFn L.βX P (Formalism.UG.bc (swapAE X.toD7) q.1.1)) _ _
    (RowDeco.redG_ptE X I L hL t q hz) hu (Units.map (X.B.embLL : X.B.fields.K →+* ℂ).toMonoidHom) L.chi (L.xiR t)
    (fun w hw s c => Units.ext (embLL_chi X px I U L hI hL w hw s c))
    (fun P hP c => Units.ext (embLL_resChar X px I U L hI hL t P (hQ ▸ hP) c))
  exact emb_of_map X (h1.trans (ch_eq L t q hL.Pg hQ).symm)

end GlobalTheory.Mem.R3.RowChr
