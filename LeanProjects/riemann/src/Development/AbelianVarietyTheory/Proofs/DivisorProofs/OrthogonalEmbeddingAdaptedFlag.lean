import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmatrixSchurComplementCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHeightPairingPullbackDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest GlobalTheory.TwoLat GlobalTheory.OrthFilt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.Twist (resM app_resM)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.OrthBcSum

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem bcForm_eq_of_family {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
    (H : h.IsCInf) (a : AdaptedChart S r s) {U : X.Opens} (f : Fin r ⊕ Fin s → Γ(S.X₂, U))
    (hf : ∀ j, ∃ t, S.f.app U t = f (.inl j)) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U) (ha : y ∈ ptsIn p σ a.U) (hd : (h.gram f y).det ≠ 0) :
    extTrace (fun v => h.gram f (c.e.symm v)) (c.e y) = h.bcForm a c y := by
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ a.U))).mem_nhds
    (ChartGlue.mem_over c.e hy (mem_ptsIn_inf.2 ⟨hU, ha⟩))
  let A : CxPts p σ → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun z =>
    Matrix.of fun i j => (a.mid hS).crd p σ (f j) z (finSumFinEquiv i)
  have hA : MInfAt A y := fun i j => (a.mid hS).vInfAt_crd _ hU ha _
  have hG (z : CxPts p σ) (hz : z ∈ ptsIn p σ U) (hz' : z ∈ ptsIn p σ a.U) :
      h.gram f z = chg (A z) (h.gram a.frame z) := by
    rw [h.gram_eq (a.mid hS) hz' _ hz, h.gram_frame hS a hz']
    exact (chg_submatrix (Matrix.of fun i j => (a.mid hS).crd p σ (f j) z i) _ finSumFinEquiv id).symm
  rw [extTrace_congr (K' := fun v => chg (A (c.e.symm v)) (h.gram a.frame (c.e.symm v)))
    (eventually_of_mem hm fun v hv => hG _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2)]
  refine extTrace_chg (((H.gram _ ha).mContDiffAt c hy).of_le (by norm_cast))
    (h.eventually_posDef hS a c hy ha) ((hA.mContDiffAt c hy).of_le (by norm_cast)) ?_
    (fun η => Matrix.ext fun i j => ?_) (eventually_of_mem hm fun v hv => ?_)
  · rw [c.e.left_inv hy]
    rw [hG y hU ha, det_chg] at hd
    refine Ne.isUnit fun e => hd ?_
    simp [e]
  · exact congr($(dbar_eq_zero (c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨hU, ha⟩))) η)
  · obtain ⟨hz, hz'⟩ := mem_ptsIn_inf.1 hv.2
    ext i j
    obtain ⟨t, e⟩ := hf j
    change (a.mid hS).crd p σ (f (.inl j)) _ (finSumFinEquiv (.inr i)) = 0
    rw [← e, (a.mid hS).crd_app a.sub S.f _ hz hz']
    simp only [mulVec, dotProduct, of_apply]
    refine Finset.sum_eq_zero fun b _ => mul_eq_zero_of_left ?_ _
    exact (a.crd_frame hS hz' (.inr i) (.inl b)).trans (by simp)

section Flag

variable {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r)

theorem exists_incl {i j : Fin (r + 1)} (hij : i ≤ j) : ∃ t : fl.F i ⟶ fl.F j, t ≫ fl.ι j = fl.ι i := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le _)
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ j ih =>
    rcases hij.eq_or_lt with rfl | hlt
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 hlt)
      exact ⟨t ≫ fl.step j, by rw [Category.assoc, fl.step_ι, ht]⟩

theorem exists_app_of_le {U : X.Opens} {i j : Fin (r + 1)} (hij : i ≤ j) (s : Γ(fl.F i, U)) :
    ∃ t : Γ(fl.F j, U), (fl.ι j).app U t = (fl.ι i).app U s := by
  obtain ⟨t, ht⟩ := exists_incl fl hij
  exact ⟨t.app U s, congr(($ht).app U s)⟩

theorem exists_frame_step (x : X) (n : Fin (r + 1)) :
    ∃ (U : X.Opens) (u : Fin n → Γ(fl.F n, U)), x ∈ U ∧ IsFrame u ∧
      ∀ (j : Fin n) (m : Fin (r + 1)), (j : ℕ) < m → ∃ t : Γ(fl.F m, U), (fl.ι m).app U t = (fl.ι n).app U (u j) := by
  induction n using Fin.induction with
  | zero =>
    obtain ⟨U, u, hx, hu⟩ := fl.isVB 0 x
    exact ⟨U, u, hx, hu, fun j => j.elim0⟩
  | succ n ih =>
    obtain ⟨U, u, hx, hu, hs⟩ := ih
    obtain ⟨a, ha⟩ := VBExt.exists_adaptedChart (VMetric.stepSeq_shortExact fl n) (fl.isVB n.castSucc)
      (fl.isVB_gr n) x
    have hf := VBExt.isFrame_sumElim (VMetric.stepSeq_shortExact fl n) (hu.res (inf_le_left (b := a.U)))
      (t := fun j => resM _ inf_le_right (a.t j)) (by
        simp only [app_resM]
        exact a.ht.res inf_le_right)
    refine ⟨U ⊓ a.U, _, ⟨hx, ha⟩, hf.comp_equiv (finSumFinEquiv (m := n) (n := 1)).symm, fun j m hm => ?_⟩
    obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := n) (n := 1)).surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases j with j | j
    · obtain ⟨t, ht⟩ := hs j m hm
      refine ⟨resM _ inf_le_left t, ?_⟩
      rw [app_resM, ht, ← app_resM]
      exact congr(($(fl.step_ι n)).app _ _).symm
    · refine exists_app_of_le fl ?_ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact hm

theorem exists_frame (x : X) :
    ∃ (U : X.Opens) (u : Fin r → Γ(E, U)), x ∈ U ∧ IsFrame u ∧
      ∀ (j : Fin r) (m : Fin (r + 1)), (j : ℕ) < m → ∃ t : Γ(fl.F m, U), (fl.ι m).app U t = u j := by
  obtain ⟨U, u, hx, hu, hs⟩ := exists_frame_step fl x (Fin.last r)
  exact ⟨U, _, hx, hu.map_iso (fl.ι _), hs⟩

theorem emb_injective {m : ℕ} (i : Fin m) : Function.Injective (emb i) := by
  rintro (a | a) (b | b) h
  · exact congrArg _ (Fin.castLE_injective i.isLt.le h)
  · exact absurd (congrArg Fin.val h) a.isLt.ne
  · exact absurd (congrArg Fin.val h) b.isLt.ne'
  · exact congrArg _ (Subsingleton.elim _ _)

theorem bcMat_step {h : VMetric p E r} (H : h.IsCInf) (i : Fin r) {U : X.Opens} (u : Fin r → Γ(E, U))
    (hu : ∀ (j : Fin r) (m : Fin (r + 1)), (j : ℕ) < m → ∃ t : Γ(fl.F m, U), (fl.ι m).app U t = u j)
    {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U)
    (hp : ((h.met σ).gram u y).PosDef) :
    bcMat ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) c y =
      formMat (extTrace (fun v => ((h.met σ).gram u (c.e.symm v)).submatrix (emb i) (emb i)) (c.e y)) := by
  choose t ht using hu
  let f : Fin i ⊕ Fin 1 → Γ(fl.F i.succ, U) :=
    Sum.elim (fun j => (fl.step i).app U (t (emb i (.inl j)) i.castSucc j.isLt)) fun j =>
      t (emb i (.inr j)) i.succ (Nat.lt_succ_self _)
  have hf (x) : (fl.ι i.succ).app U (f x) = u (emb i x) := by
    rcases x with j | j
    · exact Eq.trans congr(($(fl.step_ι i)).app U _) (ht _ _ _)
    · exact ht _ _ _
  have hG (z) (hz : z ∈ ptsIn p σ U) :
      ((h.stepMet fl i).met σ).gram f z = ((h.met σ).gram u z).submatrix (emb i) (emb i) := by
    ext a b
    refine ((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hz).trans ?_
    rw [hf, hf]
    rfl
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (ChartGlue.mem_over c.e hy hU)
  rw [bcMat, ← bcForm_eq_of_family (S := VMetric.stepSeq fl i) (r := i) (s := 1)
    (h := (h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i)
    (H.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) σ) _ f (fun j => ⟨_, rfl⟩) c hy hU
    (Met.exists_adapted (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) y).choose_spec
    (by rw [hG y hU]; exact (hp.submatrix (emb_injective i)).det_pos.ne')]
  exact congrArg formMat (extTrace_congr (eventually_of_mem hm fun v hv => hG _ hv.2))

end Flag

section Matrices

variable {ι : Type} {r : ι → ℕ} {g : ℕ} (e : (Σ a, Fin (r a)) ≃ Fin g)

theorem extTrace_block (he : ∀ a, StrictMono fun i : Fin (r a) => e ⟨a, i⟩) {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] (K : W → Matrix (Fin g) (Fin g) ℂ)
    (G : ∀ a, W → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : W)
    (hK : ∀ᶠ v in 𝓝 z, (K v).PosDef ∧ (K v).submatrix e e = blockDiagonal' fun a => G a v) (a : ι) (i : Fin (r a)) :
    extTrace (fun v => (K v).submatrix (emb (e ⟨a, i⟩)) (emb (e ⟨a, i⟩))) z =
      extTrace (fun v => (G a v).submatrix (emb i) (emb i)) z := by
  let φ : Fin i → Fin (e ⟨a, i⟩) := fun j => ⟨e ⟨a, emb i (.inl j)⟩, he a (show emb i (.inl j) < i from j.isLt)⟩
  have hφ : Function.Injective φ := fun j j' h =>
    Sum.inl_injective (emb_injective i ((he a).injective (Fin.ext (Fin.ext_iff.1 h :))))
  let ε : Fin i ⊕ ((Set.range φ)ᶜ : Set _) ≃ Fin (e ⟨a, i⟩) :=
    (Equiv.sumCongr (Equiv.ofInjective φ hφ) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  have h₁ (x : Fin i ⊕ Fin 1) : emb (e ⟨a, i⟩) (Sum.map (fun j => ε (.inl j)) id x) = e ⟨a, emb i x⟩ := by
    rcases x with j | j <;> rfl
  have h₂ (b : ((Set.range φ)ᶜ : Set _)) :
      ∃ a' j, a' ≠ a ∧ emb (e ⟨a, i⟩) (.inl (ε (.inr b))) = e ⟨a', j⟩ := by
    obtain ⟨⟨a', j⟩, hj⟩ := e.surjective (emb (e ⟨a, i⟩) (.inl b.1))
    refine ⟨a', j, ?_, hj.symm⟩
    rintro rfl
    have hlt : j < i := (he a').lt_iff_lt.1 (hj ▸ b.1.isLt : e ⟨a', j⟩ < e ⟨a', i⟩)
    exact b.2 ⟨⟨j, hlt⟩, Fin.ext (Fin.ext_iff.1 hj :)⟩
  refine (quotGram_extTrace_of_orthogonal_summand W _ _ _ _ ε).2 _ _ z (hK.mono fun v ⟨hp, hv⟩ => ⟨?_, ?_, ?_⟩)
  · ext x x'
    simp only [submatrix_apply, h₁]
    exact (congrFun (congrFun hv ⟨a, _⟩) ⟨a, _⟩).trans (blockDiagonal'_apply_eq _ _ _ _)
  · intro x b
    obtain ⟨a', j, ha, hb⟩ := h₂ b
    simp only [submatrix_apply, h₁, hb]
    exact ⟨(congrFun (congrFun hv ⟨a, _⟩) ⟨a', _⟩).trans (blockDiagonal'_apply_ne _ _ _ ha.symm),
      (congrFun (congrFun hv ⟨a', _⟩) ⟨a, _⟩).trans (blockDiagonal'_apply_ne _ _ _ ha)⟩
  · exact (posDef_subGram (hp.submatrix (emb_injective _))).det_pos.ne'.isUnit

end Matrices

section Orth

variable {ι : Type} {L : X.Modules} {g : ℕ} {hL : VMetric p L g} {E : ι → X.Modules} {r : ι → ℕ}
  {h : ∀ a, VMetric p (E a) (r a)} {T : ∀ a, E a ⟶ L} {fl : ∀ a, Vert.Flag (E a) (r a)} {w : Vert.Flag L g}
  {e : (Σ a, Fin (r a)) ≃ Fin g}

theorem flagMat_eq_sum [Fintype ι] (HL : hL.IsCInf) (H : ∀ a, (h a).IsCInf) (hT : OrthEmb hL h T)
    (hw : Adapted T fl w e) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    flagMat hL w σ c y = ∑ a, flagMat (h a) (fl a) σ c y := by
  choose V u₀ hV hu₀ hs₀ using fun a => exists_frame (fl a) (y.1 (IsLocalRing.closedPoint ℂ))
  let U : X.Opens := Finset.univ.inf V
  have hle (a) : U ≤ V a := Finset.inf_le (Finset.mem_univ a)
  have hU : y ∈ ptsIn p σ U := by
    refine mem_ptsIn.2 ?_
    change _ ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    exact Set.mem_iInter₂.2 fun a _ => hV a
  let u (a) (j : Fin (r a)) : Γ(E a, U) := resM _ (hle a) (u₀ a j)
  have hu (a) : IsFrame (u a) := (hu₀ a).res (hle a)
  have hs (a) (j : Fin (r a)) (m : Fin (r a + 1)) (hm : (j : ℕ) < m) :
      ∃ t : Γ((fl a).F m, U), ((fl a).ι m).app U t = u a j := by
    obtain ⟨t, ht⟩ := hs₀ a j m hm
    exact ⟨resM _ (hle a) t, by rw [app_resM, ht]⟩
  have hp (a) (z) (hz : z ∈ ptsIn p σ U) : (((h a).met σ).gram (u a) z).PosDef := by
    convert ((h a).met σ).posDef ⟨U, u a, hu a⟩ z hz using 1
    ext i j
    exact ((h a).met σ).form_frame ⟨U, u a, hu a⟩ hz i j
  let b (n : Fin g) : Γ(L, U) := (T (e.symm n).1).app U (u _ (e.symm n).2)
  have hb (z : Σ a, Fin (r a)) : b (e z) = (T z.1).app U (u _ z.2) :=
    congrArg (fun z : Σ a, Fin (r a) => (T z.1).app U (u _ z.2)) (e.symm_apply_apply z)
  have hG (z) (hz : z ∈ ptsIn p σ U) :
      ((hL.met σ).gram b z).submatrix e e = blockDiagonal' fun a => ((h a).met σ).gram (u a) z := by
    ext ⟨a, i⟩ ⟨a', j⟩
    change (hL.met σ).form (b _) (b _) z = _
    rw [hb, hb]
    by_cases ha : a = a'
    · subst ha
      rw [blockDiagonal'_apply_eq]
      exact hT.1 a σ U _ _ z hz
    · exact (hT.2 a a' ha σ U _ _ z hz).trans (blockDiagonal'_apply_ne _ _ _ ha).symm
  have hP (z) (hz : z ∈ ptsIn p σ U) : ((hL.met σ).gram b z).PosDef := by
    have := (posDef_blockDiagonal' fun a => hp a z hz).submatrix e.symm.injective
    rwa [← hG z hz, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
  have hbs (n : Fin g) (m : Fin (g + 1)) (hm : (n : ℕ) < m) : ∃ t : Γ(w.F m, U), (w.ι m).app U t = b n := by
    obtain ⟨z, rfl⟩ := e.surjective n
    obtain ⟨t, ht⟩ := hs z.1 z.2 z.2.succ (Nat.lt_succ_self _)
    obtain ⟨t', ht'⟩ := hw.2 z
    obtain ⟨s, hs'⟩ := exists_app_of_le w (show (e z).succ ≤ m from hm) (t'.app U t)
    refine ⟨s, hs'.trans ?_⟩
    rw [hb, ← ht]
    exact congr(($ht').app U t)
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (ChartGlue.mem_over c.e hy hU)
  simp only [flagMat]
  rw [← e.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [bcMat_step w HL _ b hbs c hy hU (hP y hU), bcMat_step (fl a) (H a) i (u a) (hs a) c hy hU (hp a y hU)]
  exact congrArg formMat (extTrace_block e hw.1 _ (fun a v => ((h a).met σ).gram (u a) (c.e.symm v)) _
    (eventually_of_mem hm fun v hv => ⟨hP _ hv.2, hG _ hv.2⟩) a i)

theorem bcPair_eq_sum_of_genSmooth [Fintype ι] (HL : hL.IsCInf) (H : ∀ a, (h a).IsCInf) (hT : OrthEmb hL h T)
    (hw : Adapted T fl w e) {d : ℕ} (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1)) (N : HermLB p) :
    bcPair hL w N d = ∑ a, bcPair (h a) (fl a) N d := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcPair, finsum_eq_sum_of_fintype]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := FlagCmp.total_sum hX (hG σ) (fun _ => 1) fun a => FlagCmp.isDens_flagDens (H a) (fl a) N d σ
  simp only [one_mul] at key
  refine (total_congr fun c y hy => ?_).trans key
  rw [flagDens, flagMat_eq_sum HL H hT hw c hy, mix_sum]
  rfl

theorem form_app_eq_zero {F F' : X.Modules} {s s' : ℕ} (m : Met p σ L g) {u : F ⟶ L} {u' : F' ⟶ L} {U : X.Opens}
    {f : Fin s → Γ(F, U)} {f' : Fin s' → Γ(F', U)} (hf : IsFrame f) (hf' : IsFrame f') {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (h₀ : ∀ i j, m.form (u.app U (f i)) (u'.app U (f' j)) y = 0)
    {V : X.Opens} (t : Γ(F, V)) (t' : Γ(F', V)) (hy : y ∈ ptsIn p σ V) : m.form (u.app V t) (u'.app V t') y = 0 := by
  have hc := m.isVB.mem_pick y
  simp only [m.form_eq _ hc _ _ hU] at h₀
  rw [m.form_eq _ hc _ _ hy, Chart.crd_app _ ⟨U, f, hf⟩ u t hy hU, Chart.crd_app _ ⟨U, f', hf'⟩ u' t' hy hU]
  generalize (Chart.crd p σ ⟨U, f, hf⟩ t y) = v
  generalize (Chart.crd p σ ⟨U, f', hf'⟩ t' y) = v'
  set A : Matrix (Fin g) (Fin s) ℂ := Matrix.of fun a b => (m.isVB.pick y).crd p σ (u.app U (f b)) y a
  set B : Matrix (Fin g) (Fin s') ℂ := Matrix.of fun a b => (m.isVB.pick y).crd p σ (u'.app U (f' b)) y a
  have hAB : Aᵀ * m.G (m.isVB.pick y) y * Bᴴᵀ = 0 := by
    ext i j
    refine Eq.trans ?_ (h₀ i j)
    rw [Matrix.mul_assoc]
    rfl
  change HermFrame.form _ (A *ᵥ v) (B *ᵥ v') = 0
  rw [HermFrame.form, star_mulVec, ← mulVec_transpose, mulVec_mulVec, dotProduct_comm, dotProduct_mulVec,
    ← mulVec_transpose, mulVec_mulVec, ← Matrix.mul_assoc, hAB]
  simp

variable {Y : Scheme.{0}} {q : Y ⟶ Sp k}

theorem orthEmb_pull (hT : OrthEmb hL h T) (π : Y ⟶ X) (v : π ≫ p = q) :
    OrthEmb (hL.pull π v) (fun a => (h a).pull π v) fun a => (Scheme.Modules.pullback π).map (T a) := by
  refine ⟨fun a σ V s t z hz => ?_, fun a b hab σ V s t z hz => ?_⟩
  · have hc := ((h a).met σ).isVB.mem_pick (PtsOver.map π v _ z)
    refine form_app_of_gram (Chart.pull _ ((h a).met σ).isVB π) hc ?_ s t hz
    refine Eq.trans ?_ (((h a).met σ).pull_G π v _ hc).symm
    ext i j
    rw [← ((h a).met σ).form_frame _ hc, ← hT.1 a σ _ _ _ _ hc, ← (hL.met σ).form_pull π v _ _ le_rfl hc,
      ← QCoh.pullback_map_app_pullbackSections, ← QCoh.pullback_map_app_pullbackSections]
    rfl
  · have hc := ((h a).met σ).isVB.mem_pick (PtsOver.map π v _ z)
    have hc' := ((h b).met σ).isVB.mem_pick (PtsOver.map π v _ z)
    have hU := mem_ptsIn_inf.2 ⟨hc, hc'⟩
    let c₁ : Chart (E a) (r a) := ⟨_, _, (((h a).met σ).isVB.pick (PtsOver.map π v _ z)).isFrame.res
      (inf_le_left (b := (((h b).met σ).isVB.pick (PtsOver.map π v _ z)).U))⟩
    let c₂ : Chart (E b) (r b) := ⟨_, _, (((h b).met σ).isVB.pick (PtsOver.map π v _ z)).isFrame.res
      (inf_le_right (a := (((h a).met σ).isVB.pick (PtsOver.map π v _ z)).U))⟩
    refine form_app_eq_zero _ (c₁.pull ((h a).met σ).isVB π).isFrame (c₂.pull ((h b).met σ).isVB π).isFrame hU
      (fun i j => ?_) s t hz
    rw [← hT.2 a b hab σ _ (c₁.e i) (c₂.e j) _ hU, ← (hL.met σ).form_pull π v _ _ le_rfl hU,
      ← QCoh.pullback_map_app_pullbackSections, ← QCoh.pullback_map_app_pullbackSections]
    rfl

theorem adapted_pull (hw : Adapted T fl w e) (π : Y ⟶ X) :
    Adapted (fun a => (Scheme.Modules.pullback π).map (T a)) (fun a => (fl a).pull π) (w.pull π) e := by
  refine ⟨hw.1, fun z => ?_⟩
  obtain ⟨t, ht⟩ := hw.2 z
  exact ⟨(Scheme.Modules.pullback π).map t, ((Functor.map_comp _ _ _).symm.trans (congrArg _ ht)).trans
    (Functor.map_comp _ _ _)⟩

theorem bcPair_eq_sum_of_isArithVar (hP : Published.Principalisation) [IsIntegral X] [Fintype ι] (HL : hL.IsCInf)
    (H : ∀ a, (h a).IsCInf) (hT : OrthEmb hL h T) (hw : Adapted T fl w e) {d : ℕ} (hX : IsArithVar p (d + 1))
    (N : HermLB p) : bcPair hL w N d = ∑ a, bcPair (h a) (fl a) N d := by
  obtain ⟨Z, ρ, _, hρ, hG⟩ := GenSmoothCover.exists_isCov_genSmooth hP k X p (d + 1) hX
  have key := bcPair_eq_sum_of_genSmooth (HL.pull ρ rfl) (fun a => (H a).pull ρ rfl) (orthEmb_pull hT ρ rfl)
    (adapted_pull hw ρ) hρ.1 hG (N.pull ρ rfl)
  rw [MixDensPull.bcPair_pull k X Z p d ρ hX hρ L g hL HL w N, Finset.sum_congr rfl fun a _ =>
    MixDensPull.bcPair_pull k X Z p d ρ hX hρ (E a) (r a) (h a) (H a) (fl a) N, ← Finset.mul_sum] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hρ.2.2) key

end Orth

theorem bcPair_pull_eq_sum : Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (ι : Type) [Fintype ι] (L : X.Modules) (g : ℕ) (hL : VMetric p L g), hL.IsCInf → ∀ (E : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)), (∀ a, (h a).IsCInf) → ∀ (T : ∀ a, E a ⟶ L) (fl : ∀ a, Vert.Flag (E a) (r a)) (w : Vert.Flag L g) (e : (Σ a, Fin (r a)) ≃ Fin g), OrthEmb hL h T → Adapted T fl w e → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (τ : Y ⟶ X) (v : τ ≫ p = q) (d : ℕ), IsArithVar q (d + 1) → ∀ N : HermLB q, bcPair (hL.pull τ v) (w.pull τ) N d = ∑ a, bcPair ((h a).pull τ v) ((fl a).pull τ) N d :=
  fun hP _ _ _ _ _ _ _ _ _ HL _ _ _ H _ _ _ _ hT hw _ _ _ τ v _ hY N =>
    bcPair_eq_sum_of_isArithVar hP (HL.pull τ v) (fun a => (H a).pull τ v) (orthEmb_pull hT τ v) (adapted_pull hw τ) hY N

end GlobalTheory.OrthBcSum

end
