import Formalism.HermitianCurvature.StatementJC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameIntegralJacobian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem concrete_data_instance : Formalism.FourierDecayAlt.JC.MkDataInst := by
  intro E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th e
  unfold J.Inst J.PlacesOf
  exact ⟨rfl, rfl, fun _ _ => rfl, S.hv, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem concrete_sizes_of_parts : Formalism.FourierDecayAlt.JC.SizesConcreteOfParts := by
  intro hLSJ hIS hBox hLG hIM hNI hDF hFP hX hILS hMk
  obtain ⟨C₁, hC₁, h⟩ := hILS hLSJ hIS hBox hLG hIM hNI hDF hFP hX
  refine ⟨C₁, hC₁, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th e Θ hU hg1 hg2 hCA hlen hΘ hgr
  have hI := hMk E Wp Wq S Kr hK0 Th e
  obtain ⟨h1, h2⟩ := h E _ (S.mkData Kr hK0 Th e) S.pl S.G S.CA S.de S.de' S.T S.T' S.l Θ hU hI hg1 hg2
    hCA hlen hΘ hgr
  refine ⟨h1, ?_⟩
  have hK : (S.mkData Kr hK0 Th e).K = 5 := hI.2.1
  rw [hK] at h2
  exact h2

theorem concrete_axioms : Formalism.FourierDecayAlt.JC.AxiomsConcrete := by
  intro hAx hLC hA13 E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th hLM
  exact hAx hLC hA13 E _ (S.mkData Kr hK0 Th fun _ => 0) hLM

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.JCx1

open NumberField

theorem norm_σ {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (t : E) : ‖S.σ v t‖ = S.pl v t := by
  show ‖S.emb v t‖ = S.pl v t
  rw [← S.hemb v, NumberField.InfinitePlace.apply]

end Formalism.FourierDecayAlt.P.JCx1

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

private theorem setOf_threshold_values_finite (N : ℕ) (a : ℝ) (b d : ℕ → ℝ) (c : ℕ → ℕ → ℝ) :
    {x : ℝ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧ ((i = 1 ∧ x = a) ∨ (2 ≤ i ∧ x = b i) ∨
      (∃ s : ℕ, 2 ≤ s ∧ s + i ≤ N + 1 ∧ x = c i s) ∨ x = d i)}.Finite := by
  apply Set.Finite.subset (((Set.finite_Iic N).image b).union
    ((((Set.finite_Iic N).prod (Set.finite_Iic (N + 1))).image (fun q : ℕ × ℕ => c q.1 q.2)).union
      ((Set.finite_Iic N).image d)) |>.insert a)
  rintro x ⟨i, hi1, hiN, h | h | ⟨s, hs2, hsi, h⟩ | h⟩
  · rw [h.2]
    exact Set.mem_insert _ _
  · rw [h.2]
    exact Set.mem_insert_of_mem _ (Set.mem_union_left _ (Set.mem_image_of_mem b (Set.mem_Iic.2 hiN)))
  · rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (Set.mem_union_left _
      (Set.mem_image_of_mem (fun q : ℕ × ℕ => c q.1 q.2)
        (Set.mk_mem_prod (Set.mem_Iic.2 hiN) (Set.mem_Iic.2 (by omega))))))
  · rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (Set.mem_union_right _
      (Set.mem_image_of_mem d (Set.mem_Iic.2 hiN))))

theorem jc_theta_exists_variant : Formalism.FourierDecayAlt.JC.ThetaExistence₂ := by
  intro ι _ G C de de' T T' l hf hpos
  have hfin : (G.thrSet C de de' T T' l).Finite := setOf_threshold_values_finite _ _ _ _ _
  have hne : (G.thrSet C de de' T T' l).Nonempty := by
    unfold Set.Nonempty Sz.Glob.thrSet
    simp only [Set.mem_setOf_eq]
    exact ⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩
  have hmem := hne.csSup_mem hfin
  have hgr : IsGreatest (G.thrSet C de de' T T' l) (sSup (G.thrSet C de de' T T' l)) :=
    ⟨hmem, fun x hx => le_csSup hfin.bddAbove hx⟩
  have hm0 : 0 < sSup (G.thrSet C de de' T T' l) := hpos _ hmem
  have hf0 : (G.f : ℝ) ≠ 0 := by exact_mod_cast (by omega : G.f ≠ 0)
  refine ⟨sSup (G.thrSet C de de' T T' l) ^ (-(1 / (G.f : ℝ))), Real.rpow_pos_of_pos hm0 _, ?_⟩
  have e : ((sSup (G.thrSet C de de' T T' l) ^ (-(1 / (G.f : ℝ)))) ^ G.f)⁻¹ = sSup (G.thrSet C de de' T T' l) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, neg_mul, one_div_mul_cancel hf0, Real.rpow_neg_one, inv_inv]
  rw [e]
  exact hgr

end Formalism.FourierDecayAlt.P

section cutf

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.JCx1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_entry {k r : ℕ} (i j : Fin (2 * r + k + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => g i j) := by
  exact contDiff_apply_apply ℝ ℂ i j

theorem contDiff_det {n : Type} [Fintype n] [DecidableEq n] {k r : ℕ} (M : B.Mat k r → Matrix n n ℂ)
    (hM : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun g => M g a b)) : ContDiff ℝ (⊤ : ℕ∞) (fun g => (M g).det) := by
  have hdet : (fun g => (M g).det) = fun g => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i := by
    funext g
    exact Matrix.det_apply' (M g)
  rw [hdet]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

theorem contDiff_Zhat {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Zhat k r z z' g a b) := by
  unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Matrix.mulVec]
  exact ContDiff.sum fun i _ => contDiff_const.mul (ContDiff.sum fun j _ => contDiff_const.mul
    (ContDiff.sum fun l _ => (contDiff_entry j l).mul contDiff_const))

theorem contDiff_Dmin {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) := by
  unfold Formalism.QuantumDeterminants.Dmin
  exact contDiff_det _ fun a b => contDiff_Zhat z z' _ _

theorem contDiff_normSq : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => Complex.normSq c) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => c.re) := Complex.reCLM.contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => c.im) := Complex.imCLM.contDiff
  have e : (fun c : ℂ => Complex.normSq c) = fun c => c.re * c.re + c.im * c.im :=
    funext Complex.normSq_apply
  rw [e]
  exact (h1.mul h1).add (h2.mul h2)

theorem contDiff_Gf {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Gf k r z z' g) := by
  unfold Formalism.QuantumDeterminants.Gf
  exact (contDiff_normSq.comp (contDiff_Dmin z z' _)).sub
    (contDiff_const.mul (contDiff_normSq.comp (contDiff_Dmin z z' _)))

end Formalism.FourierDecayAlt.P.JCx1

namespace Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutoff_smooth : Formalism.FourierDecayAlt.JC.CutFSmooth := by
  intro k r Wp Wq _ _ _ _ Bs χ f ε hχ hf hε g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hff'⟩ := hf g₀ hg₀
  refine ⟨U, fun g => ((χ (Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • f' g, hU, hg₀U, ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g : B.Mat k r => ((χ (Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hχ.1.comp ((JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))
    exact h1.contDiffOn.smul hf'
  · intro g hgU hgV
    simp only [D.cutF, hff' g hgU hgV]

end Formalism.FourierDecayAlt.P

end cutf

section lemE

open Formalism.FourierDecayAlt Filter Topology

namespace Formalism.FourierDecayAlt.P

theorem lemma_E_of_model : Formalism.FourierDecayAlt.JC.LemmaEOfModel := by
  intro hE hLZ hGA hM
  obtain ⟨C₂, C₆, _hC₂, hC₆, hMod⟩ := hM
  refine ⟨C₆, hC₆, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ hB hsm hcut hmod
  refine hE hLZ hGA E Wp Wq S T f χ ν' m₀ top A₀ _ hB hsm (fun w v => ?_)
  obtain ⟨_hχ, _hCm, hσ, hSet, hDec, hAdj, hEig, hRR, hSys⟩ := hmod v
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  obtain ⟨hA, hsz⟩ := hSys (C₂ * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2) (w.1 v) hadm
  have hlen : (w.1 v).length ≤ S.Ntop :=
    le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2
  have hN : S.G.r + 1 ≤ S.Ntop := by
    simp only [C.HidaSetting.Ntop, C.Kst]; omega
  have hT := hMod (D.parOf S v) (S.l + 1) (L v) (j v) (lam v) (S.cutLo v) (S.cutHi v) c S.Ntop hSet hDec hAdj hEig hN
    (hcut v) (w.1 v) hA hlen
  have h1 : Tendsto (fun ε : ℝ => σ v * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => σ v * ε) (𝓝 0) (𝓝 (σ v * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0)
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using mul_pos hσ hε
  have h3 := (Complex.continuous_ofReal.tendsto _).comp ((hT.comp h1).const_mul (Cm v))
  have key : ∀ x : ℝ, (S.sizeAt v (w.1 v) * (Cm v * x) : ℝ) = Cm v * ((MA.sysQ (D.parOf S v) (S.l + 1) (L v) (j v)
      (lam v) (S.cutLo v) (S.cutHi v) (C₂ * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2) c S.Ntop).size (w.1 v) * x) :=
    fun x => by rw [hsz]; ring
  refine Tendsto.congr' (f₁ := fun ε => ((Cm v * MA.cutoffEnergyForm (D.parOf S v) (S.l + 1) (j v) c (σ v * ε) (w.1 v) : ℝ) : ℂ))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hRR ε hε (w.1 v) hadm).symm
  · rw [key]
    exact h3

end Formalism.FourierDecayAlt.P

end lemE

section decayPart

open Finset Formalism.FourierDecayAlt

noncomputable section decayNC

namespace Formalism.FourierDecayAlt.P.JCx1.decay

open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder

theorem sum_mult {Z X : Type} [DecidableEq Z] (P : Finset Z) (F : Z → ℂ) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) :
    ∑ p : P, (∑ h ∈ Y, if g h = (p : Z) then (1 : ℂ) else 0) * F p = ∑ h ∈ Y, F (g h) := by
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_eq_single (⟨g h, hg h hh⟩ : P)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Subtype.ext e.symm)
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem psd_compress {Z X J : Type} [Fintype J] [DecidableEq Z] (P : Finset Z) (H : Z → Z → ℂ)
    (hH : PSDOn P H) (Y : J → Finset X) (g : J → X → Z) (hg : ∀ j, ∀ h ∈ Y j, g j h ∈ P) :
    Matrix.PosSemidef (Matrix.of fun j k : J => ∑ h ∈ Y j, ∑ h' ∈ Y k, H (g j h) (g k h')) := by
  have hH' : Matrix.PosSemidef (Matrix.of fun x y : P => H x y) := hH
  have key : ∀ (j : J) (F : Z → ℂ),
      ∑ p : P, (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0) * F p = ∑ h ∈ Y j, F (g j h) :=
    fun j F => sum_mult P F (Y j) (g j) (hg j)
  have hst : ∀ (j : J) (p : P), star (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0)
      = ∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0 := by
    intro j p
    rw [star_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  have hmat := hH'.conjTranspose_mul_mul_same
    (Matrix.of fun (p : P) (j : J) => ∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0)
  convert hmat using 1
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hst]
  have e1 : ∀ q : P, ∑ p : P, (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0) * H p q
      = ∑ h ∈ Y j, H (g j h) q := fun q => key j (fun z => H z q)
  simp only [e1]
  have e2 : ∑ q : P, (∑ h ∈ Y j, H (g j h) q) * (∑ h' ∈ Y k, if g k h' = (q : Z) then (1 : ℂ) else 0)
      = ∑ h' ∈ Y k, ∑ h ∈ Y j, H (g j h) (g k h') := by
    refine Eq.trans ?_ (key k (fun z => ∑ h ∈ Y j, H (g j h) z))
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [e2, Finset.sum_comm]

theorem psd_pull {Z X : Type} [DecidableEq Z] (P : Finset Z) (H : Z → Z → ℂ) (hH : PSDOn P H)
    (Y : Finset X) (g : X → Z) (hg : ∀ h ∈ Y, g h ∈ P) : PSDOn Y (fun x y => H (g x) (g y)) := by
  have hH' : Matrix.PosSemidef (Matrix.of fun x y : P => H x y) := hH
  exact hH'.submatrix (fun y : Y => (⟨g y, hg y y.2⟩ : P))

theorem psd_two_cs (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re ∧ 0 ≤ (M 0 0).re ∧ 0 ≤ (M 1 1).re := by
  have hH := hM.1
  have h01 : star (M 0 1) = M 1 0 := hH.apply 1 0
  have h00 : star (M 0 0) = M 0 0 := hH.apply 0 0
  have h11 : star (M 1 1) = M 1 1 := hH.apply 1 1
  have hd0 : (M 0 0).im = 0 := Complex.conj_eq_iff_im.1 h00
  have hd1 : (M 1 1).im = 0 := Complex.conj_eq_iff_im.1 h11
  have hdet : 0 ≤ M.det := hM.det_nonneg
  have p0 : 0 ≤ M 0 0 := hM.diag_nonneg
  have p1 : 0 ≤ M 1 1 := hM.diag_nonneg
  rw [Matrix.det_fin_two, ← h01] at hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    have hre := (Complex.le_def.1 hdet).1
    simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re, hd0, hd1, Complex.star_def,
      Complex.conj_re, Complex.conj_im] at hre
    nlinarith [hre]
  · have := (Complex.le_def.1 p0).1
    simpa using this
  · have := (Complex.le_def.1 p1).1
    simpa using this

attribute [local instance] Classical.propDecidable

variable {E W : Type} [Field E] (D : Data E W)

theorem join_mem (Y : Finset (Pt E)) (s : ℕ) (T : Finset E) (t : E) (ht : t ∈ T) :
    ∀ h ∈ Y, join h s t ∈ pts Y s T := by
  intro h hh
  unfold pts
  exact Finset.mem_image.2 ⟨(h, t), Finset.mem_product.2 ⟨hh, ht⟩, rfl⟩

private theorem psdOn_hadamard_mul_of_psdOn {α : Type} (F : Finset α) (A B : α → α → ℂ) (hA : PSDOn F A)
    (hB : PSDOn F B) : PSDOn F (fun x y => A x y * B x y) := by
  have hA' : Matrix.PosSemidef (Matrix.of fun x y : F => A x y) := hA
  have hB' : Matrix.PosSemidef (Matrix.of fun x y : F => B x y) := hB
  show Matrix.PosSemidef (Matrix.of fun x y : F => A x y * B x y)
  first
  | exact hA'.hadamard hB'
  | exact Matrix.PosSemidef.hadamard hA' hB'
  | obtain ⟨C, hC⟩ : ∃ C : Matrix F F ℂ, (Matrix.of fun x y : F => A x y) = C.conjTranspose * C := by
      first
      | exact ⟨hA'.sqrt, by rw [hA'.posSemidef_sqrt.1.eq, hA'.sqrt_mul_self]⟩
      | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hA'
      | exact Matrix.posSemidef_iff_exists_eq_conjTranspose_mul_self.1 hA'
    have hsum : (Matrix.of fun x y : F => A x y * B x y) =
        ∑ k : F, (Matrix.diagonal fun i => C k i).conjTranspose * (Matrix.of fun x y : F => B x y) *
          Matrix.diagonal fun i => C k i := by
      ext i j
      have hij : A i j = ∑ k : F, star (C k i) * C k j := by
        have := congrFun (congrFun hC i) j
        simpa [Matrix.mul_apply] using this
      rw [Matrix.sum_apply]
      simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply,
        Pi.star_apply]
      rw [hij, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero ?_
    intro k _
    exact hB'.conjTranspose_mul_mul_same _

theorem nst_diag_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : W)
    (Y : Finset (Pt E)) (T : Finset E) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn (pts Y s T) κ) (t : E) (ht : t ∈ T) :
    0 ≤ (D.Nst ε i s w Y (blk κ s t t) t t).re := by
  have hwt : 0 < D.wt w := hW w
  have hH : PSDOn (pts Y s T) (fun a b => κ a b * D.gram ε i w a b) :=
    psdOn_hadamard_mul_of_psdOn _ _ _ hκ (hG ε hε i w _)
  have hg : ∀ j : Fin 2, ∀ h ∈ Y, join h s (![t, t] j) ∈ pts Y s T := by
    intro j h hh
    fin_cases j
    · exact join_mem Y s T t ht h hh
    · exact join_mem Y s T t ht h hh
  have hM := psd_two_cs _ (psd_compress (pts Y s T) _ hH (fun _ : Fin 2 => Y)
    (fun j h => join h s (![t, t] j)) hg)
  have key : ∀ b : ℂ, 0 ≤ b.re → 0 ≤ (b / (D.wt w : ℂ)).re := fun b hb => by
    rw [Complex.div_ofReal_re]
    exact div_nonneg hb hwt.le
  exact key _ hM.2.1

theorem nst_gram (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : W)
    (Y : Finset (Pt E)) (T : Finset E) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn (pts Y s T) κ) (t t' : E)
    (ht : t ∈ T) (ht' : t' ∈ T) :
    PairingProductCorollary.PairingGramInequality (D.Nst ε i s w Y (blk κ s t t') t t') (D.Nst ε i s w Y (blk κ s t t) t t).re
      (D.Nst ε i s w Y (blk κ s t' t') t' t').re := by
  have hwt : 0 < D.wt w := hW w
  have hH : PSDOn (pts Y s T) (fun a b => κ a b * D.gram ε i w a b) :=
    psdOn_hadamard_mul_of_psdOn _ _ _ hκ (hG ε hε i w _)
  have hg : ∀ j : Fin 2, ∀ h ∈ Y, join h s (![t, t'] j) ∈ pts Y s T := by
    intro j h hh
    fin_cases j
    · exact join_mem Y s T t ht h hh
    · exact join_mem Y s T t' ht' h hh
  have hM := psd_two_cs _ (psd_compress (pts Y s T) _ hH (fun _ : Fin 2 => Y)
    (fun j h => join h s (![t, t'] j)) hg)
  have key : ∀ a b c : ℂ, ‖a‖ ^ 2 ≤ b.re * c.re →
      PairingProductCorollary.PairingGramInequality (a / (D.wt w : ℂ)) (b / (D.wt w : ℂ)).re (c / (D.wt w : ℂ)).re := by
    intro a b c h
    unfold PairingProductCorollary.PairingGramInequality
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hwt.le, Complex.div_ofReal_re,
      Complex.div_ofReal_re, div_pow, div_mul_div_comm, ← sq]
    gcongr
  exact key _ _ _ hM.1

theorem minFac_eq (x a : ℝ) (K : ℕ) (hx : 0 ≤ x) (ha : 0 < a) : PairingProductCorollary.minFac x a K = min 1 ((x / a) ^ K) := by
  unfold PairingProductCorollary.minFac
  split_ifs with h
  · rw [min_eq_right]
    exact pow_le_one₀ (div_nonneg hx ha.le) ((div_le_one ha).2 h.le)
  · rw [min_eq_left]
    exact one_le_pow₀ ((one_le_div ha).2 (not_lt.1 h))

theorem combine {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ x a : ι → ℝ) (N M : ℝ)
    (A : Finset ι) (hA : ∀ v, v ∈ A ↔ x v < a v)
    (hL : ∀ v, 0 ≤ abelian₂ v) (hLx : ∀ v, abelian₂ v ≤ x v) (ha : ∀ v, 0 < a v) (hM : 0 ≤ M)
    (h : (∏ v ∈ A, a v ^ K) * N ≤ (∏ v ∈ A, abelian₂ v ^ K) * M) :
    N ≤ (∏ v, min 1 ((x v / a v) ^ K)) * M := by
  have hpt : ∀ v, min 1 ((x v / a v) ^ K) = if v ∈ A then (x v / a v) ^ K else 1 := by
    intro v
    have hxv : 0 ≤ x v := (hL v).trans (hLx v)
    split_ifs with hv
    · exact min_eq_right (pow_le_one₀ (div_nonneg hxv (ha v).le) ((div_le_one (ha v)).2 ((hA v).1 hv).le))
    · exact min_eq_left (one_le_pow₀ ((one_le_div (ha v)).2 (not_lt.1 fun h => hv ((hA v).2 h))))
  have hprod : (∏ v, min 1 ((x v / a v) ^ K)) = ∏ v ∈ A, (x v / a v) ^ K := by
    rw [Finset.prod_congr rfl fun v _ => hpt v, Finset.prod_ite_mem, Finset.univ_inter]
  rw [hprod]
  have hPa : 0 < ∏ v ∈ A, a v ^ K := Finset.prod_pos fun v _ => pow_pos (ha v) K
  have hq : (∏ v ∈ A, (x v / a v) ^ K) = (∏ v ∈ A, x v ^ K) / ∏ v ∈ A, a v ^ K := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun v _ => div_pow _ _ _
  have hLx' : (∏ v ∈ A, abelian₂ v ^ K) ≤ ∏ v ∈ A, x v ^ K :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (hL v) K) fun v _ => pow_le_pow_left₀ (hL v) (hLx v) K
  rw [hq, div_mul_eq_mul_div, le_div_iff₀ hPa]
  calc N * ∏ v ∈ A, a v ^ K = (∏ v ∈ A, a v ^ K) * N := mul_comm _ _
    _ ≤ (∏ v ∈ A, abelian₂ v ^ K) * M := h
    _ ≤ (∏ v ∈ A, x v ^ K) * M := mul_le_mul_of_nonneg_right hLx' hM

end Formalism.FourierDecayAlt.P.JCx1.decay

open Formalism.FourierDecayAlt.P.JCx1.decay in
theorem Formalism.FourierDecayAlt.P.plane_exponential_bound_of_places : Formalism.FourierDecayAlt.JC.PlaneExponentialBoundOfPlaces := by
  intro hGP hWP E _ _ _ Wp Wq _ _ _ _ S abelian₂ hPos hGr hWave hThr ε hε i hi1 hir w hw hcnt
  have hG : S.base.GramPSD := hGP E Wp Wq S hPos hGr _ _ _ _
  have hW : S.base.WordsPos := hWP E Wp Wq S hGr _ _ _ _
  obtain ⟨θ, hθ, hb⟩ := hWave ε hε i hi1 hir w hw hcnt
  refine ⟨θ, hθ, ?_⟩
  intro Y hY κ hκ l hl hl0
  have key := hb Y hY κ hκ l hl hl0 (S.bigPlaces i l)
  have hM : 0 ≤ ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ (S.bigPlaces i l) w' * S.base.N0 ε (i - 1) w' Y κ :=
    Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ _).1 w') (BaseGramNonnegativity.baseGram_nonneg _ hG hW hε _ _ Y κ hκ)
  have hav : ∀ v, 0 < S.base.av v l := fun v => by
    show 0 < S.pl v l
    exact (S.pl v).pos_iff.mpr hl0
  exact combine C.Kst (abelian₂ i) (S.base.szD i) (fun v => S.base.av v l) _ _ _ (fun v => by simp [C.HidaSetting.bigPlaces]; rfl) (fun v => (hThr i hi1 hir v).1)
    (fun v => (hThr i hi1 hir v).2) hav hM key

theorem Formalism.FourierDecayAlt.P.corollary_T_of_sum_form : Formalism.FourierDecayAlt.JC.CorollaryTOfSumForm := by
  intro hEst hG hW E _ _ _ Wp Wq _ _ _ _ S C₄ hpos hgrid hsum
  exact hEst _ _ S.base C₄ (hG E Wp Wq S hpos hgrid _ _ _ _) (hW E Wp Wq S hgrid _ _ _ _) hsum

open Formalism.FourierDecayAlt.P.JCx1.decay Formalism.FourierDecayAlt.TB in
theorem Formalism.FourierDecayAlt.P.off_diagonal_lift_bound_of_places : Formalism.FourierDecayAlt.JC.OffDiagonalLiftBoundOfPlaces := by
  intro hP3 hGP hWP E _ _ _ Wp Wq _ _ _ _ S abelian₂ Lam' hPos hGr hBelow hTop hThr
  have hG : S.base.GramPSD := hGP E Wp Wq S hPos hGr _ _ _ _
  have hW : S.base.WordsPos := hWP E Wp Wq S hGr _ _ _ _
  intro ε hε i s hs hsi hir hns w hw hcnt
  have hir' : i ≤ S.G.r + 1 := hir
  have hav : ∀ v (x : E), x ≠ 0 → 0 < S.base.av v x := fun v x hx => by
    show 0 < S.pl v x
    exact (S.pl v).pos_iff.mpr hx
  by_cases hi : i ≤ S.G.r
  · obtain ⟨θ, hθ, hb⟩ := hBelow ε hε i s hs hsi hi w hw hcnt
    refine ⟨fun (π : Fin S.f → Fin 3) => θ (univ.filter fun v => π v ≠ 0), fun π => hθ _, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho
    refine ⟨fun v => if S.base.szL (i - s + 1) s v < S.base.av v (t⁻¹ - t'⁻¹) then 1 else 0, ?_⟩
    have hthr : ∀ v, 0 ≤ abelian₂ (i - s + 1) s v ∧ abelian₂ (i - s + 1) s v ≤ S.base.szL (i - s + 1) s v :=
      fun v => hThr.1 (i - s + 1) s (by omega) hs (by omega) v
    have hM : ∀ A, 0 ≤ ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K),
        θ A x * (((S.base.Nst ε i s x.1 Y (blk κ s t t) t t).re +
          (S.base.Nst ε i s x.2 Y (blk κ s t' t') t' t').re) / 2) := fun A =>
      Finset.sum_nonneg fun x _ => mul_nonneg ((hθ A).1 x) (div_nonneg (add_nonneg
        (nst_diag_nonneg _ hG hW hε i s x.1 Y T κ hκ t ht)
        (nst_diag_nonneg _ hG hW hε i s x.2 Y T κ hκ t' ht')) zero_le_two)
    exact combine S.base.K (abelian₂ (i - s + 1) s) (S.base.szL (i - s + 1) s) (fun v => S.base.av v (t⁻¹ - t'⁻¹))
      _ _ _ (fun v => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with h <;> simp [h])
      (fun v => (hthr v).1) (fun v => (hthr v).2) (fun v => hav v _ ho) (hM _)
      (hb Y T κ hY hκ t ht t' ht' h0 h0' ho _)
  · have hi' : i = S.G.r + 1 := by omega
    subst hi'
    have hs2 : 2 ≤ s := by
      by_contra hc
      exact hns ⟨rfl, by omega⟩
    obtain ⟨θ, hθ, hb⟩ := hTop ε hε s hs2 hsi w hw hcnt
    have hbs : S.G.r + 1 - s + 1 = S.G.r + 2 - s := by omega
    rw [hbs]
    let θ2 : (Fin S.f → Fin 3) → S.W × S.W → ℝ := fun π x =>
      θ (univ.filter fun v => π v = 1) x.1 * θ (univ.filter fun v => π v = 2) x.2
    refine ⟨θ2, fun π => ⟨fun x => mul_nonneg ((hθ _).1 _) ((hθ _).1 _), fun x hx => ?_, ?_⟩, ?_⟩
    · rw [Finset.mem_product, not_and_or] at hx
      rcases hx with hx | hx
      · simp only [θ2, (hθ _).2.1 _ hx, zero_mul]
      · simp only [θ2, (hθ _).2.1 _ hx, mul_zero]
    · simp only [θ2]
      rw [Finset.sum_product, ← Finset.sum_mul_sum, (hθ _).2.2, (hθ _).2.2, one_mul]
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho
    let tv : Fin S.f → ℂ := fun v => S.σ v t
    let tv' : Fin S.f → ℂ := fun v => S.σ v t'
    let L : Fin S.f → ℝ := Lam' (S.G.r + 2 - s) s
    have hthr : ∀ v, 0 ≤ L v ∧ 2 * L v ≤ S.base.szL (S.G.r + 2 - s) s v :=
      fun v => hThr.2 s hs2 hsi v
    have hoA : ∀ v, PairingProductCorollary.oAbs tv tv' v = S.base.av v (t⁻¹ - t'⁻¹) := fun v => by
      simp only [PairingProductCorollary.oAbs, tv, tv', one_div, ← map_inv₀, ← map_sub]
      exact Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
    have htv : ∀ v, ‖tv v‖ = S.base.av v t := fun v => Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
    let π : Fin S.f → Fin 3 := fun v =>
      if 2 * L v < PairingProductCorollary.oAbs tv tv' v then (if ‖tv v‖ ≤ ‖tv' v‖ then 1 else 2) else 0
    refine ⟨π, ?_⟩
    have hY' : ∀ h ∈ Y, TB.level h = S.G.r + 1 - s := hY
    have hκt : PSDOn Y (blk κ s t t) := by
      classical
      exact psd_pull _ κ hκ Y (fun h => join h s t) (join_mem Y s T t ht)
    have hκt' : PSDOn Y (blk κ s t' t') := by
      classical
      exact psd_pull _ κ hκ Y (fun h => join h s t') (join_mem Y s T t' ht')
    set B1 : Finset (Fin S.f) := univ.filter fun v => π v = 1 with hB1
    set B2 : Finset (Fin S.f) := univ.filter fun v => π v = 2 with hB2
    set S1 := ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θ B1 w' *
      (S.base.Nst ε (S.G.r + 1) s w' Y (blk κ s t t) t t).re with hS1
    set S2 := ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θ B2 w' *
      (S.base.Nst ε (S.G.r + 1) s w' Y (blk κ s t' t') t' t').re with hS2
    have hS1n : 0 ≤ S1 := Finset.sum_nonneg fun x _ =>
      mul_nonneg ((hθ _).1 x) (nst_diag_nonneg _ hG hW hε _ s x Y T κ hκ t ht)
    have hS2n : 0 ≤ S2 := Finset.sum_nonneg fun x _ =>
      mul_nonneg ((hθ _).1 x) (nst_diag_nonneg _ hG hW hε _ s x Y T κ hκ t' ht')
    have e1 : univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ‖tv v‖ ≤ ‖tv' v‖) = B1 := by
      ext v
      simp only [hB1, π, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have e2 : univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ¬ ‖tv v‖ ≤ ‖tv' v‖) = B2 := by
      ext v
      simp only [hB2, π, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have hB1b : (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t) t t).re ≤
        (∏ v ∈ univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ‖tv v‖ ≤ ‖tv' v‖),
          (‖tv v‖ * L v) ^ (2 * S.base.K)) * S1 := by
      rw [e1]
      have := hb Y hY' (blk κ s t t) hκt t h0 B1
      simpa only [htv] using this
    have hB2b : (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t' t') t' t').re ≤
        (∏ v ∈ univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ¬ ‖tv v‖ ≤ ‖tv' v‖),
          (‖tv' v‖ * L v) ^ (2 * S.base.K)) * S2 := by
      rw [e2]
      have := hb Y hY' (blk κ s t' t') hκt' t' h0' B2
      have htv' : ∀ v, ‖tv' v‖ = S.base.av v t' := fun v => Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
      simpa only [htv'] using this
    have hmain := hP3 (Fin S.f) S.base.K L tv tv' (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t') t t')
      (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t) t t).re
      (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t' t') t' t').re S1 S2
      (fun v => ⟨(map_ne_zero (S.σ v)).mpr h0, (map_ne_zero (S.σ v)).mpr h0'⟩) (fun v => (hthr v).1)
      (nst_diag_nonneg _ hG hW hε _ s w Y T κ hκ t ht) (nst_diag_nonneg _ hG hW hε _ s w Y T κ hκ t' ht')
      hS1n hS2n (nst_gram _ hG hW hε _ s w Y T κ hκ t t' ht ht') hB1b hB2b
    have hsum : ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θ2 π x *
        (((S.base.Nst ε (S.G.r + 1) s x.1 Y (blk κ s t t) t t).re +
          (S.base.Nst ε (S.G.r + 1) s x.2 Y (blk κ s t' t') t' t').re) / 2) = (S1 + S2) / 2 := by
      rw [Finset.sum_product]
      simp only [θ2, ← hB1, ← hB2]
      have hsplit : ∀ x y : S.W, θ B1 x * θ B2 y *
          (((S.base.Nst ε (S.G.r + 1) s x Y (blk κ s t t) t t).re +
            (S.base.Nst ε (S.G.r + 1) s y Y (blk κ s t' t') t' t').re) / 2) =
          (θ B1 x * (S.base.Nst ε (S.G.r + 1) s x Y (blk κ s t t) t t).re) * θ B2 y / 2 +
            θ B1 x * (θ B2 y * (S.base.Nst ε (S.G.r + 1) s y Y (blk κ s t' t') t' t').re) / 2 := by
        intro x y; ring
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul_sum, hS1, hS2,
        (hθ B1).2.2, (hθ B2).2.2, mul_one, one_mul]
      ring
    rw [hsum]
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
    · unfold PairingProductCorollary.minFac; split_ifs
      · exact pow_nonneg (div_nonneg (by linarith [(hthr v).1]) (norm_nonneg _)) _
      · exact zero_le_one
    · have hpos : 0 < PairingProductCorollary.oAbs tv tv' v := by rw [hoA]; exact hav v _ ho
      rw [minFac_eq _ _ _ (by linarith [(hthr v).1]) hpos, hoA]
      refine min_le_min_left _ (pow_le_pow_left₀ (div_nonneg (by linarith [(hthr v).1]) (hav v _ ho).le) ?_ _)
      exact div_le_div_of_nonneg_right (hthr v).2 (hav v _ ho).le

end decayNC

end decayPart

section needsPart

open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField

namespace Formalism.FourierDecayAlt.P.JCx1.needs

theorem ptSize_loc {E : Type} [Field E] (σ : E →+* ℂ) (p : TB.Pt E) :
    D.ptSize (C.loc σ p) = TB.level p := by
  unfold D.ptSize C.loc TB.level
  simp [List.map_map, Function.comp_def]

end Formalism.FourierDecayAlt.P.JCx1.needs

namespace Formalism.FourierDecayAlt.P

theorem gram_proposition_of_places : Formalism.FourierDecayAlt.JC.PropGramOfPlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S Hv _ _ V H _ _ Vt hT hG Y hY
  have hv : ∀ v, ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ p ∈ Y.image (C.loc (S.σ v)), ∀ q ∈ Y.image (C.loc (S.σ v)),
      (S.pd v).RR ε (S.G.r + 1) [] p q = inner ℂ (V v q) (V v p) := by
    intro v
    apply hG v
    intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]
    exact (hY p' hp').1
  filter_upwards [Filter.eventually_all.mpr hv] with ε hε
  intro p hp q hq
  rw [hT p q (hY p hp) (hY q hq)]
  simp only [C.HidaSetting.gram, le_refl, if_true, C.HidaSetting.gramLoc, C.Word.emp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hε v _ (Finset.mem_image_of_mem _ hp) _ (Finset.mem_image_of_mem _ hq)]
end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.JCx1.needs

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_sgs (Bs : RealPlaceData k r Wp Wq) {p : SS k r} (hp : Bs.inSS p) (g : Mat k r) :
    Gf k r Bs.z Bs.z' (sgs p g) = Gf k r Bs.z Bs.z' g := by
  unfold Formalism.QuantumDeterminants.Gf
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]

theorem choose_congr {α : Sort*} {P Q : α → Prop} (e : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
    hP.choose = hQ.choose := by
  subst e
  rfl

theorem orbJ_smul_of_ae (Bs : RealPlaceData k r Wp Wq) (γ : Mat k r) (μR : Measure (Mt k r))
    (F G : Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hFG : ∀ᵐ p ∂Bs.μSS, D.orbIntegrand Bs γ F p = c • D.orbIntegrand Bs γ G p) :
    D.orbJ Bs γ μR F = c • D.orbJ Bs γ μR G := by
  unfold D.orbJ
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul]
    split_ifs with hF
    · refine (integral_congr_ae ?_).trans (integral_zero _ _)
      exact hFG.mono fun p hp => by simp only [hp, zero_smul, smul_zero]
    all_goals rfl
  · have hiff : ∀ θ : B.SS k r → ℝ, Integrable (fun p => θ p • D.orbIntegrand Bs γ F p) Bs.μSS ↔
        Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := by
      intro θ
      have e : (fun p => θ p • D.orbIntegrand Bs γ F p) =ᵐ[Bs.μSS]
          fun p => c • (θ p • D.orbIntegrand Bs γ G p) :=
        hFG.mono fun p hp => by
          simp only [hp]
          exact smul_comm _ _ _
      rw [integrable_congr e]
      exact integrable_smul_iff hc (fun p => θ p • D.orbIntegrand Bs γ G p)
    split_ifs with hF hG hG
    · rw [choose_congr (by funext θ; exact propext (and_congr_right fun _ => hiff θ)) hF hG,
        ← integral_smul]
      refine integral_congr_ae (hFG.mono fun p hp => ?_)
      simp only [hp]
      exact smul_comm _ _ _
    · exact (hG ⟨hF.choose, hF.choose_spec.1, (hiff _).1 hF.choose_spec.2⟩).elim
    · exact (hF ⟨hG.choose, hG.choose_spec.1, (hiff _).2 hG.choose_spec.2⟩).elim
    · simp

theorem orbJ_cutF (Bs : RealPlaceData k r Wp Wq) (γ : Mat k r) (μR : Measure (Mt k r))
    (χ : ℝ → ℝ) (f : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    D.orbJ Bs γ μR (D.cutF Bs χ f ε) = ((χ (Gf k r Bs.z Bs.z' γ / ε) : ℝ) : ℂ) • D.orbJ Bs γ μR f := by
  have hfin : ∀ (U : Set (Mat k r)) (μ : Measure (Mt k r)), IsHaarOn U μ → SFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := hfin _ _ Bs.haarW
  haveI := hfin _ _ Bs.haarN
  haveI := hfin _ _ Bs.haarW'
  have hW : ∀ᵐ x ∂Bs.μW, Matrix.of x ∈ UWset k r Bs.z := ae_iff.2 Bs.haarW.conc
  have hN : ∀ᵐ x ∂Bs.μN, Matrix.of x ∈ Nset k r := ae_iff.2 Bs.haarN.conc
  have hW' : ∀ᵐ x ∂Bs.μW', Matrix.of x ∈ UWset k r Bs.z' := ae_iff.2 Bs.haarW'.conc
  have a1 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.1.1 ∈ UWset k r Bs.z :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := Bs.μN)).ae hW)
  have a2 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := Bs.μN)).ae hN)
  have a3 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.2.1 ∈ UWset k r Bs.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := Bs.μN)).ae hW')
  have a4 : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod Bs.μN) (ν := Bs.μW'.prod Bs.μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := Bs.μN)).ae hN)
  have hae : ∀ᵐ p ∂Bs.μSS, Bs.inSS p := by
    unfold RealPlaceData.μSS
    filter_upwards [a1, a2, a3, a4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  apply orbJ_smul_of_ae
  filter_upwards [hae] with p hp
  simp only [D.orbIntegrand, B.rho, D.cutF, gf_sgs Bs hp γ]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem vecV_cutF_eventually (hGS : D.PtGSpec) (Bs : RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ)
    (m₀ : Mat k r) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (f : Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), D.vecV Bs ν' m₀ (D.cutF Bs χ f ε) p = D.vecV Bs ν' m₀ f p := by
  unfold D.vecV
  split_ifs with h h'
  · have hG : 0 < Gf k r Bs.z Bs.z' h'.choose := by
      rw [← hGS k r Bs.z Bs.z' p h'.choose h.1 h'.choose_spec.2.1]
      exact h.2
    filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [orbJ_cutF, hχ.2.2 _ ((one_le_div hε.1).2 hε.2.le)]
    simp
  · simp
  · simp

theorem vecV_of_not {Bs : RealPlaceData k r Wp Wq} {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : Mat k r}
    {F : Mat k r → (Wq →L[ℂ] Wp)} {p : C.LPt} (h : ¬ D.IsLocPt p (r + 1)) : D.vecV Bs ν' m₀ F p = 0 := by
  unfold D.vecV
  rw [dif_neg (fun h' => h h'.1)]

theorem hsVec_zero [FiniteDimensional ℂ Wq] : hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [hsVec]

end Formalism.FourierDecayAlt.P.JCx1.needs

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem orbital_integral_cutoff_scalar : Formalism.FourierDecayAlt.JC.OrbJCutScalar := by
  intro k r Wp Wq _ _ _ _ Bs γ μR χ f ε _ _ _
  exact JCx1.needs.orbJ_cutF Bs γ μR χ f ε

theorem gram_at_built_place : Formalism.FourierDecayAlt.JC.GramPlaceBuilt := by
  intro _ hGS _ _ _ E _ _ _ Wp Wq _ _ _ _ _ S T f χ ν' m₀ top A₀ _ _ hB v Y hY
  obtain ⟨hχ, hv⟩ := hB
  have hpd := (hv v).1
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ p ∈ Y,
      D.vecV (T v).base (ν' v) (m₀ v) (D.cutF (T v).base χ (f v) ε) (D.toStd S.G.r (S.g : ℝ) 1 p) =
        D.vecV (T v).base (ν' v) (m₀ v) (f v) (D.toStd S.G.r (S.g : ℝ) 1 p) := by
    rw [Filter.eventually_all_finset]
    intro p _
    exact Formalism.FourierDecayAlt.P.JCx1.needs.vecV_cutF_eventually hGS _ _ _ χ hχ _ _
  filter_upwards [hev] with ε hε
  intro p hp q hq
  rw [hpd]
  simp only [D.componentFamilySetting_ofSetting, D.RRplace, JC.vecPlace]
  by_cases hpq : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 p) (S.G.r + 1) ∧
      D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 q) (S.G.r + 1)
  · simp only [dif_pos hpq, dif_neg (show ¬ (S.G.r + 1 ≤ S.G.r) by omega), ↓reduceIte]
    rw [hε p hp, hε q hq]
    simp only [D.GamLev, Finset.Ioc_self, Finset.prod_empty, one_pow, hsInner, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  · rw [dif_neg hpq]
    rcases not_and_or.mp hpq with h | h
    · rw [Formalism.FourierDecayAlt.P.JCx1.needs.vecV_of_not h]
      simp [Formalism.FourierDecayAlt.P.JCx1.needs.hsVec_zero]
    · rw [Formalism.FourierDecayAlt.P.JCx1.needs.vecV_of_not h]
      simp [Formalism.FourierDecayAlt.P.JCx1.needs.hsVec_zero]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.JCx1.needs

noncomputable section

section meas

open scoped Classical

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem isEmptyReal' : IsEmpty {w : InfinitePlace E // w.IsReal} := by
  exact ⟨fun w => NumberField.InfinitePlace.not_isReal_iff_isComplex.2
    (NumberField.IsTotallyComplex.isComplex w.1) w.2⟩

def cpx (c : J.CV E) : {w : InfinitePlace E // w.IsComplex} → ℂ := (Formalism.FourierDecayAlt.P.Jx2.ee E c).2

theorem cpx_apply (c : J.CV E) (w : {w : InfinitePlace E // w.IsComplex}) : cpx E c w = c w.1 := by
  rfl

theorem cpx_mp : MeasurePreserving (cpx E) volume volume := by
  haveI := isEmptyReal' E
  have h1 : MeasurePreserving (Formalism.FourierDecayAlt.P.Jx2.ee E) volume volume := by
    first
    | exact Formalism.FourierDecayAlt.P.Jx2.ee_mp E
    | exact Formalism.FourierDecayAlt.P.Jx2.ee_mp
  haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ)) := by
    constructor
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    simp
  have h2 : MeasurePreserving (Prod.snd : NumberField.mixedEmbedding.mixedSpace E → _) volume volume :=
    measurePreserving_snd
  exact h2.comp h1

variable {E} {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def eqv (S : C.HidaSetting E Wp Wq) : Fin S.f ≃ {w : InfinitePlace E // w.IsComplex} :=
  S.pl.trans (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w)).symm

def Qm (S : C.HidaSetting E Wp Wq) (c : J.CV E) : Fin S.f → ℂ :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (eqv S).symm (cpx E c)

theorem Qm_apply (S : C.HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : Qm S c v = c (S.pl v) := by
  have h1 : (eqv S).symm (eqv S v) = v := Equiv.symm_apply_apply _ _
  conv_lhs => rw [← h1]
  rw [Qm, MeasurableEquiv.piCongrLeft_apply_apply, cpx_apply]
  rfl

theorem Qm_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (Qm S) volume volume := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin S.f => (volume : Measure ℂ)) (eqv S).symm).comp
    (cpx_mp E)

end meas

theorem integrable_of_decay {φ : ℂ → ℂ} (hc : Continuous φ) {Cφ : ℝ}
    (hb : ∀ c, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) : Integrable φ := by
  have hg : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) := by
    apply integrable_one_add_norm
    rw [Complex.finrank_real_complex]
    norm_num
  refine (hg.const_mul Cφ).mono' hc.aestronglyMeasurable (ae_of_all _ fun c => ?_)
  have h1 : (0 : ℝ) ≤ 1 + ‖c‖ := by positivity
  rw [Real.rpow_neg h1, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact hb c

open scoped ComplexConjugate in
theorem thmPInt_of_covolume_prod (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (dl : ℕ → Fin S.f → ℝ) (hpos : C.ThmPPos S)
    (hcov : ∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) ≠ 0)
    (hprod : ∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1))
    (hpl : ∀ v, JC.ThmPIntPlace S v fun i => dl i v) : C.ThmPInt S := by
  intro ε hε i hi1 hi2 w Y hY κ hκ
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) ∧
      (∃ Cφ : ℝ, ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∫ c : ℂ, φ c = (dl i v : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') := by
    intro v h h'
    exact hpl v ε hε i hi1 hi2 w _ _ (by rw [ptSize_loc]; exact hY h h.2)
      (by rw [ptSize_loc]; exact hY h' h'.2)
  choose φ hφc hφe hφb hφi using H
  choose Cφ hCφ using hφb
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  set Φ : (Fin S.f → ℂ) → ℂ := fun y => (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, φ v h h' (y v)) / sz with hΦ
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ => (hφc v h h').comp (continuous_apply v))
  have hN1 : ∀ c : J.CV E, (∀ v, c (S.pl v) ≠ 0) → S.N1 ε i w.1 Y κ c = Φ (Qm S c) := by
    intro c hc
    simp only [C.HidaSetting.N1, hΦ, Qm_apply]
    congr 1
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h' _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hφe v h h' _ (hc v)]
  have hQc : Continuous (Qm S) := by
    have : Qm S = fun c v => c (S.pl v) := funext fun c => funext fun v => Qm_apply S c v
    rw [this]
    exact continuous_pi fun v => (EuclideanSpace.proj (𝕜 := ℂ) (S.pl v)).continuous
  refine ⟨⟨fun c => Φ (Qm S c), hΦc.comp hQc, fun c hc => (hN1 c hc).symm,
    (∑ h : Y, ∑ h' : Y, ‖κ h h'‖ * ∏ v, Cφ v h h') / ‖sz‖, fun c => ?_⟩, ?_⟩
  ·
    simp only [hΦ, Qm_apply, norm_div]
    rw [div_mul_eq_mul_div]
    gcongr
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
    gcongr with v
    exact hCφ v h h' _
  ·
    have hpsi : ∀ c, S.psiInf 0 c = 1 := by
      intro c
      simp [C.HidaSetting.psiInf]
    simp only [C.HidaSetting.Nhat, hpsi, mul_one]
    have hae : S.N1 ε i w.1 Y κ =ᵐ[volume] fun c => Φ (Qm S c) := by
      have hnull : volume (Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
        rw [(Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
          measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
        exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
      apply hN1 c
      intro v hv
      exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Qm_apply, hv]⟩))
    have hmap : ∫ c, Φ (Qm S c) = ∫ y, Φ y := by
      conv_rhs => rw [← (Qm_mp S).map_eq]
      rw [integral_map (Qm_mp S).measurable.aemeasurable hΦc.aestronglyMeasurable]
    have hint : ∀ (h h' : Y), Integrable (fun y : Fin S.f → ℂ => ∏ v, φ v h h' (y v)) :=
      fun h h' => Integrable.fintype_prod (fun v => integrable_of_decay (hφc v h h') (hCφ v h h'))
    have hΦi : ∫ y, Φ y = (∑ h : Y, ∑ h' : Y, κ h h' *
        ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℂ) *
          S.gram ε (i - 1) w.1 h h')) / sz := by
      simp only [hΦ]
      rw [integral_div, integral_finsetSum _ fun h _ =>
        integrable_finsetSum _ fun h' _ => (hint h h').const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [integral_finsetSum _ fun h' _ => (hint h h').const_mul _]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [integral_const_mul, integral_fintype_prod_volume_eq_prod]
      congr 1
      simp only [hφi, Finset.prod_mul_distrib, C.HidaSetting.gram, if_pos (show i - 1 ≤ S.G.r + 1 by omega)]
      rw [← Complex.ofReal_prod, hprod i hi1 hi2]

    have hκH : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h h') = κ h' h := by
      intro h hh h' hh'
      exact hκ.1.apply (⟨h', hh'⟩ : Y) (⟨h, hh⟩ : Y)
    have hgH : ∀ h h' : TB.Pt E, conj (S.gram ε (i - 1) w.1 h h') = S.gram ε (i - 1) w.1 h' h := by
      intro h h'
      simp only [C.HidaSetting.gram, if_pos (show i - 1 ≤ S.G.r + 1 by omega), map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      have hP := hpos v ε hε (i - 1) (by omega) w {C.loc (S.σ v) h, C.loc (S.σ v) h'}
      exact hP.1.apply (⟨C.loc (S.σ v) h', by simp⟩ : ({C.loc (S.σ v) h, C.loc (S.σ v) h'} : Finset C.LPt))
        (⟨C.loc (S.σ v) h, by simp⟩ : ({C.loc (S.σ v) h, C.loc (S.σ v) h'} : Finset C.LPt))
    set X : ℂ := ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε (i - 1) w.1 h h' with hX
    have hXr : ((X.re : ℝ) : ℂ) = X := by
      rw [← Complex.conj_eq_iff_re, hX, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun h' hh' => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [map_mul, hκH h' hh' h hh, hgH h' h]
    have hN0 : ((S.base.N0 ε (i - 1) w Y κ : ℝ) : ℂ) = X / sz := by
      show (((X.re / C.Word.size S.P w.1 : ℝ)) : ℂ) = X / sz
      rw [Complex.ofReal_div, hXr]
    rw [hN0, integral_congr_ae hae, hmap, hΦi]
    have hcv := hcov i hi1 hi2
    set cv : ℝ := ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) with hcvd
    have hcv' : (cv : ℂ) ≠ 0 := by exact_mod_cast hcv
    have hsum : ∑ h : Y, ∑ h' : Y, κ h h' * ((cv : ℂ) * S.gram ε (i - 1) w.1 h h') = (cv : ℂ) * X := by
      rw [hX, Finset.mul_sum, ← Finset.sum_coe_sort Y]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_coe_sort Y]
      refine Finset.sum_congr rfl fun h' _ => ?_
      ring
    rw [hsum]
    field_simp

end

end Formalism.FourierDecayAlt.P.JCx1.needs

namespace Formalism.FourierDecayAlt.P

theorem theorem_P_integral_of_places : Formalism.FourierDecayAlt.JC.ThmPIntOfPlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S dl hpos hprod hcov hpl
  exact JCx1.needs.thmPInt_of_covolume_prod E Wp Wq S dl hpos hcov hprod hpl

end Formalism.FourierDecayAlt.P

end needsPart
