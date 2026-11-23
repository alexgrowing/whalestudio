import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RdUEqConstMulClsSum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadingEqThP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLatticeStatement

namespace GlobalTheory.AdTh.GenConst

section Renumber

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}

theorem pv_trans (π : Fin g ≃ Fin g) (x : Frame X.Ψ r) (v : Fin r → E) :
    pv X (π.trans idx) x v ∘ π.symm = pv X idx x v := by
  funext j
  simp [pv]

theorem hMat_trans (π : Fin g ≃ Fin g) (x : Frame X.Ψ r) :
    hMat X bas (π.trans idx) x = (hMat X bas idx x).submatrix (Equiv.refl _) π := by
  rw [hMat, hMat, ← Matrix.inv_submatrix_equiv]
  rfl

theorem hx_trans (π : Fin g ≃ Fin g) (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas (π.trans idx) x z w = hx X bas idx x (z ∘ π.symm) (w ∘ π.symm) := by
  have h1 : ∀ z : Fin g → ℂ, hMat X bas (π.trans idx) x *ᵥ z = hMat X bas idx x *ᵥ (z ∘ π.symm) := fun z => by
    rw [hMat_trans, Matrix.submatrix_mulVec_equiv]
    rfl
  have h2 : tauMat X bas (π.trans idx) x = tauMat X bas idx x := by
    rw [tauMat, tauMat, hMat_trans]
    exact Matrix.submatrix_mul_equiv (hMat X bas idx x) (perMat X bas idx Sum.inr x) id π id
  rw [hx, hx, h1, h1, imInv, imInv, h2]

theorem meanOne_trans (π : Fin g ≃ Fin g) {x : Frame X.Ψ r} {L : Lt E r} {ϑ : (Fin g → ℂ) → ℂ}
    (h : MeanOne X bas idx x L ϑ) : MeanOne X bas (π.trans idx) x L fun z => ϑ (z ∘ π.symm) := by
  obtain ⟨A, Fd, hA, hF, hI⟩ := h
  let T : (Fin g → ℂ) ≃ᵐ (Fin g → ℂ) := MeasurableEquiv.piCongrLeft (fun _ => ℂ) π
  have hT : MeasureTheory.MeasurePreserving T := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℂ) π
  have hTa : ∀ z, T z = z ∘ π.symm := fun z => by
    funext j
    simp [T, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  let Ta : (Fin g → ℂ) ≃+ (Fin g → ℂ) := (LinearEquiv.funCongrLeft ℂ ℂ π).toAddEquiv
  refine ⟨A.map Ta.toAddMonoidHom, T ⁻¹' Fd, fun z => ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (hA u).1 hu
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, (hA _).2 ⟨v, hv, rfl⟩, rfl⟩
  · refine hF.preimage_of_equiv hT.quasiMeasurePreserving (e := Ta.addSubgroupMap A)
      (Ta.addSubgroupMap A).bijective fun a z => ?_
    rw [hTa, hTa]
    funext j
    show (a : Fin g → ℂ) (π (π.symm j)) + z (π.symm j) = (a : Fin g → ℂ) j + z (π.symm j)
    rw [π.apply_symm_apply]
  · rw [hT.measure_preimage_equiv, ← hI, ← hT.setIntegral_preimage_emb T.measurableEmbedding _ Fd]
    simp only [hTa, hx_trans]

variable {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ}

theorem exists_anFib_trans (π : Fin g ≃ Fin g) (A : AnFib X bas idx e x L y) :
    ∃ A' : AnFib X bas (π.trans idx) (π.trans e) x L y, (∀ mk, A.Marked mk → A'.Marked mk) ∧
      ∀ ϑ, A.Reads 1 y.s ϑ → A'.Reads 1 y.s fun z => ϑ (z ∘ π.symm) := by
  let T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := (LinearEquiv.funCongrLeft ℂ ℂ π.symm).toContinuousLinearEquiv
  have hT : ∀ z, T z = z ∘ π.symm := fun _ => rfl
  have hp : ∀ v, T (pv X (π.trans idx) x v) = pv X idx x v := pv_trans π x
  refine ⟨{ ex := fun z => A.ex (T z)
            ex_add := fun z w => by rw [map_add, A.ex_add]
            ex_onto := A.ex_onto.comp T.surjective
            ex_ker := fun z => by
              rw [A.ex_ker]
              exact exists_congr fun v => and_congr_right fun _ => by rw [← hp, T.injective.eq_iff]
            ex_lin := fun a z => by
              rw [← A.ex_lin]
              congr 1
              funext j
              simp [hT]
            hol := fun U f => ⟨(A.hol U f).1.preimage T.continuous,
              (A.hol U f).2.comp T.differentiableOn fun _ h => h⟩
            der := fun ℓ => ⟨by simp only [map_zero]; exact (A.der ℓ).1, fun U h f => ?_⟩
            fr := fun j z => A.fr j (T z)
            fr_hol := fun j => (A.fr_hol j).comp T.differentiableOn fun _ h => h
            fr_ne := fun j z => A.fr_ne j _
            fr_g := fun j j' z => A.fr_g j j' _
            fr_0 := fun j => by rw [map_zero]; exact A.fr_0 j
            χ := A.χ
            χ_norm := A.χ_norm
            fr_per := fun v hv j z hz => by
              rw [hx_trans, hx_trans, pv_trans, map_add, hp]
              exact A.fr_per v hv j _ hz }, fun mk hmk a ha => ?_, fun ϑ h j z => h j (T z)⟩
  · rw [(A.der ℓ).2 U h f]
    have := T.comp_right_fderiv (f := fun z => valAt' (A.ex z).left U f) (x := 0)
    refine Eq.trans ?_ (DFunLike.congr_fun this _).symm
    rw [map_zero, ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    simp [hT, Pi.single_apply, Equiv.symm_apply_eq]
  · exact (hmk a ha).trans (congrArg A.ex (hp _).symm)

end Renumber

section Main

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem idx_unique {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx idx' : Fin g ≃ X.Ψ × Fin r}
    (hs : IsSympl X bas) (h : ∀ x v j, pv X idx x v j = pv X idx' x v j) : idx = idx' := by
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected E r X).nonempty
  have hsp := ((hx_laws E r X g bas idx 0 hs Even.zero x hx).2.2.2.2.2.2.1 _ X.Λ_span).1
  refine Equiv.ext fun j => ?_
  have key : ∀ z : Fin g → ℂ, z j = z (idx.symm (idx' j)) := fun z => by
    have hz : z ∈ Submodule.span ℝ (pv X idx x '' (X.Λ : Set (Fin r → E))) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, rfl⟩ := hz
      rw [h]
      simp [pv]
    | zero => rfl
    | add a b _ _ ha hb => rw [Pi.add_apply, Pi.add_apply, ← ha, ← hb]
    | smul t a _ ha => rw [Pi.smul_apply, Pi.smul_apply, ← ha]
  by_contra hne
  have := key (Pi.single j 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne fun h => hne (idx.symm_apply_eq.1 h).symm] at this
  exact one_ne_zero this

theorem polyDeriv_one {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (u : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv (1 : MvPolynomial σ ℂ) u F x = F x := by
  have key : ∀ (k : ℕ), k = 0 → ∀ v : Fin k → W, iteratedFDeriv ℂ k F x v = F x := by
    rintro k rfl v; exact iteratedFDeriv_zero_apply v
  unfold I2.polyDeriv
  rw [MvPolynomial.support_one, Finset.sum_singleton, key _ (by simp)]
  simp

variable {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem one_mem_harmA (c : Coeff l) (n : ℕ) : (1 : MvPolynomial (LtN Dw n) c.F) ∈ harmA c 0 n := by
  refine ⟨⟨?_, fun _ _ _ _ _ => map_one _, fun m hm σ i => ?_⟩, fun m => ?_⟩
  · simp [harmK, lap]
  · have : m = 0 := by
      by_contra h0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm h0)] at hm
      exact hm rfl
    subst this
    simp
  · rw [MvPolynomial.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem ne_zero_of_meanOne {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {x : Frame X.Ψ r} {L : Lt E r} {ϑ : (Fin g → ℂ) → ℂ} (h : MeanOne X bas idx x L ϑ) : ϑ ≠ 0 := by
  rintro rfl
  obtain ⟨A, Fd, -, -, hI⟩ := h
  simp at hI

theorem exists_root_ne_zero {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hs : IsSympl X bas) {w : E} {L : Lt E r} (hL : SelfD X L) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l L mk) {n N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) {ϑ : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L ϑ) (h0 : ϑ ≠ 0) : ∃ q, ∀ b, ϑ (pv X idx x (Y q b)) ≠ 0 := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨-, -, h1, h2, -⟩ := DualMark.dual_marking E H Dw l r X L mk _ hL hmk (Complex.isPrimitiveRoot_exp l.M hM.ne')
  obtain ⟨u, hu, hne⟩ := GlobalTheory.T.exists_levelOne_theta_ne_zero_on_ideal_half_lattice E r X g bas idx hs w L hL x hx (Mfr l) l.M (le_trans (by norm_num) l.three_le)
    (by rw [h1, h2]) ϑ h h0
  obtain ⟨a, ha, t, ht, rfl⟩ := hmk.surj u hu
  refine ⟨fun _ => Submodule.Quotient.mk a, fun b hb => hne ?_⟩
  obtain ⟨⟨a', ha', hq, hy⟩, -⟩ := hY (fun _ => Submodule.Quotient.mk a) b
  obtain ⟨s, hs', s', hs'', hss⟩ := LevelFibre.level_split l
  obtain ⟨b₁, -, hb₁⟩ := MarkLift.modN_of_mem_half l hs' (Submodule.sub_mem _ ha' ha)
  obtain ⟨b₂, hb₂⟩ := MarkLift.modN_of_mem_bar l hs'' ((Submodule.Quotient.eq _).1 hq)
  have e₀ : mk a' = mk a + l.M • mk (b₁ + b₂) := by
    rw [← map_nsmul, smul_add, ← hb₁, ← hb₂, ← add_smul, hss, one_smul, ← map_add, add_sub_cancel]
  set y := Y (fun _ => Submodule.Quotient.mk a) b
  have hv : y - (l.M : E)⁻¹ • mk a' + mk (b₁ + b₂) - t ∈ L := L.sub_mem (L.add_mem hy (hmk.mem _)) ht
  have e₁ : (l.M : E)⁻¹ • (mk a + l.M • t) + (y - (l.M : E)⁻¹ • mk a' + mk (b₁ + b₂) - t) = y := by
    rw [e₀, smul_add, smul_add, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0,
      inv_smul_smul₀ hM0]
    abel
  have e₂ := congrFun (h.2 _ hv) (pv X idx x ((l.M : E)⁻¹ • (mk a + l.M • t)))
  have hadd : ∀ u v, pv X idx x u + pv X idx x v = pv X idx x (u + v) := fun u v => by
    rw [pv, pv, pv, per_add]; rfl
  rw [← e₂, Pi.smul_apply, fock, hadd, e₁, hb, mul_zero, smul_zero]

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem exists_const_fib (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (k : U.Comp) (n : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
    (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hn : Even n) (hs : IsSympl (U.X k) bas)
    (hI : IdxIs c σ (U.X k) idx e) (v : TF n g) (hv : IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    SelfD (U.X k) (U.X k).Λ ∧ ∃ C : ℂ, C ≠ 0 ∧ ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 →
      ∃ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC U k x)) (ϑ : (Fin g → ℂ) → ℂ), A.Reads 1 (unC U k x).s ϑ ∧
        IsTheta1 (U.X k) bas idx (H.w0 : E) x.1 (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ ∧
        ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W⟩ := nonempty_uw hU
  obtain rfl : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  refine ⟨hL, ?_⟩
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, hDe, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  subst hDe
  obtain rfl : idx = Dc.idx := idx_unique hs fun x u j => (hI.1 x u j).trans (Dc.per_eq x u j).symm
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv
  have hpt : ∀ x (hx : x ∈ (U.X k).dom), IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib (U.X k) bas Dc.idx Dc.e x (U.X k).Λ (unC U k ⟨x, hx⟩)) (ϑ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC U k ⟨x, hx⟩).s ϑ ∧
        IsTheta1 (U.X k) bas Dc.idx (H.w0 : E) x (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas Dc.idx x (U.X k).Λ ϑ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ (z b) = κ * thA (U.X k) bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨π, hπ⟩ : ∃ π : Fin W.g ≃ Fin W.g, π.trans W.e = Dc.e := ⟨Dc.e.trans W.e.symm, by ext1; simp⟩
    have hπ' : ∀ j, W.e j = Dc.e (π.symm j) := fun j => by rw [← hπ]; simp
    have hid : π.trans (π.symm.trans Dc.idx) = Dc.idx := by ext1; simp
    obtain ⟨A₀, hA₀, ϑ₀, hϑ₀, hm₀⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k bas (π.symm.trans Dc.idx) hs
      (fun x u j => by rw [hπ']; exact Dc.per_eq x u _) (fun j => by rw [hπ']; exact Dc.ty_eq _) ⟨x, hx⟩ hux
    have h1 := exists_anFib_trans π A₀
    have hmean := meanOne_trans π hm₀
    rw [hid, hπ] at h1
    rw [hid] at hmean
    obtain ⟨A, hA, hR⟩ := h1
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x _ _ A hs hx hL _ (hR _ hϑ₀)
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x hx _ hT
    exact ⟨κ, hnorm x hx hux _ κ hT hmean hκ, A, _, hA _ hA₀, hR _ hϑ₀, hT, hmean, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, hCn, hCe⟩ := Const.exists_const (U.X k) (Formalism.L2.PjFree.laU U 0 n k) ρ hρ κ hκ
  refine ⟨C, norm_pos_iff.1 (hCn ▸ hρ), fun x hux => ?_⟩
  obtain ⟨A, ϑ, -, hϑ, hT, hmean, hprod⟩ := hpt x.1 x.2 hux
  refine ⟨A, ϑ, hϑ, hT, hmean, ?_⟩
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨q, hq⟩ := exists_root_ne_zero hs hL x.2 hmk hY hT (ne_zero_of_meanOne hmean)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  have hsec : f ∈ sec Xo c 0 n := GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩
  have hsb : IsSB (heisG (U.X k) bas (Y q) v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g bas Dc.idx n hs hn).2.2.2 (Y q) v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn Dc.k Dc.k'
    _ hsb _ (Dc.mem 1 hP.1)
  have hS := hU.2.2.2.2.1 0 n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = Formalism.L2.PjFree.laU U 0 n k := Dc.wt_eq
  rw [hwt] at hhol
  have hval : ∀ x' hx' hu', Formalism.L2.PjFree.rdU U f k x' = κ x' hx' hu' * thP (U.X k) Dc.hr bas Dc.idx
      (heisG (U.X k) bas (Y q) v) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ 1)) x' := fun x' hx' hu' => by
    obtain ⟨A', ϑ', hA', hϑ', -, -, hprod'⟩ := hpt x' hx' hu'
    have := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) bas Dc.idx Dc.e x' _ _ A' hs hx' hL Dw.p n Dc.hr
      Dc.eL hU.1 hn Dc.dir_eq nab hnab ϑ' v _ hϑ' hv hprod' (W.mark k) hmk hA' (fun b => levRep (q b)) (Y q)
      (fun b => by
        obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
        exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
          (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
      (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k ⟨x', hx'⟩))
    exact Eq.trans (dif_pos hx') this
  have h1 := hCe _ _ hS.1 hhol.1 (fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩) hval x.1 x.2
  have h2 := (fock_laws E r _ _ bas Dc.idx n hs hn x.1 x.2 1 ϑ).2.2.2.2 (fun _ => ϑ) _ v hv.1 hprod (Y q) 0
  have h3 : thA (U.X k) bas Dc.idx (heisG (U.X k) bas (Y q) v) x.1 0 ≠ 0 := by
    refine right_ne_zero_of_mul (h2 ▸ Finset.prod_ne_zero_iff.2 fun b _ => ?_)
    rw [fock, Pi.zero_apply, zero_add, zero_add]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hq b)
  rw [hval x.1 x.2 hux, map_one, map_one, thP, polyDeriv_one] at h1
  rw [← mul_right_cancel₀ h3 h1]
  exact hprod

end Main

end GlobalTheory.AdTh.GenConst

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdTh.prod_gen_eq_const_mul_thA : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (n g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), Even n → IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, C ≠ 0 ∧ ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → (∃ ϑ, GenReads U k bas idx e x ϑ) ∧ ∀ ϑ, GenReads U k bas idx e x ϑ → IsTheta1 (U.X k) bas idx (H.w0 : E) x.1 (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ ∧ ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  intro hC E _ _ _ H Dw l Xo c σ r U hσ hU hr1 _ k n g bas idx e hn hs hI v hv
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨hL, C, hC0, h⟩ := GenConst.exists_const_fib hC (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr1 k n bas idx e hn hs hI v hv
  refine ⟨C, hC0, fun x hux => ?_⟩
  obtain ⟨A, ϑ, hϑ, h1⟩ := h x hux
  refine ⟨⟨ϑ, A, hϑ⟩, ?_⟩
  rintro ϑ' ⟨A', hϑ'⟩
  have h2 := ((GlobalTheory.T.analyticFibreDescription_unique E H Dw l Xo c r g _ bas idx e x.1 _ _ A A' hs x.2 hL).2 ϑ').2 hϑ'
  obtain rfl : ϑ = ϑ' :=
    (reads_existsUnique_theta E H Dw l Xo c r g _ bas idx e x.1 _ _ A hs x.2 hL 1 _).1.unique hϑ h2
  exact h1
